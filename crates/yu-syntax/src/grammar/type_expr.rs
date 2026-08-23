//! Standalone fixed-precedence grammar for Yulang type expressions.
//!
//! The module deliberately owns no declaration or pattern use-site.  Future
//! grammar owners call its canonical entry after establishing their own stops.

mod polymorphic_variant;

use std::{marker::PhantomData, ops::Range, sync::Arc};

use chasa::{Back as _, ErrorSink, Input as _, error::std::{Unexpected, UnexpectedEndOfInput}, prelude::from_fn};

use crate::{
    grammar::{declaration::Recovered, expression::parse_integer_literal},
    scan::{
        punctuation::{PunctuationKind, scan_punctuation},
        trivia::{TriviaRun, scan_comment, scan_trivia},
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
    if matches!(&primary, TypePrimary::Forall(_))
        || matches!(&primary, TypePrimary::PolymorphicVariant(PolymorphicVariantType {
            close: Recovered::Incomplete,
            ..
        }))
    {
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
    mut i: SynIn<'_, 'source, '_, E>,
) -> Recovered<TypeExpression<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    i.run(from_fn(|i| parse_type_expression_with_outer_missing_role(outer_missing_role, i)))
        .or_else(|| {
            recover_type_item_for_ast(&mut i)
                .then(|| parse_type_expression_with_outer_missing_role(outer_missing_role, i))
                .flatten()
        })
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
    if primary != DirectTypePrimary::Ordinary {
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
                } else if let Some(range) = committed.probe(|probe| scan_type_path_invalid_run(probe.input())) {
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
                    match direct_type_item_error_retry(committed, TypeRole::ArrowRhs) {
                        Some(TypeItemRecovery::Retry) => {
                            if commit_direct_type_expression(committed).is_none() {
                                emit_type_missing(committed, GrammarRole::Type(TypeRole::ArrowRhs), ExpectedSyntax::TypeExpression);
                            }
                        }
                        Some(TypeItemRecovery::Boundary) => {}
                        None => {
                            emit_type_missing(committed, GrammarRole::Type(TypeRole::ArrowRhs), ExpectedSyntax::TypeExpression);
                        }
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
    let emit_missing = match direct_type_item_error_retry(committed, TypeRole::Primary) {
        Some(TypeItemRecovery::Retry) => {
            return commit_direct_type_expression(committed)
                .expect("the primary recovery retry stopped at a valid primary");
        }
        Some(TypeItemRecovery::Boundary) => false,
        None => true,
    };
    let at = committed.probe(|probe| probe.input().pos());
    committed.start_node(SyntaxKind::TypeExpression);
    if emit_missing {
        emit_type_missing(
            committed,
            outer_missing_role.unwrap_or(GrammarRole::Type(TypeRole::Primary)),
            ExpectedSyntax::TypeExpression,
        );
    }
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
    TerminalIncompletePolymorphicVariant,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TypePrimaryContext {
    Leading,
    Applied,
}

impl TypePrimaryContext {
    fn from_allow_forall(allow_forall: bool) -> Self {
        if allow_forall { Self::Leading } else { Self::Applied }
    }

    fn allows_forall(self) -> bool {
        self == Self::Leading
    }
}

enum TypePrimaryHead<'source> {
    Forall(Range<usize>),
    EffectRow { apostrophe: Range<usize>, open: Range<usize> },
    PolymorphicVariant { colon: Range<usize>, open: Range<usize> },
    Name(TypeName<'source>),
    Number(TypeNumberAtom<'source>),
    Parenthesized(Range<usize>),
    Record(Range<usize>),
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

/// The sequence judge uses this after a malformed-item scanner has stopped.
/// It probes the gap without assigning that gap to either the Error node or a
/// future item; the owning sequence commits it only after choosing a state
/// transition.
#[derive(Clone, Debug, Eq, PartialEq)]
enum DelimitedRecoveryTarget {
    RetryPrimary,
    ExplicitSeparator(TypeExplicitSeparator),
    ImplicitNewline,
    MatchingClose(Range<usize>),
    LocalMismatchedClose(Range<usize>),
    OuterBoundary,
}

#[derive(Clone, Copy)]
struct DelimitedRecoverySpec {
    delimiter: Delimiter,
}

/// The close slot is shared by AST and direct-CST sequences.  Effect rows
/// intentionally retain their older contract: after consuming a local
/// mismatch, a later safe point does not receive a second Missing close.
#[derive(Clone, Copy)]
struct CloseRecoverySpec {
    delimiter: Delimiter,
    owner: ConstructRole,
    matching_kind: SyntaxKind,
    missing_after_mismatch: MissingAfterMismatch,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum MissingAfterMismatch {
    Emit,
    Suppress,
}

trait TypeCloseSlotContext<'source> {
    type Error: ErrorSink<usize>;

    fn with_input<R>(
        &mut self,
        f: impl FnOnce(&mut SynIn<'_, 'source, '_, Self::Error>) -> R,
    ) -> R;
    fn emit_close_trivia(&mut self, trivia: &TriviaRun);
    fn emit_matching_close(&mut self, kind: SyntaxKind, range: Range<usize>);
    fn emit_mismatched_close(&mut self, role: GrammarRole, range: Range<usize>, expected: ExpectedSyntax);
    fn emit_missing_close(&mut self, role: GrammarRole, expected: ExpectedSyntax);
}

/// Drive the close slot after an item sequence has yielded ownership.  The
/// caller supplies only output realization; matching-close, local mismatch,
/// and safe-point ordering remain identical across AST and direct CST.
fn drive_type_close_slot<'source, C>(
    context: &mut C,
    spec: CloseRecoverySpec,
) -> Recovered<Range<usize>>
where
    C: TypeCloseSlotContext<'source>,
    Unexpected<char>: Into<<C::Error as ErrorSink<usize>>::Error>,
    UnexpectedEndOfInput: Into<<C::Error as ErrorSink<usize>>::Error>,
{
    let role = GrammarRole::ClosingDelimiter {
        owner: spec.owner,
        delimiter: spec.delimiter,
    };
    let expected = ExpectedSyntax::Punctuation(PunctuationEvidence::Close(spec.delimiter));
    let mut saw_mismatch = false;
    loop {
        if let Some(trivia) = context.with_input(|i| consume_trivia_before_local_close(spec.delimiter, i)) {
            context.emit_close_trivia(&trivia);
        }
        if let Some(close) = context.with_input(|i| scan_close_for_delimiter(spec.delimiter, i)) {
            context.emit_matching_close(spec.matching_kind, close.clone());
            return Recovered::Complete(close);
        }
        if let Some(mismatched) = context.with_input(|i| scan_mismatched_close_for(spec.delimiter, i)) {
            context.emit_mismatched_close(role, mismatched, expected);
            saw_mismatch = true;
            continue;
        }
        if !saw_mismatch || spec.missing_after_mismatch == MissingAfterMismatch::Emit {
            context.emit_missing_close(role, expected);
        }
        return Recovered::Incomplete;
    }
}

/// Commit a gap only when it belongs to the local close slot.  In particular,
/// trailing trivia before an outer stop remains available to that outer owner.
fn consume_trivia_before_local_close<E>(
    delimiter: Delimiter,
    i: &mut SynIn<E>,
) -> Option<TriviaRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = consume_trivia(i);
    // An active newline stop belongs to the caller even if a local close
    // appears after it; the complete gap must remain unconsumed.
    if trivia_has_newline(&trivia) && active_stop_set(i).contains(StopKind::Newline) {
        i.rollback(checkpoint);
        return None;
    }
    let after_trivia = i.checkpoint();
    let local_close_pending = scan_close_for_delimiter(delimiter, i).is_some()
        || scan_mismatched_close_for(delimiter, i).is_some();
    i.rollback(after_trivia);
    if local_close_pending {
        Some(trivia)
    } else {
        i.rollback(checkpoint);
        None
    }
}

impl<'parse, 'source, 'local, E> TypeCloseSlotContext<'source>
    for SynIn<'parse, 'source, 'local, E>
where
    E: ErrorSink<usize>,
{
    type Error = E;

    fn with_input<R>(
        &mut self,
        f: impl FnOnce(&mut SynIn<'_, 'source, '_, Self::Error>) -> R,
    ) -> R {
        f(self)
    }

    fn emit_close_trivia(&mut self, _trivia: &TriviaRun) {}
    fn emit_matching_close(&mut self, _kind: SyntaxKind, _range: Range<usize>) {}
    fn emit_mismatched_close(&mut self, _role: GrammarRole, _range: Range<usize>, _expected: ExpectedSyntax) {}
    fn emit_missing_close(&mut self, _role: GrammarRole, _expected: ExpectedSyntax) {}
}

struct DirectTypeCloseContext<'context, 'parse, 'source, 'local, E: ErrorSink<usize>, O: CommitOutput<'source>> {
    committed: &'context mut Committed<'parse, 'source, 'local, E, O>,
}

impl<'source, E, O> TypeCloseSlotContext<'source>
    for DirectTypeCloseContext<'_, '_, 'source, '_, E, O>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    type Error = E;

    fn with_input<R>(
        &mut self,
        f: impl FnOnce(&mut SynIn<'_, 'source, '_, Self::Error>) -> R,
    ) -> R {
        self.committed.probe(|probe| f(probe.input()))
    }

    fn emit_close_trivia(&mut self, trivia: &TriviaRun) {
        self.committed.emit_trivia(trivia);
    }

    fn emit_matching_close(&mut self, kind: SyntaxKind, range: Range<usize>) {
        self.committed.token(kind, range);
    }

    fn emit_mismatched_close(&mut self, role: GrammarRole, range: Range<usize>, expected: ExpectedSyntax) {
        emit_error_with_role(self.committed, role, range, expected);
    }

    fn emit_missing_close(&mut self, role: GrammarRole, expected: ExpectedSyntax) {
        emit_type_missing(self.committed, role, expected);
    }
}

/// Probe the post-scanner state without consuming trivia.  A caller that
/// accepts the transition subsequently consumes the same gap through its own
/// output adapter, keeping trivia ownership out of scanner recovery ranges.
fn classify_type_delimited_recovery<E>(
    spec: DelimitedRecoverySpec,
    layout: LayoutDelimitedFrame,
    retry_primary: impl FnOnce(&mut SynIn<E>) -> bool,
    i: &mut SynIn<E>,
) -> DelimitedRecoveryTarget
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = consume_trivia(i);
    let stays_in_chain = type_chain_trivia(i, &trivia);
    let target = if let Some(close) = scan_close_for_delimiter(spec.delimiter, i) {
        DelimitedRecoveryTarget::MatchingClose(close)
    } else if let Some(mismatched) = scan_mismatched_close_for(spec.delimiter, i) {
        DelimitedRecoveryTarget::LocalMismatchedClose(mismatched)
    } else if let Some(separator) = scan_separator(i) {
        DelimitedRecoveryTarget::ExplicitSeparator(separator)
    } else if layout.boundary_after_trivia(&trivia, i.local.line().line_indent)
        == LayoutDelimitedBoundary::ImplicitNewline
    {
        DelimitedRecoveryTarget::ImplicitNewline
    } else if stays_in_chain && retry_primary(i) {
        DelimitedRecoveryTarget::RetryPrimary
    } else {
        DelimitedRecoveryTarget::OuterBoundary
    };
    i.rollback(checkpoint);
    target
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
    let context = TypePrimaryContext::from_allow_forall(allow_forall);
    match committed.probe(|probe| recognize_type_primary_head(context, probe.input()))? {
        TypePrimaryHead::Forall(keyword) => {
            commit_direct_forall_type(keyword, committed);
            Some(DirectTypePrimary::TerminalForall)
        }
        TypePrimaryHead::EffectRow { apostrophe, open } => {
            commit_direct_type_delimited(
                TypeDelimitedOwner::EffectRow,
                TypeDelimitedShape::Bracket,
                SyntaxKind::EffectRowType,
                Some((SyntaxKind::Apostrophe, apostrophe)),
                open,
                committed,
            );
            Some(DirectTypePrimary::Ordinary)
        }
        TypePrimaryHead::PolymorphicVariant { colon, open } => {
            let closed = polymorphic_variant::commit_direct(colon, open, committed);
            Some(if closed {
                DirectTypePrimary::Ordinary
            } else {
                DirectTypePrimary::TerminalIncompletePolymorphicVariant
            })
        }
        TypePrimaryHead::Name(name) => {
            committed.token(type_name_kind(name), type_name_range(name));
            Some(DirectTypePrimary::Ordinary)
        }
        TypePrimaryHead::Number(number) => {
            committed.token(SyntaxKind::Integer, number.range);
            Some(DirectTypePrimary::Ordinary)
        }
        TypePrimaryHead::Parenthesized(open) => {
            commit_direct_type_delimited(
                TypeDelimitedOwner::ParenthesizedGroup,
                TypeDelimitedShape::Parenthesis,
                SyntaxKind::ParenthesizedTypeGroup,
                None,
                open,
                committed,
            );
            Some(DirectTypePrimary::Ordinary)
        }
        TypePrimaryHead::Record(open) => {
            commit_direct_named_record_type(open, committed);
            Some(DirectTypePrimary::Ordinary)
        }
    }
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
            let mut recovery = None;
            if let Some(trivia) = trivia.as_ref() {
                // A first-binder boundary is owned by its recovery item too.
                committed.start_node(SyntaxKind::ForallTypeBinder);
                committed.emit_trivia(trivia);
                match direct_forall_invalid_run(ForallRecoveryPhase::FirstBinder, committed) {
                    Some((range, found_recovery)) => {
                        emit_type_error(committed, TypeRole::ForallBinder, range, ExpectedSyntax::ForallTypeBinder);
                        recovery = Some(found_recovery);
                    }
                    None => {
                        emit_type_missing(committed, GrammarRole::Type(TypeRole::ForallBinder), ExpectedSyntax::ForallTypeBinder);
                    }
                }
                committed.finish_node();
            } else if direct_forall_colon_pending(committed) {
                committed.start_node(SyntaxKind::ForallTypeBinder);
                emit_type_missing(committed, GrammarRole::Type(TypeRole::ForallBinder), ExpectedSyntax::ForallTypeBinder);
                committed.finish_node();
            } else if let Some((range, found_recovery)) = direct_forall_invalid_run(ForallRecoveryPhase::FirstBinder, committed) {
                committed.start_node(SyntaxKind::ForallTypeBinder);
                emit_type_error(committed, TypeRole::ForallBinder, range, ExpectedSyntax::ForallTypeBinder);
                committed.finish_node();
                recovery = Some(found_recovery);
            } else {
                committed.start_node(SyntaxKind::ForallTypeBinder);
                emit_type_missing(committed, GrammarRole::Type(TypeRole::ForallBinder), ExpectedSyntax::ForallTypeBinder);
                committed.finish_node();
                break;
            }

            if recovery == Some(ForallInvalidRecovery::Colon) {
                commit_direct_forall_recovered_colon_and_body(committed);
            } else if direct_forall_colon_pending(committed) {
                commit_direct_forall_colon_and_body(committed);
            } else if recovery == Some(ForallInvalidRecovery::Binder) {
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
        if let Some((range, recovery)) = direct_forall_invalid_run(ForallRecoveryPhase::AfterBinder, committed) {
            let role = if recovery == ForallInvalidRecovery::Binder { TypeRole::ForallBinder } else { TypeRole::ForallColon };
            emit_type_error(committed, role, range, ExpectedSyntax::Punctuation(PunctuationEvidence::Colon));
            match recovery {
                ForallInvalidRecovery::Binder => continue,
                ForallInvalidRecovery::Colon => {
                    commit_direct_forall_recovered_colon_and_body(committed);
                    break;
                }
                ForallInvalidRecovery::Body => {
                    commit_direct_forall_body(committed);
                    break;
                }
                ForallInvalidRecovery::Boundary => break,
            }
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

fn commit_direct_forall_recovered_colon_and_body<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let trivia = consume_direct_forall_trivia(committed, false)
        .expect("forall recovery stopped before type-chain trivia and a colon");
    committed.emit_trivia(&trivia);
    commit_direct_forall_colon_and_body(committed);
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
        match direct_forall_invalid_run(ForallRecoveryPhase::Body, committed) {
            Some((range, ForallInvalidRecovery::Body)) => {
                emit_type_error(committed, TypeRole::ForallBody, range, ExpectedSyntax::TypeExpression);
                if commit_direct_type_expression(committed).is_none() {
                    emit_type_missing(committed, GrammarRole::Type(TypeRole::ForallBody), ExpectedSyntax::TypeExpression);
                }
            }
            Some((range, ForallInvalidRecovery::Boundary)) => {
                emit_type_error(committed, TypeRole::ForallBody, range, ExpectedSyntax::TypeExpression);
            }
            Some((range, ForallInvalidRecovery::Binder | ForallInvalidRecovery::Colon)) => {
                emit_type_error(committed, TypeRole::ForallBody, range, ExpectedSyntax::TypeExpression);
            }
            None => {
                emit_type_missing(committed, GrammarRole::Type(TypeRole::ForallBody), ExpectedSyntax::TypeExpression);
            }
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

fn direct_forall_invalid_run<'parse, 'source, 'local, E, O>(
    phase: ForallRecoveryPhase,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<(Range<usize>, ForallInvalidRecovery)>
where
    E: ErrorSink<usize>, O: CommitOutput<'source>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| scan_forall_invalid_run(phase, probe.input()))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ForallInvalidRecovery {
    Binder,
    Colon,
    Body,
    Boundary,
}

#[derive(Clone, Copy)]
enum ForallRecoveryPhase {
    FirstBinder,
    AfterBinder,
    Body,
}

/// Shared AST/direct cursor movement for one malformed forall phase.  The
/// candidate classification is phase-specific, while byte ownership comes
/// entirely from the common TypeExpression malformed-run scanner.
fn scan_forall_invalid_run<E>(
    phase: ForallRecoveryPhase,
    i: &mut SynIn<E>,
) -> Option<(Range<usize>, ForallInvalidRecovery)>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let newline_policy = TypeMalformedNewlinePolicy::ContinuationQualified {
        continuation_base: active_type_continuation_base(i),
    };
    let (range, recovery) = scan_type_item_invalid_run_with(
        i,
        |i| forall_recovery_candidate(phase, i).is_some(),
        |i| forall_recovery_candidate_after_trivia(phase, i).is_some(),
        |i| forall_recovery_boundary_pending(phase, i),
        |i| type_item_boundary_after_trivia_with_policy(
            i,
            newline_policy,
            |i| forall_recovery_boundary_pending(phase, i),
        ),
    )?;
    let recovery = match recovery {
        TypeItemRecovery::Retry => forall_recovery_candidate(phase, i)
            .or_else(|| forall_recovery_candidate_after_trivia(phase, i))
            .expect("forall malformed scanner stopped at its phase candidate"),
        TypeItemRecovery::Boundary => ForallInvalidRecovery::Boundary,
    };
    Some((range, recovery))
}

/// Probe only the token which may legally resume this particular forall
/// phase.  Trivia is scanned as part of the malformed run, so reaching a
/// space alone is never mistaken for a retry.
fn forall_recovery_candidate<E>(phase: ForallRecoveryPhase, i: &mut SynIn<E>) -> Option<ForallInvalidRecovery>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let recovery = match phase {
        ForallRecoveryPhase::FirstBinder => {
            if scan_forall_binder(i).is_some() { Some(ForallInvalidRecovery::Binder) }
            else if scan_exact_colon(i).is_some() { Some(ForallInvalidRecovery::Colon) }
            else { None }
        }
        ForallRecoveryPhase::AfterBinder => {
            if scan_forall_binder(i).is_some() { Some(ForallInvalidRecovery::Binder) }
            else if scan_exact_colon(i).is_some() { Some(ForallInvalidRecovery::Colon) }
            else if type_primary_candidate(i) { Some(ForallInvalidRecovery::Body) }
            else { None }
        }
        ForallRecoveryPhase::Body => type_primary_candidate(i).then_some(ForallInvalidRecovery::Body),
    };
    i.rollback(checkpoint);
    recovery
}

fn forall_recovery_candidate_after_trivia<E>(
    phase: ForallRecoveryPhase,
    i: &mut SynIn<E>,
) -> Option<ForallInvalidRecovery>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = consume_forall_trivia(i, false);
    let candidate = trivia
        .filter(|trivia| !trivia.is_empty())
        .and_then(|_| forall_recovery_candidate(phase, i));
    i.rollback(checkpoint);
    candidate
}

/// A first forall binder owns an otherwise-unowned comma or semicolon as
/// malformed input.  Every other boundary follows the common type rule.
fn forall_recovery_boundary_pending<E>(phase: ForallRecoveryPhase, i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let punctuation = i.run(scan_punctuation).map(|punctuation| punctuation.kind());
    i.rollback(checkpoint);
    match punctuation {
        Some(PunctuationKind::Comma) if matches!(phase, ForallRecoveryPhase::FirstBinder) => {
            active_stop_set(i).contains(StopKind::Comma)
        }
        Some(PunctuationKind::Semicolon) if matches!(phase, ForallRecoveryPhase::FirstBinder) => {
            active_stop_set(i).contains(StopKind::Semicolon)
        }
        _ => type_recovery_boundary_pending(i),
    }
}

#[derive(Clone, Copy)]
struct TypeDelimitedSpec {
    owner: TypeDelimitedOwner,
    shape: TypeDelimitedShape,
}

impl TypeDelimitedSpec {
    fn item_role(self) -> TypeRole {
        match self.owner {
            TypeDelimitedOwner::Call => TypeRole::CallArgument,
            TypeDelimitedOwner::ParenthesizedGroup => TypeRole::ParenthesizedItem,
            TypeDelimitedOwner::NamedRecord => TypeRole::RecordField,
            TypeDelimitedOwner::EffectRow => TypeRole::EffectRowItem,
            TypeDelimitedOwner::PolymorphicVariant => TypeRole::PolymorphicVariantPayload,
        }
    }

    fn separator_role(self) -> TypeRole {
        match self.owner {
            TypeDelimitedOwner::Call => TypeRole::CallArgumentSeparator,
            TypeDelimitedOwner::ParenthesizedGroup => TypeRole::ParenthesizedSeparator,
            TypeDelimitedOwner::NamedRecord => TypeRole::RecordFieldSeparator,
            TypeDelimitedOwner::EffectRow => TypeRole::EffectRowSeparator,
            TypeDelimitedOwner::PolymorphicVariant => TypeRole::PolymorphicVariantTagSeparator,
        }
    }

    fn close_spec(self) -> CloseRecoverySpec {
        CloseRecoverySpec {
            delimiter: self.shape.delimiter(),
            owner: match self.owner {
                TypeDelimitedOwner::Call => ConstructRole::TypeCall,
                TypeDelimitedOwner::ParenthesizedGroup => ConstructRole::ParenthesizedTypeGroup,
                TypeDelimitedOwner::NamedRecord => ConstructRole::NamedRecordType,
                TypeDelimitedOwner::EffectRow => ConstructRole::EffectRowType,
                TypeDelimitedOwner::PolymorphicVariant => ConstructRole::PolymorphicVariantType,
            },
            matching_kind: self.shape.close_kind(),
            missing_after_mismatch: match self.owner {
                TypeDelimitedOwner::EffectRow => MissingAfterMismatch::Suppress,
                _ => MissingAfterMismatch::Emit,
            },
        }
    }
}

trait TypeDelimitedContext<'source>: TypeCloseSlotContext<'source> {
    fn emit_trivia(&mut self, trivia: &TriviaRun);
    fn emit_incomplete_item(&mut self, role: TypeRole);
    fn emit_malformed_item(&mut self);
    fn emit_item_error(&mut self, role: TypeRole, range: Range<usize>);
    fn emit_separator(&mut self, separator: TypeExplicitSeparator);
    fn emit_missing_separator(&mut self, role: TypeRole);
    fn set_trailing_separator(&mut self, separator: TypeExplicitSeparator);
    fn parse_item(&mut self) -> bool;
}

/// Shared item/sequence judge for call arguments, parenthesized type groups,
/// and effect rows.  Contexts retain only AST/CST realization; this driver
/// owns every post-scanner transition and all close-slot handoff.
fn drive_type_delimited<'source, C>(
    context: &mut C,
    spec: TypeDelimitedSpec,
) -> Recovered<Range<usize>>
where
    C: TypeDelimitedContext<'source>,
    Unexpected<char>: Into<<C::Error as ErrorSink<usize>>::Error>,
    UnexpectedEndOfInput: Into<<C::Error as ErrorSink<usize>>::Error>,
{
    let incoming = context.with_input(|i| {
        i.local.indentation_baseline().map_or(0, |baseline| baseline.column)
    });
    let stops = context.with_input(|i| {
        active_stop_set(i)
            .with(StopKind::Comma)
            .with(StopKind::Semicolon)
            .with(spec.shape.close_stop())
    });
    context.with_input(|i| {
        i.local.push_delimiter(spec.shape.delimiter());
        i.local.push_stop_set(stops);
        i.local.push_type_delimited_owner(spec.owner);
    });
    let opening = context.with_input(consume_trivia);
    context.emit_trivia(&opening);
    let layout = context.with_input(|i| {
        LayoutDelimitedFrame::after_opening_trivia(incoming, &opening, i.local.line().line_indent)
    });
    context.with_input(|i| push_layout(layout, i));

    loop {
        if context.with_input(|i| type_delimited_close_or_mismatch_pending(spec.shape, i)) {
            break;
        }
        if context.with_input(separator_pending) {
            context.emit_incomplete_item(spec.item_role());
            let separator = context.with_input(scan_separator)
                .expect("the separator pending probe accepted a literal separator");
            context.emit_separator(separator);
            let trailing = context.with_input(consume_trivia);
            context.emit_trivia(&trailing);
            continue;
        }
        if !context.parse_item() {
            let recovered = context.with_input(scan_type_item_invalid_run);
            let Some((range, _)) = recovered else {
                context.emit_incomplete_item(spec.item_role());
                break;
            };
            context.emit_item_error(spec.item_role(), range);
            match context.with_input(|i| {
                classify_type_delimited_recovery(
                    DelimitedRecoverySpec { delimiter: spec.shape.delimiter() },
                    layout,
                    direct_type_primary_candidate,
                    i,
                )
            }) {
                DelimitedRecoveryTarget::RetryPrimary => {
                    let trivia = context.with_input(consume_trivia);
                    context.emit_trivia(&trivia);
                    continue;
                }
                DelimitedRecoveryTarget::ExplicitSeparator(separator) => {
                    context.emit_malformed_item();
                    let trivia = context.with_input(consume_trivia);
                    context.emit_trivia(&trivia);
                    let consumed = context.with_input(scan_separator)
                        .expect("the recovery classifier accepted a separator");
                    debug_assert_eq!(separator_range(&consumed), separator_range(&separator));
                    context.emit_separator(consumed);
                    let trailing = context.with_input(consume_trivia);
                    context.emit_trivia(&trailing);
                    continue;
                }
                DelimitedRecoveryTarget::ImplicitNewline => {
                    context.emit_malformed_item();
                    let trivia = context.with_input(consume_trivia);
                    context.emit_trivia(&trivia);
                    continue;
                }
                DelimitedRecoveryTarget::MatchingClose(_) | DelimitedRecoveryTarget::LocalMismatchedClose(_) => {
                    context.emit_malformed_item();
                    let trivia = context.with_input(consume_trivia);
                    context.emit_trivia(&trivia);
                    break;
                }
                DelimitedRecoveryTarget::OuterBoundary => {
                    context.emit_malformed_item();
                    let trivia = context.with_input(consume_type_chain_trivia);
                    if let Some(trivia) = trivia.as_ref() {
                        context.emit_trivia(trivia);
                    }
                    break;
                }
            }
        }

        let trivia = context.with_input(consume_trivia);
        context.emit_trivia(&trivia);
        if let Some(separator) = context.with_input(scan_separator) {
            context.emit_separator(separator.clone());
            let trailing = context.with_input(consume_trivia);
            context.emit_trivia(&trailing);
            if context.with_input(|i| close_delimiter_pending(spec.shape, i)) {
                context.set_trailing_separator(separator);
                break;
            }
            if trailing.is_empty() && context.with_input(|i| i.input.remainder().is_empty()) {
                context.emit_incomplete_item(spec.item_role());
                break;
            }
            continue;
        }
        if context.with_input(|i| type_delimited_close_or_mismatch_pending(spec.shape, i)) {
            break;
        }
        match context.with_input(|i| layout.boundary_after_trivia(&trivia, i.local.line().line_indent)) {
            LayoutDelimitedBoundary::ImplicitNewline => continue,
            LayoutDelimitedBoundary::DeeperNewline => {
                if context.with_input(direct_type_primary_candidate) {
                    context.emit_missing_separator(spec.separator_role());
                    continue;
                }
                break;
            }
            LayoutDelimitedBoundary::None => {
                if context.with_input(direct_type_primary_candidate) {
                    context.emit_missing_separator(spec.separator_role());
                    continue;
                }
                break;
            }
        }
    }

    let close = drive_type_close_slot(context, spec.close_spec());
    context.with_input(|i| {
        pop_layout(layout, i);
        assert_eq!(i.local.pop_type_delimited_owner(), Some(spec.owner));
        assert_eq!(i.local.pop_stop_set(), Some(stops));
        assert_eq!(i.local.pop_delimiter(), Some(spec.shape.delimiter()));
    });
    close
}

fn close_delimiter_pending<E>(shape: TypeDelimitedShape, i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = scan_close_delimiter(shape, i).is_some();
    i.rollback(checkpoint);
    pending
}

fn type_delimited_close_or_mismatch_pending<E>(shape: TypeDelimitedShape, i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = scan_close_delimiter(shape, i).is_some()
        || scan_mismatched_close_for(shape.delimiter(), i).is_some();
    i.rollback(checkpoint);
    pending
}

fn separator_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = scan_separator(i).is_some();
    i.rollback(checkpoint);
    pending
}

struct DirectTypeDelimitedContext<'context, 'parse, 'source, 'local, E: ErrorSink<usize>, O: CommitOutput<'source>> {
    committed: &'context mut Committed<'parse, 'source, 'local, E, O>,
}

impl<'source, E, O> TypeCloseSlotContext<'source>
    for DirectTypeDelimitedContext<'_, '_, 'source, '_, E, O>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    type Error = E;

    fn with_input<R>(
        &mut self,
        f: impl FnOnce(&mut SynIn<'_, 'source, '_, Self::Error>) -> R,
    ) -> R {
        self.committed.probe(|probe| f(probe.input()))
    }

    fn emit_close_trivia(&mut self, trivia: &TriviaRun) {
        self.committed.emit_trivia(trivia);
    }

    fn emit_matching_close(&mut self, kind: SyntaxKind, range: Range<usize>) {
        self.committed.token(kind, range);
    }

    fn emit_mismatched_close(&mut self, role: GrammarRole, range: Range<usize>, expected: ExpectedSyntax) {
        emit_error_with_role(self.committed, role, range, expected);
    }

    fn emit_missing_close(&mut self, role: GrammarRole, expected: ExpectedSyntax) {
        emit_type_missing(self.committed, role, expected);
    }
}

impl<'source, E, O> TypeDelimitedContext<'source>
    for DirectTypeDelimitedContext<'_, '_, 'source, '_, E, O>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    fn emit_trivia(&mut self, trivia: &TriviaRun) {
        self.committed.emit_trivia(trivia);
    }

    fn emit_incomplete_item(&mut self, role: TypeRole) {
        emit_type_missing(self.committed, GrammarRole::Type(role), ExpectedSyntax::TypeExpression);
    }

    fn emit_malformed_item(&mut self) {}

    fn emit_item_error(&mut self, role: TypeRole, range: Range<usize>) {
        emit_type_error(self.committed, role, range, ExpectedSyntax::TypeExpression);
    }

    fn emit_separator(&mut self, separator: TypeExplicitSeparator) {
        self.committed.token(separator_kind(&separator), separator_range(&separator));
    }

    fn emit_missing_separator(&mut self, role: TypeRole) {
        emit_type_missing(
            self.committed,
            GrammarRole::Type(role),
            ExpectedSyntax::DelimitedSequenceSeparator,
        );
    }

    fn set_trailing_separator(&mut self, _separator: TypeExplicitSeparator) {}

    fn parse_item(&mut self) -> bool {
        commit_direct_type_expression(self.committed).is_some()
    }
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
    if let Some((kind, range)) = prefix {
        committed.token(kind, range);
    }
    committed.token(shape.open_kind(), open);
    let _ = drive_type_delimited(
        &mut DirectTypeDelimitedContext { committed },
        TypeDelimitedSpec { owner, shape },
    );
    committed.finish_node();
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
    let mut after_semicolon = false;
    loop {
        if after_semicolon {
            match committed.probe(|probe| classify_named_record_recovery(layout, probe.input())) {
                DelimitedRecoveryTarget::RetryPrimary | DelimitedRecoveryTarget::ImplicitNewline
                | DelimitedRecoveryTarget::ExplicitSeparator(_) => {
                    let trivia = consume_direct_trivia(committed);
                    committed.emit_trivia(&trivia);
                    after_semicolon = false;
                    continue;
                }
                DelimitedRecoveryTarget::MatchingClose(_) | DelimitedRecoveryTarget::LocalMismatchedClose(_) => {
                    let trivia = consume_direct_trivia(committed);
                    committed.emit_trivia(&trivia);
                    break;
                }
                DelimitedRecoveryTarget::OuterBoundary => {
                    if let Some(trivia) = consume_direct_type_chain_trivia(committed) {
                        committed.emit_trivia(&trivia);
                    }
                    break;
                }
            }
        }
        if committed.probe(|probe| close_brace_pending(probe.input()) || record_local_mismatched_close_pending(probe.input())) { break; }
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
            after_semicolon = true;
            continue;
        }
        if !commit_direct_type_record_field(committed) {
            if let Some((range, _)) = committed.probe(|probe| scan_record_invalid_run(probe.input())) {
                emit_type_error(committed, TypeRole::RecordField, range, ExpectedSyntax::Identifier);
                match committed.probe(|probe| classify_named_record_recovery(layout, probe.input())) {
                    DelimitedRecoveryTarget::RetryPrimary | DelimitedRecoveryTarget::ImplicitNewline => {
                        let trivia = consume_direct_trivia(committed);
                        committed.emit_trivia(&trivia);
                        continue;
                    }
                    DelimitedRecoveryTarget::ExplicitSeparator(_) => {
                        let trivia = consume_direct_trivia(committed);
                        committed.emit_trivia(&trivia);
                        let separator = committed
                            .probe(|probe| scan_separator(probe.input()))
                            .expect("record-item recovery classified an explicit separator");
                        match separator {
                            TypeExplicitSeparator::Comma(comma) => {
                                committed.token(SyntaxKind::Comma, comma);
                            }
                            TypeExplicitSeparator::Semicolon(semicolon) => {
                                emit_type_error(
                                    committed,
                                    TypeRole::RecordFieldSeparator,
                                    semicolon,
                                    ExpectedSyntax::DelimitedSequenceSeparator,
                                );
                                after_semicolon = true;
                            }
                        }
                        let post = consume_direct_trivia(committed);
                        committed.emit_trivia(&post);
                        continue;
                    }
                    DelimitedRecoveryTarget::MatchingClose(_) | DelimitedRecoveryTarget::LocalMismatchedClose(_) => {
                        let trivia = consume_direct_trivia(committed);
                        committed.emit_trivia(&trivia);
                        break;
                    }
                    DelimitedRecoveryTarget::OuterBoundary => {
                        if let Some(trivia) = consume_direct_type_chain_trivia(committed) {
                            committed.emit_trivia(&trivia);
                        }
                        break;
                    }
                }
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
            after_semicolon = true;
            continue;
        }
        if committed.probe(|probe| close_brace_pending(probe.input()) || record_local_mismatched_close_pending(probe.input())) { break; }
        if committed.probe(|probe| layout.boundary_after_trivia(&trivia, probe.input().local.line().line_indent)) == LayoutDelimitedBoundary::ImplicitNewline {
            continue;
        }
        if committed.probe(|probe| named_record_next_field_candidate(probe.input(), &trivia)) {
            emit_type_missing(committed, GrammarRole::Type(TypeRole::RecordFieldSeparator), ExpectedSyntax::DelimitedSequenceSeparator);
            continue;
        }
        break;
    }
    let _ = drive_type_close_slot(
        &mut DirectTypeCloseContext { committed },
        CloseRecoverySpec {
            delimiter: Delimiter::Brace,
            owner: ConstructRole::NamedRecordType,
            matching_kind: SyntaxKind::RBrace,
            missing_after_mismatch: MissingAfterMismatch::Emit,
        },
    );
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
        if let Some(trivia) = consume_direct_type_chain_trivia(committed) {
            committed.emit_trivia(&trivia);
        }
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
        } else if committed.probe(|probe| type_primary_candidate(probe.input())) {
            emit_type_missing(committed, GrammarRole::Type(TypeRole::RecordFieldColon), ExpectedSyntax::Punctuation(PunctuationEvidence::Colon));
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
    if let Some(trivia) = consume_direct_type_chain_trivia(committed) {
        committed.emit_trivia(&trivia);
    }
    if type_expected && commit_direct_type_expression(committed).is_none() {
        match direct_type_item_error_retry(committed, TypeRole::RecordFieldType) {
            Some(TypeItemRecovery::Retry) => {
                if commit_direct_type_expression(committed).is_none() {
                    emit_type_missing(committed, GrammarRole::Type(TypeRole::RecordFieldType), ExpectedSyntax::TypeExpression);
                }
            }
            Some(TypeItemRecovery::Boundary) => {}
            None => {
                emit_type_missing(committed, GrammarRole::Type(TypeRole::RecordFieldType), ExpectedSyntax::TypeExpression);
            }
        }
    }
    committed.finish_node();
    true
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
    let context = TypePrimaryContext::from_allow_forall(allow_forall);
    match recognize_type_primary_head(context, i)? {
        TypePrimaryHead::Forall(keyword) => {
            Some(TypePrimary::Forall(parse_forall_type(keyword, i)))
        }
        TypePrimaryHead::EffectRow { apostrophe, open } => {
            Some(TypePrimary::EffectRow(parse_effect_row_type(apostrophe, open, i)))
        }
        TypePrimaryHead::PolymorphicVariant { colon, open } => {
            Some(TypePrimary::PolymorphicVariant(polymorphic_variant::parse(colon, open, i)))
        }
        TypePrimaryHead::Name(name) => Some(TypePrimary::Atom(match name {
            TypeName::Identifier(word) => TypeAtom::Identifier(word),
            TypeName::SigilIdentifier(word) => TypeAtom::SigilIdentifier(word),
        })),
        TypePrimaryHead::Number(number) => Some(TypePrimary::Atom(TypeAtom::Number(number))),
        TypePrimaryHead::Parenthesized(open) => {
            Some(TypePrimary::Parenthesized(parse_parenthesized_type_group(open, i)))
        }
        TypePrimaryHead::Record(open) => {
            Some(TypePrimary::Record(parse_named_record_type(open, i)))
        }
    }
}

fn recognize_type_primary_head<'source, E>(
    context: TypePrimaryContext,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<TypePrimaryHead<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if classify_type_boundary(
        TypeBoundaryPolicy {
            matching_close: None,
            local_separators: StopSet::default(),
            locally_owned_stops: StopSet::default(),
        },
        i,
    )
    .is_some()
    {
        return None;
    }
    if context.allows_forall() {
        if let Some(keyword) = scan_forall_keyword(i) {
            return Some(TypePrimaryHead::Forall(keyword));
        }
    }
    if let Some((apostrophe, open)) = scan_effect_row_open(i) {
        return Some(TypePrimaryHead::EffectRow { apostrophe, open });
    }
    if let Some((colon, open)) = scan_polymorphic_variant_open(i) {
        return Some(TypePrimaryHead::PolymorphicVariant { colon, open });
    }
    if let Some(name) = scan_type_name(i) {
        return Some(TypePrimaryHead::Name(name));
    }
    if i.input.remainder().chars().next().is_some_and(|character| character.is_ascii_digit()) {
        if let Some(integer) = i.run(parse_integer_literal) {
            return Some(TypePrimaryHead::Number(TypeNumberAtom {
                text: integer.text(),
                range: integer.range(),
            }));
        }
    }
    if let Some(open) = scan_open_parenthesis(i) {
        return Some(TypePrimaryHead::Parenthesized(open));
    }
    scan_open_brace(i).map(TypePrimaryHead::Record)
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
    } else if let Some(recovery) = recover_forall_for_ast(ForallRecoveryPhase::FirstBinder, i) {
        binders.push(Recovered::Incomplete);
        match recovery {
            ForallInvalidRecovery::Binder => {
                let gap = consume_forall_trivia(i, true);
                let name = scan_forall_binder(i).expect("forall recovery stopped at a binder");
                let boundary = gap.map_or(Recovered::Incomplete, |trivia| Recovered::Complete(trivia.range()));
                let end = name.range().end;
                let binder_start = match &boundary { Recovered::Complete(range) => range.start, Recovered::Incomplete => name.range().start };
                binders.push(Recovered::Complete(ForallTypeBinder { boundary, name, range: binder_start..end }));
            }
            ForallInvalidRecovery::Colon => {
                let found_colon = consume_forall_recovered_colon_for_ast(i);
                colon = Recovered::Complete(found_colon);
                body = parse_forall_body_for_ast(i);
                let end = forall_end(&keyword, &binders, &colon, &body, i.pos());
                return ForallType { keyword, binders, colon, body, range: start..end };
            }
            ForallInvalidRecovery::Body | ForallInvalidRecovery::Boundary => {
                let end = forall_end(&keyword, &binders, &colon, &body, i.pos());
                return ForallType { keyword, binders, colon, body, range: start..end };
            }
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
        match recover_forall_for_ast(ForallRecoveryPhase::AfterBinder, i) {
            Some(ForallInvalidRecovery::Binder) => continue,
            Some(ForallInvalidRecovery::Colon) => {
                let found_colon = consume_forall_recovered_colon_for_ast(i);
                colon = Recovered::Complete(found_colon);
                body = parse_forall_body_for_ast(i);
                break;
            }
            Some(ForallInvalidRecovery::Body) => {
                colon = Recovered::Incomplete;
                body = parse_forall_body_for_ast(i);
                break;
            }
            Some(ForallInvalidRecovery::Boundary) | None => break,
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

fn consume_forall_recovered_colon_for_ast<E>(i: &mut SynIn<E>) -> Range<usize>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let _ = consume_forall_trivia(i, false);
    scan_exact_colon(i).expect("forall recovery stopped at a colon")
}

fn parse_forall_body_for_ast<'source, E>(i: &mut SynIn<'_, 'source, '_, E>) -> Recovered<Box<TypeExpression<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let _ = consume_forall_trivia(i, false);
    i.run(from_fn(|i| parse_type_expression_with_outer_missing_role(None, i)))
        .or_else(|| {
            if recover_forall_for_ast(ForallRecoveryPhase::Body, i) == Some(ForallInvalidRecovery::Body) {
                let _ = consume_forall_trivia(i, false);
                i.run(from_fn(|i| parse_type_expression_with_outer_missing_role(None, i)))
            } else {
                None
            }
        })
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

fn recover_forall_for_ast<E>(phase: ForallRecoveryPhase, i: &mut SynIn<E>) -> Option<ForallInvalidRecovery>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    scan_forall_invalid_run(phase, i).map(|(_, recovery)| recovery)
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
    let mut after_semicolon = false;
    loop {
        if after_semicolon {
            match classify_named_record_recovery(layout, i) {
                DelimitedRecoveryTarget::RetryPrimary | DelimitedRecoveryTarget::ImplicitNewline => {
                    let _ = consume_trivia(i);
                    after_semicolon = false;
                    continue;
                }
                DelimitedRecoveryTarget::ExplicitSeparator(_) => {
                    let _ = consume_trivia(i);
                    after_semicolon = false;
                    continue;
                }
                DelimitedRecoveryTarget::MatchingClose(_) | DelimitedRecoveryTarget::LocalMismatchedClose(_) => {
                    let _ = consume_trivia(i);
                    break;
                }
                DelimitedRecoveryTarget::OuterBoundary => {
                    let _ = consume_type_chain_trivia(i);
                    break;
                }
            }
        }
        if close_brace_pending(i) || record_local_mismatched_close_pending(i) { break; }
        if scan_record_comma(i).is_some() {
            fields.push(Recovered::Incomplete);
            let _ = consume_trivia(i);
            continue;
        }
        if scan_record_semicolon(i).is_some() {
            after_semicolon = true;
            continue;
        }
        if let Some(field) = parse_type_record_field(i) {
            fields.push(Recovered::Complete(field));
        } else if let Some(_) = recover_record_item_for_ast(i) {
            fields.push(Recovered::Incomplete);
            match classify_named_record_recovery(layout, i) {
                DelimitedRecoveryTarget::RetryPrimary | DelimitedRecoveryTarget::ImplicitNewline => {
                    let _ = consume_trivia(i);
                    continue;
                }
                DelimitedRecoveryTarget::ExplicitSeparator(_) => {
                    let _ = consume_trivia(i);
                    let _ = scan_separator(i);
                    let _ = consume_trivia(i);
                    continue;
                }
                DelimitedRecoveryTarget::MatchingClose(_) | DelimitedRecoveryTarget::LocalMismatchedClose(_) => {
                    let _ = consume_trivia(i);
                    break;
                }
                DelimitedRecoveryTarget::OuterBoundary => {
                    let _ = consume_type_chain_trivia(i);
                    break;
                }
            }
        } else {
            fields.push(Recovered::Incomplete);
            break;
        }
        let trivia = consume_trivia(i);
        if let Some(comma) = scan_record_comma(i) {
            let post = consume_trivia(i);
            if close_brace_pending(i) {
                trailing_comma = Some(comma);
                break;
            }
            if post.is_empty() && i.input.remainder().is_empty() {
                fields.push(Recovered::Incomplete);
                break;
            }
            continue;
        }
        if scan_record_semicolon(i).is_some() {
            after_semicolon = true;
            continue;
        }
        if close_brace_pending(i) || record_local_mismatched_close_pending(i) { break; }
        match layout.boundary_after_trivia(&trivia, i.local.line().line_indent) {
            LayoutDelimitedBoundary::ImplicitNewline => continue,
            LayoutDelimitedBoundary::None if named_record_next_field_candidate(i, &trivia) => continue,
            _ => break,
        }
    }
    let close = drive_type_close_slot(
        i,
        CloseRecoverySpec {
            delimiter: Delimiter::Brace,
            owner: ConstructRole::NamedRecordType,
            matching_kind: SyntaxKind::RBrace,
            missing_after_mismatch: MissingAfterMismatch::Emit,
        },
    );
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
    let (name, colon, type_expected) = if let Some(name) = scan_plain_type_identifier(i) {
        let _ = consume_type_chain_trivia(i);
        if let Some(colon) = scan_exact_colon(i) {
            (Recovered::Complete(name), Recovered::Complete(colon), true)
        } else if scan_exact_equals(i).is_some() {
            (Recovered::Complete(name), Recovered::Incomplete, true)
        } else if type_primary_candidate(i) {
            (Recovered::Complete(name), Recovered::Incomplete, true)
        } else if consume_record_colon_invalid_run(i).is_some() {
            let recovered_colon = scan_exact_colon(i);
            let type_expected = recovered_colon.is_some() || type_primary_candidate(i);
            (
                Recovered::Complete(name),
                recovered_colon.map_or(Recovered::Incomplete, Recovered::Complete),
                type_expected,
            )
        } else {
            let type_expected = type_primary_candidate(i);
            (Recovered::Complete(name), Recovered::Incomplete, type_expected)
        }
    } else if let Some(colon) = scan_exact_colon(i) {
        (Recovered::Incomplete, Recovered::Complete(colon), true)
    } else if let Some((_, colon)) = scan_malformed_record_name_colon(i) {
        (Recovered::Incomplete, Recovered::Complete(colon), true)
    } else {
        return None;
    };
    let _ = consume_type_chain_trivia(i);
    let type_expr = type_expected
        .then(|| {
            i.run(from_fn(|i| parse_type_expression_with_outer_missing_role(None, i)))
                .or_else(|| {
                    recover_type_item_for_ast(i)
                        .then(|| i.run(from_fn(|i| parse_type_expression_with_outer_missing_role(None, i))))
                        .flatten()
                })
                .map(|value| Recovered::Complete(Box::new(value)))
                .unwrap_or(Recovered::Incomplete)
        })
        .unwrap_or(Recovered::Incomplete);
    let end = match &type_expr { Recovered::Complete(value) => value.range.end, Recovered::Incomplete => match &colon { Recovered::Complete(colon) => colon.end, Recovered::Incomplete => match &name { Recovered::Complete(name) => name.range().end, Recovered::Incomplete => start } } };
    Some(TypeRecordField { name, colon, type_expr, range: start..end })
}

struct AstTypeDelimitedContext<'context, 'parse, 'source, 'local, E: ErrorSink<usize>> {
    i: &'context mut SynIn<'parse, 'source, 'local, E>,
    items: Vec<Recovered<TypeExpression<'source>>>,
    trailing: Option<TypeExplicitSeparator>,
}

impl<'source, E> TypeCloseSlotContext<'source>
    for AstTypeDelimitedContext<'_, '_, 'source, '_, E>
where
    E: ErrorSink<usize>,
{
    type Error = E;

    fn with_input<R>(
        &mut self,
        f: impl FnOnce(&mut SynIn<'_, 'source, '_, Self::Error>) -> R,
    ) -> R {
        f(self.i)
    }

    fn emit_close_trivia(&mut self, _trivia: &TriviaRun) {}
    fn emit_matching_close(&mut self, _kind: SyntaxKind, _range: Range<usize>) {}
    fn emit_mismatched_close(&mut self, _role: GrammarRole, _range: Range<usize>, _expected: ExpectedSyntax) {}
    fn emit_missing_close(&mut self, _role: GrammarRole, _expected: ExpectedSyntax) {}
}

impl<'source, E> TypeDelimitedContext<'source>
    for AstTypeDelimitedContext<'_, '_, 'source, '_, E>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    fn emit_trivia(&mut self, _trivia: &TriviaRun) {}

    fn emit_incomplete_item(&mut self, _role: TypeRole) {
        self.items.push(Recovered::Incomplete);
    }

    fn emit_malformed_item(&mut self) {
        self.items.push(Recovered::Incomplete);
    }

    fn emit_item_error(&mut self, _role: TypeRole, _range: Range<usize>) {}
    fn emit_separator(&mut self, _separator: TypeExplicitSeparator) {}
    fn emit_missing_separator(&mut self, _role: TypeRole) {}

    fn set_trailing_separator(&mut self, separator: TypeExplicitSeparator) {
        self.trailing = Some(separator);
    }

    fn parse_item(&mut self) -> bool {
        let value = self.i.run(from_fn(|i| parse_type_expression_with_outer_missing_role(None, i)));
        if let Some(value) = value {
            self.items.push(Recovered::Complete(value));
            true
        } else {
            false
        }
    }
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
    let mut context = AstTypeDelimitedContext {
        i,
        items: Vec::new(),
        trailing: None,
    };
    let close = drive_type_delimited(&mut context, TypeDelimitedSpec { owner, shape });
    (context.items, context.trailing, close)
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
    scan_type_item_invalid_run(i).is_some()
}

fn recover_record_item_for_ast<E>(i: &mut SynIn<E>) -> Option<TypeItemRecovery>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    scan_record_invalid_run(i).map(|(_, recovery)| recovery)
}

fn recover_type_path_for_ast<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    scan_type_path_invalid_run(i).is_some()
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
    let context = TypePrimaryContext::from_allow_forall(allow_forall);
    let candidate = recognize_type_primary_head(context, i).is_some();
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
    scan_close_for_delimiter(shape.delimiter(), i)
}

fn scan_close_for_delimiter<'source, E>(delimiter: Delimiter, i: &mut SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let checkpoint = i.checkpoint();
    let Some(punctuation) = i.run(scan_punctuation) else {
        i.rollback(checkpoint);
        return None;
    };
    if punctuation.kind() == PunctuationKind::Close(delimiter) { Some(punctuation.range()) } else { i.rollback(checkpoint); None }
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
    scan_exact_operator_spelling("=", i)
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
    let newline_policy = TypeMalformedNewlinePolicy::AnyPhysicalHandoff;
    let recovered = scan_type_item_invalid_run_with(
        i,
        exact_colon_pending,
        |_| false,
        record_colon_invalid_boundary_pending,
        |i| type_item_boundary_after_trivia_with_policy(
            i,
            newline_policy,
            record_colon_invalid_boundary_pending,
        ),
    );
    let Some((range, TypeItemRecovery::Retry)) = recovered else {
        i.rollback(checkpoint);
        return None;
    };
    let colon = scan_exact_colon(i).expect("record-name recovery stopped at a colon");
    Some((range, colon))
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
    scan_exact_operator_spelling("->", i)
}

/// Accept an operator-shaped token only when its complete maximal spelling
/// equals `expected`.  This is the same lexical rule used by pattern `=` and
/// `..`: an exact grammar token must not split a longer dynamic operator run.
fn scan_exact_operator_spelling<E>(expected: &str, i: &mut SynIn<E>) -> Option<Range<usize>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let checkpoint = i.checkpoint();
    let start = i.pos();
    while i.input.remainder().chars().next().is_some_and(is_operator_shaped_character) {
        i.input.next()?;
    }
    let end = i.pos();
    if &i.input.source()[start..end] != expected {
        i.rollback(checkpoint);
        return None;
    }
    let mut line = i.local.line();
    line.at_line_start = false;
    i.local.set_line(line);
    Some(start..end)
}

fn is_operator_shaped_character(character: char) -> bool {
    !character.is_whitespace()
        && !character.is_ascii_digit()
        && character != '_'
        && !unicode_ident::is_xid_continue(character)
        && !matches!(
            character,
            '(' | ')' | '[' | ']' | '{' | '}' | ',' | ':' | '/' | ';' | '\\' | '\'' | '@'
        )
}

fn consume_trivia<E>(i: &mut SynIn<E>) -> TriviaRun
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> { i.run(scan_trivia).expect("trivia scanning is total") }

/// The five TMN-C outcomes for one maximal trivia run after malformed type
/// input.  The scanner and its owner adapters must agree on this classifier
/// before deciding whether the following token is a local retry or boundary.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TypeMalformedTriviaClassification {
    NoNewline,
    CallerBoundary,
    Handoff,
    Boundary,
    DeeperContinuation,
}

/// Classify one maximal trivia run.  Its callers probe the run under a
/// checkpoint, so this comparison stays state-neutral.
fn classify_type_malformed_trivia<E>(
    i: &SynIn<E>,
    trivia: &TriviaRun,
    policy: TypeMalformedNewlinePolicy,
) -> TypeMalformedTriviaClassification
where
    E: ErrorSink<usize>,
{
    if !trivia_has_newline(trivia) {
        TypeMalformedTriviaClassification::NoNewline
    } else if active_stop_set(i).contains(StopKind::Newline) {
        TypeMalformedTriviaClassification::CallerBoundary
    } else {
        match policy {
            TypeMalformedNewlinePolicy::AnyPhysicalHandoff => {
                TypeMalformedTriviaClassification::Handoff
            }
            TypeMalformedNewlinePolicy::ContinuationQualified { continuation_base } => {
                if continues_after_newline(i, trivia, continuation_base) {
                    TypeMalformedTriviaClassification::DeeperContinuation
                } else {
                    TypeMalformedTriviaClassification::Boundary
                }
            }
        }
    }
}

/// Test whether trivia after malformed input leads straight to a boundary
/// without assigning that trivia to the malformed Error range.
fn type_item_boundary_after_trivia_with_policy<E>(
    i: &mut SynIn<E>,
    policy: TypeMalformedNewlinePolicy,
    boundary: impl FnOnce(&mut SynIn<E>) -> bool,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = consume_trivia(i);
    let classification = classify_type_malformed_trivia(i, &trivia, policy);
    let boundary = match classification {
        TypeMalformedTriviaClassification::NoNewline => !trivia.is_empty() && boundary(i),
        TypeMalformedTriviaClassification::CallerBoundary
        | TypeMalformedTriviaClassification::Handoff
        | TypeMalformedTriviaClassification::Boundary => true,
        TypeMalformedTriviaClassification::DeeperContinuation => false,
    };
    i.rollback(checkpoint);
    boundary
}

/// Compatibility shim for polymorphic variants until their existing shared
/// scanner call is made explicit in the dedicated AnyPhysicalHandoff slice.
/// This is intentionally not a generic default policy.
pub(super) fn type_item_boundary_after_trivia<E>(
    i: &mut SynIn<E>,
    boundary: impl FnOnce(&mut SynIn<E>) -> bool,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    type_item_boundary_after_trivia_with_policy(
        i,
        TypeMalformedNewlinePolicy::AnyPhysicalHandoff,
        boundary,
    )
}

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
    committed.probe(|probe| consume_type_chain_trivia(probe.input()))
}

/// Consume post-introducer trivia only when it remains inside the current type
/// chain.  The checkpoint is owned here so source-free AST and direct-CST
/// callers retain precisely the same outer-layout boundary.
fn consume_type_chain_trivia<E>(i: &mut SynIn<E>) -> Option<TriviaRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = consume_trivia(i);
    if type_chain_trivia(i, &trivia) {
        Some(trivia)
    } else {
        i.rollback(checkpoint);
        None
    }
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

/// Selects who owns a physical newline reached by a malformed type-item
/// scanner.  Every scanner caller chooses this explicitly; the policy has no
/// implicit default because candidate-complete and candidate-incomplete owner
/// phases have different handoff contracts.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum TypeMalformedNewlinePolicy {
    ContinuationQualified { continuation_base: usize },
    AnyPhysicalHandoff,
}

/// A malformed mandatory item may either stop before another type primary or
/// reach a boundary owned by its enclosing construct.  Both cases commit the
/// Error run; only the first may retry the required slot.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum TypeItemRecovery {
    Retry,
    Boundary,
}

/// Scan the shared malformed run for every TypeExpression slot.  The AST and
/// direct-CST paths deliberately share this cursor movement so a recovered
/// primary begins at the same byte on both paths.
fn scan_type_item_invalid_run<E>(i: &mut SynIn<E>) -> Option<(Range<usize>, TypeItemRecovery)>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let newline_policy = TypeMalformedNewlinePolicy::ContinuationQualified {
        continuation_base: active_type_continuation_base(i),
    };
    scan_type_item_invalid_run_with(
        i,
        direct_type_primary_candidate,
        |_| false,
        type_recovery_boundary_pending,
        |i| type_item_boundary_after_trivia_with_policy(
            i,
            newline_policy,
            type_recovery_boundary_pending,
        ),
    )
}

/// The common cursor discipline for malformed TypeExpression-adjacent slots.
/// Callers supply only their legal retry candidate and any narrower boundary
/// policy; physical line boundaries and active caller ownership remain one
/// implementation for every user.
pub(super) fn scan_type_item_invalid_run_with<E, Candidate, TriviaCandidate, Boundary, TriviaBoundary>(
    i: &mut SynIn<E>,
    mut candidate: Candidate,
    mut candidate_after_trivia: TriviaCandidate,
    mut boundary: Boundary,
    mut boundary_after_trivia: TriviaBoundary,
) -> Option<(Range<usize>, TypeItemRecovery)>
where
    E: ErrorSink<usize>,
    Candidate: FnMut(&mut SynIn<E>) -> bool,
    TriviaCandidate: FnMut(&mut SynIn<E>) -> bool,
    Boundary: FnMut(&mut SynIn<E>) -> bool,
    TriviaBoundary: FnMut(&mut SynIn<E>) -> bool,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let mut end = start;
    loop {
        if end == start {
            // TMN-S starts only after a non-empty malformed prefix.  Before
            // that point, a maximal trivia run containing a newline belongs
            // to the slot's normal missing/boundary handling rather than to a
            // synthetic Error run.
            let checkpoint = i.checkpoint();
            let trivia = consume_trivia(i);
            let starts_at_physical_newline = trivia_has_newline(&trivia);
            i.rollback(checkpoint);
            if starts_at_physical_newline {
                return None;
            }
        }
        if end > start {
            if candidate(i) || candidate_after_trivia(i) {
                return Some((start..end, TypeItemRecovery::Retry));
            }
            if boundary_after_trivia(i) {
                return Some((start..end, TypeItemRecovery::Boundary));
            }
        }
        if boundary(i) {
            return (start < end).then_some((start..end, TypeItemRecovery::Boundary));
        }
        // A comment may be malformed content, but it must remain one opaque
        // unit. Consume it separately so a following space or newline still
        // receives this caller's ordinary boundary classification.
        if i.run(scan_comment).is_some() {
            end = i.pos();
            continue;
        }

        // Non-comment trivia that neither resumes this slot nor reaches a
        // boundary belongs to the malformed run.
        let trivia = consume_trivia(i);
        if !trivia.is_empty() {
            end = i.pos();
            continue;
        }
        let Some(_) = i.input.remainder().chars().next() else {
            return (start < end).then_some((start..end, TypeItemRecovery::Boundary));
        };
        i.input.next()?;
        end = i.pos();
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
    }
}

/// Recover one malformed call/group item without crossing a delimiter or an
/// active caller stop.  A non-empty Error run ending at a boundary is still a
/// committed recovery site, but it is not an item retry and must not make the
/// list synthesize a second Missing item from the same cause.

/// Generic primary recovery used by the mandatory and arrow-RHS entries.
/// Delimited calls and groups use the boundary-aware variant above because
/// their close and separator slots need separate ownership.
fn direct_type_item_error_retry<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: TypeRole,
) -> Option<TypeItemRecovery>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let recovered = committed.probe(|probe| scan_type_item_invalid_run(probe.input()));
    let Some((range, recovery)) = recovered else { return None; };
    emit_type_error(committed, role, range, ExpectedSyntax::TypeExpression);
    Some(recovery)
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
    let checkpoint = i.checkpoint();
    let fixed = i.run(scan_punctuation).map(|punctuation| punctuation.kind());
    i.rollback(checkpoint);
    if matches!(
        fixed,
        Some(
            PunctuationKind::Close(_)
                | PunctuationKind::Comma
                | PunctuationKind::Semicolon
        )
    ) {
        return true;
    }
    matches!(
        classify_type_boundary(
            TypeBoundaryPolicy {
                matching_close: None,
                local_separators: StopSet::default(),
                locally_owned_stops: StopSet::default(),
            },
            i,
        ),
        Some(TypeBoundary::Eof | TypeBoundary::ActiveStop(_) | TypeBoundary::OuterOwnedClose)
    )
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TypeBoundary {
    Eof,
    ActiveStop(StopKind),
    MatchingClose,
    OuterOwnedClose,
    LocalSeparator,
    PhysicalNewline,
}

#[derive(Clone, Copy)]
struct TypeBoundaryPolicy {
    matching_close: Option<Delimiter>,
    local_separators: StopSet,
    locally_owned_stops: StopSet,
}

/// Classifies one source position without consuming it.  Exact lexical
/// recognition lives here; construct-specific judges decide which classified
/// boundaries they own.
fn classify_type_boundary<E>(policy: TypeBoundaryPolicy, i: &mut SynIn<E>) -> Option<TypeBoundary>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if i.input.remainder().is_empty() {
        return Some(TypeBoundary::Eof);
    }
    if matches!(i.input.remainder().chars().next(), Some('\n' | '\r')) {
        if active_stop_set(i).contains(StopKind::Newline)
            && !policy.locally_owned_stops.contains(StopKind::Newline)
        {
            return Some(TypeBoundary::ActiveStop(StopKind::Newline));
        }
        return Some(TypeBoundary::PhysicalNewline);
    }

    let checkpoint = i.checkpoint();
    let punctuation = i.run(scan_punctuation).map(|punctuation| punctuation.kind());
    i.rollback(checkpoint);
    match punctuation {
        Some(PunctuationKind::Close(delimiter)) if policy.matching_close == Some(delimiter) => {
            return Some(TypeBoundary::MatchingClose);
        }
        Some(PunctuationKind::Close(delimiter)) => {
            let stop = close_stop_kind(delimiter);
            if active_stop_set(i).contains(stop) && !policy.locally_owned_stops.contains(stop) {
                return Some(TypeBoundary::OuterOwnedClose);
            }
        }
        Some(PunctuationKind::Comma) if policy.local_separators.contains(StopKind::Comma) => {
            return Some(TypeBoundary::LocalSeparator);
        }
        Some(PunctuationKind::Semicolon) if policy.local_separators.contains(StopKind::Semicolon) => {
            return Some(TypeBoundary::LocalSeparator);
        }
        _ => {}
    }

    let active = active_stop_set(i).difference(policy.locally_owned_stops);
    StopKind::ALL
        .iter()
        .copied()
        .find(|stop| active.contains(*stop) && stop_kind_pending(*stop, i))
        .map(TypeBoundary::ActiveStop)
}

fn close_stop_kind(delimiter: Delimiter) -> StopKind {
    match delimiter {
        Delimiter::Parenthesis => StopKind::RightParenthesis,
        Delimiter::Bracket => StopKind::RightBracket,
        Delimiter::Brace => StopKind::RightBrace,
    }
}

/// One exact spelling probe per [`StopKind`].  The outer checkpoint keeps every
/// branch state-neutral, including scanners which succeed by consuming input.
fn stop_kind_pending<E>(stop: StopKind, i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = match stop {
        StopKind::Newline => matches!(i.input.remainder().chars().next(), Some('\n' | '\r')),
        StopKind::Comma => scan_record_comma(i).is_some(),
        StopKind::Semicolon => scan_record_semicolon(i).is_some(),
        StopKind::Colon => scan_exact_colon(i).is_some(),
        StopKind::LeftBrace => scan_open_brace(i).is_some(),
        StopKind::Elsif => i.run(scan_word).is_some_and(|word| word.text() == "elsif"),
        StopKind::Else => i.run(scan_word).is_some_and(|word| word.text() == "else"),
        StopKind::RightParenthesis => scan_close_delimiter(TypeDelimitedShape::Parenthesis, i).is_some(),
        StopKind::RightBracket => scan_close_delimiter(TypeDelimitedShape::Bracket, i).is_some(),
        StopKind::RightBrace => scan_close_brace(i).is_some(),
        StopKind::Equal => scan_exact_equals(i).is_some(),
        StopKind::Arrow => scan_exact_arrow(i).is_some(),
        StopKind::ArmGuardIf => i.run(scan_word).is_some_and(|word| word.text() == "if"),
        StopKind::ArmGuardWhere => i.run(scan_word).is_some_and(|word| word.text() == "where"),
        StopKind::With => i.run(scan_word).is_some_and(|word| word.text() == "with"),
    };
    i.rollback(checkpoint);
    pending
}

/// Structural type tails must yield to every active outer stop, matching the
/// mandatory recovery scanner's ownership boundary.
fn type_active_tail_stop_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    matches!(
        classify_type_boundary(
            TypeBoundaryPolicy {
                matching_close: None,
                local_separators: StopSet::default(),
                locally_owned_stops: StopSet::default(),
            },
            i,
        ),
        Some(TypeBoundary::ActiveStop(_))
    )
}

fn scan_type_path_invalid_run<E>(i: &mut SynIn<E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let newline_policy = TypeMalformedNewlinePolicy::ContinuationQualified {
        continuation_base: active_type_continuation_base(i),
    };
    scan_type_item_invalid_run_with(
        i,
        type_name_pending,
        |_| false,
        type_path_invalid_boundary_pending,
        |i| type_item_boundary_after_trivia_with_policy(
            i,
            newline_policy,
            type_path_invalid_boundary_pending,
        ),
    )
    .map(|(range, _)| range)
}

/// Scan one malformed named-record field head.  The cursor remains before
/// following trivia so both AST and direct paths can retain that trivia in
/// their ordinary sequence machinery; the sequence judge classifies that gap.
fn scan_record_invalid_run<E>(i: &mut SynIn<E>) -> Option<(Range<usize>, TypeItemRecovery)>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let newline_policy = TypeMalformedNewlinePolicy::ContinuationQualified {
        continuation_base: active_type_continuation_base(i),
    };
    scan_type_item_invalid_run_with(
        i,
        record_field_head_candidate,
        record_field_head_candidate_after_trivia,
        record_invalid_boundary_pending,
        |i| type_item_boundary_after_trivia_with_policy(
            i,
            newline_policy,
            record_invalid_boundary_pending,
        ),
    )
}

fn consume_record_colon_invalid_run<E>(i: &mut SynIn<E>) -> Option<Range<usize>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let newline_policy = TypeMalformedNewlinePolicy::ContinuationQualified {
        continuation_base: active_type_continuation_base(i),
    };
    scan_type_item_invalid_run_with(
        i,
        |i| exact_colon_pending(i) || type_primary_candidate(i),
        |_| false,
        record_colon_invalid_boundary_pending,
        |i| type_item_boundary_after_trivia_with_policy(
            i,
            newline_policy,
            record_colon_invalid_boundary_pending,
        ),
    )
    .map(|(range, _)| range)
}

fn type_name_pending<E>(i: &mut SynIn<E>) -> bool
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let checkpoint = i.checkpoint();
    let pending = scan_type_name(i).is_some();
    i.rollback(checkpoint);
    pending
}

fn exact_colon_pending<E>(i: &mut SynIn<E>) -> bool
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let checkpoint = i.checkpoint();
    let pending = scan_exact_colon(i).is_some();
    i.rollback(checkpoint);
    pending
}

fn type_path_invalid_boundary_pending<E>(i: &mut SynIn<E>) -> bool
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    matches!(i.input.remainder().chars().next(), Some(character) if (
        character.is_whitespace() && !matches!(character, '\n' | '\r')
    ) || character == ':')
        || type_recovery_boundary_pending(i)
}

fn record_field_head_candidate_after_trivia<E>(i: &mut SynIn<E>) -> bool
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let checkpoint = i.checkpoint();
    let trivia = consume_trivia(i);
    let candidate = !trivia.is_empty()
        && type_chain_trivia(i, &trivia)
        && record_field_head_candidate(i);
    i.rollback(checkpoint);
    candidate
}

fn record_comma_pending<E>(i: &mut SynIn<E>) -> bool
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let checkpoint = i.checkpoint();
    let pending = scan_record_comma(i).is_some();
    i.rollback(checkpoint);
    pending
}

fn close_brace_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = scan_close_brace(i).is_some();
    i.rollback(checkpoint);
    pending
}

fn record_field_start_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = scan_plain_type_identifier(i).is_some()
        || scan_exact_colon(i).is_some()
        || scan_malformed_record_name_colon(i).is_some();
    i.rollback(checkpoint);
    pending
}

fn classify_named_record_recovery<E>(
    layout: LayoutDelimitedFrame,
    i: &mut SynIn<E>,
) -> DelimitedRecoveryTarget
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    classify_type_delimited_recovery(
        DelimitedRecoverySpec {
            delimiter: Delimiter::Brace,
        },
        layout,
        record_field_start_pending,
        i,
    )
}

fn record_invalid_boundary_pending<E>(i: &mut SynIn<E>) -> bool
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    record_comma_pending(i)
        || record_local_mismatched_close_pending(i)
        || record_owner_boundary_pending(i)
}

fn record_local_mismatched_close_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = scan_mismatched_close_for(Delimiter::Brace, i).is_some();
    i.rollback(checkpoint);
    pending
}

fn record_colon_invalid_boundary_pending<E>(i: &mut SynIn<E>) -> bool
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    matches!(i.input.remainder().chars().next(), Some(character) if (
        character.is_whitespace() && !matches!(character, '\n' | '\r')
    ))
        || record_comma_pending(i)
        || record_owner_boundary_pending(i)
}

/// Named records own only their brace close.  A mismatched close remains
/// malformed record content unless an enclosing caller explicitly owns it.
fn record_owner_boundary_pending<E>(i: &mut SynIn<E>) -> bool
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let checkpoint = i.checkpoint();
    let own_close = scan_close_brace(i).is_some();
    i.rollback(checkpoint);
    own_close || matches!(
        classify_type_boundary(
            TypeBoundaryPolicy {
                matching_close: None,
                local_separators: StopSet::default(),
                locally_owned_stops: StopSet::default(),
            },
            i,
        ),
        Some(TypeBoundary::Eof | TypeBoundary::ActiveStop(_) | TypeBoundary::OuterOwnedClose)
    )
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

fn active_type_continuation_base<E>(i: &SynIn<E>) -> usize
where E: ErrorSink<usize> { i.local.indentation_baseline().map_or(0, |baseline| baseline.column) }

/// The one type-side continuation comparison.  `continuation_base` is
/// captured when the owning recovery phase starts; callers must not derive it
/// from a following token or a later recovery position.
fn continues_after_newline<E>(i: &SynIn<E>, trivia: &TriviaRun, continuation_base: usize) -> bool
where E: ErrorSink<usize> {
    trivia_has_newline(trivia) && i.local.line().line_indent > continuation_base
}

fn type_chain_trivia<E>(i: &SynIn<E>, trivia: &TriviaRun) -> bool where E: ErrorSink<usize> {
    !trivia_has_newline(trivia) || continues_after_newline(i, trivia, active_type_continuation_base(i))
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

    fn parse_required_prefix<'source>(
        source: &'source str,
    ) -> (&'source str, Recovered<TypeExpression<'source>>) {
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
        let value = i
            .run(from_fn(|i| Some(parse_required_type_expression_with_outer_missing_role(None, i))))
            .expect("required type expression AST prefix");
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
        parse_direct_mandatory_prefix_with_outer_stop(source, outer_missing_role, None).1
    }

    fn parse_direct_mandatory_prefix_with_outer_stop(
        source: &str,
        outer_missing_role: Option<GrammarRole>,
        stop: Option<StopKind>,
    ) -> (String, Vec<crate::session::CommittedRecoveryRecord>) {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        if let Some(stop) = stop {
            local.push_stop_set(StopSet::default().with(stop));
        }
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
        let remainder = committed.probe(|probe| probe.input().input.remainder().to_owned());
        committed.finish_node();
        let recoveries = committed.into_output().committed_recoveries().to_vec();
        (remainder, recoveries)
    }

    #[test]
    fn active_tail_stops_return_every_outer_boundary_before_type_apply() {
        for (source, stop, remainder) in [
            ("Int = value", StopKind::Equal, " = value"),
            ("Int -> value", StopKind::Arrow, " -> value"),
            ("Int if ready", StopKind::ArmGuardIf, " if ready"),
            ("Int where ready", StopKind::ArmGuardWhere, " where ready"),
            ("Int\nnext", StopKind::Newline, "\nnext"),
        ] {
            let (actual, recoveries) =
                parse_direct_mandatory_prefix_with_outer_stop(source, None, Some(stop));
            assert_eq!(actual, remainder, "{source:?}");
            assert!(recoveries.is_empty(), "{source:?}");
        }
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
        let output = committed.into_output();
        let recoveries = output.committed_recoveries().to_vec();
        let _ = output.finish_complete();
        recoveries
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

    fn parse_direct_prefix(source: &str) -> (String, Vec<crate::session::CommittedRecoveryRecord>) {
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
        commit_direct_type_expression(&mut committed).expect("direct type expression prefix");
        let remainder = committed.probe(|probe| probe.input().input.remainder().to_owned());
        committed.finish_node();
        let recoveries = committed.into_output().committed_recoveries().to_vec();
        (remainder, recoveries)
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
    fn mandatory_type_ast_entry_retries_a_primary_after_malformed_input() {
        let (remainder, value) = parse_required_prefix("@A");
        assert_eq!(remainder, "");
        assert!(matches!(value, Recovered::Complete(TypeExpression {
            primary: TypePrimary::Atom(TypeAtom::Identifier(_)),
            range,
            ..
        }) if range == (1..2)));
    }

    #[test]
    fn ast_type_item_recovery_scans_past_same_line_trivia() {
        let (remainder, mandatory) = parse_required_prefix("@ A");
        assert_eq!(remainder, "");
        assert!(matches!(mandatory, Recovered::Complete(TypeExpression { range, .. }) if range == (2..3)));
        let (remainder, mandatory_direct) =
            parse_direct_mandatory_prefix_with_outer_stop("@ A", None, None);
        assert_eq!(remainder, "");
        assert!(matches!(mandatory_direct.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::Primary)
                && record.kind == RecoveryKind::Error
                && record.site.range == (0..2)));

        assert!(matches!(parse("A ->@ B").arrow, Some(TypeArrowTail {
            rhs: Recovered::Complete(rhs), ..
        }) if rhs.range == (6..7)));
        let arrow_direct = parse_direct_recovered("A ->@ B");
        assert!(matches!(arrow_direct.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::ArrowRhs)
                && record.kind == RecoveryKind::Error
                && record.site.range == (4..6)));

        assert!(matches!(parse("{name: @ A}").primary, TypePrimary::Record(NamedRecordType {
            close: Recovered::Complete(_),
            ref fields,
            ..
        }) if matches!(fields.as_slice(), [Recovered::Complete(TypeRecordField {
            type_expr: Recovered::Complete(type_expr),
            ..
        })] if type_expr.range == (9..10))));
        let record_direct = parse_direct_recovered("{name: @ A}");
        assert!(matches!(record_direct.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::RecordFieldType)
                && record.kind == RecoveryKind::Error
                && record.site.range == (7..9)));

        assert!(matches!(parse("T(@ A)").postfix.as_slice(), [TypePostfixTail::Call(TypeCallTail {
            arguments,
            close: Recovered::Complete(_),
            ..
        })] if matches!(arguments.as_slice(), [Recovered::Complete(TypeExpression { range, .. })] if *range == (4..5))));
        let call_direct = parse_direct_recovered("T(@ A)");
        assert!(matches!(call_direct.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::CallArgument)
                && record.kind == RecoveryKind::Error
                && record.site.range == (2..4)));
    }

    #[test]
    fn mandatory_type_recovery_leaves_an_active_outer_stop_unconsumed() {
        let (remainder, recoveries) = parse_direct_mandatory_prefix_with_outer_stop(
            "@=A",
            None,
            Some(StopKind::Equal),
        );
        assert_eq!(remainder, "=A");
        assert!(matches!(recoveries.as_slice(), [error]
            if error.site.role == GrammarRole::Type(TypeRole::Primary)
                && error.site.range == (0..1)
                && error.kind == crate::session::RecoveryKind::Error));
    }

    #[test]
    fn mandatory_type_recovery_commits_a_malformed_run_before_a_delimiter() {
        let (remainder, recoveries) =
            parse_direct_mandatory_prefix_with_outer_stop("@)", None, None);
        assert_eq!(remainder, ")");
        assert!(matches!(recoveries.as_slice(), [error]
            if error.site.role == GrammarRole::Type(TypeRole::Primary)
                && error.site.range == (0..1)
                && error.kind == crate::session::RecoveryKind::Error));

        let (remainder, recoveries) =
            parse_direct_mandatory_prefix_with_outer_stop("@ )", None, None);
        assert_eq!(remainder, " )");
        assert!(matches!(recoveries.as_slice(), [error]
            if error.site.role == GrammarRole::Type(TypeRole::Primary)
                && error.site.range == (0..1)
                && error.kind == crate::session::RecoveryKind::Error));
        assert_eq!(parse_required_prefix("@ )").0, " )");
    }

    #[test]
    fn mandatory_type_recovery_treats_comments_as_atomic_malformed_trivia() {
        for (source, range) in [("@/*)*/A", 0..6), ("@/*,;*/#A", 0..8)] {
            let (remainder, recoveries) =
                parse_direct_mandatory_prefix_with_outer_stop(source, None, None);
            assert_eq!(remainder, "", "{source}");
            assert!(matches!(recoveries.as_slice(), [error]
                if error.site.role == GrammarRole::Type(TypeRole::Primary)
                    && error.kind == RecoveryKind::Error
                    && error.site.range == range), "{source}: {recoveries:#?}");
            assert_eq!(parse_required_prefix(source).0, "", "AST {source}");
        }

        let (remainder, recoveries) =
            parse_direct_mandatory_prefix_with_outer_stop("@//)\nA", None, None);
        assert_eq!(remainder, "//)\nA");
        assert!(matches!(recoveries.as_slice(), [error]
            if error.site.role == GrammarRole::Type(TypeRole::Primary)
                && error.kind == RecoveryKind::Error
                && error.site.range == (0..1)));
        assert_eq!(parse_required_prefix("@//)\nA").0, "//)\nA");
    }

    #[test]
    fn mandatory_type_recovery_at_eof_emits_one_error() {
        let (remainder, recoveries) =
            parse_direct_mandatory_prefix_with_outer_stop("@", None, None);
        assert_eq!(remainder, "");
        assert!(matches!(recoveries.as_slice(), [error]
            if error.site.role == GrammarRole::Type(TypeRole::Primary)
                && error.site.range == (0..1)
                && error.kind == crate::session::RecoveryKind::Error));
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

        let deeper_call = parse("G T(F\n  A)");
        assert!(matches!(deeper_call.postfix.as_slice(), [TypePostfixTail::Apply(argument)]
            if matches!(argument.argument.postfix.as_slice(), [TypePostfixTail::Call(tail)]
                if tail.arguments.len() == 2)));
        let deeper_call_recoveries = parse_direct_recovered("G T(F\n  A)");
        assert!(matches!(deeper_call_recoveries.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::CallArgumentSeparator)
                && record.site.range == (8..8)
                && record.kind == crate::session::RecoveryKind::Missing), "{deeper_call_recoveries:#?}");

        let deeper_group = parse("G (F\n  A)");
        assert!(matches!(deeper_group.postfix.as_slice(), [TypePostfixTail::Apply(argument)]
            if matches!(argument.argument.primary, TypePrimary::Parenthesized(ParenthesizedTypeGroup {
                ref elements, ..
            }) if elements.len() == 2)));
        let deeper_group_recoveries = parse_direct_recovered("G (F\n  A)");
        assert!(matches!(deeper_group_recoveries.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::ParenthesizedSeparator)
                && record.site.range == (7..7)
                && record.kind == crate::session::RecoveryKind::Missing), "{deeper_group_recoveries:#?}");

        let deeper_effect = parse("G '[F\n  A]");
        assert!(matches!(deeper_effect.postfix.as_slice(), [TypePostfixTail::Apply(argument)]
            if matches!(argument.argument.primary, TypePrimary::EffectRow(EffectRowType {
                ref items, ..
            }) if items.len() == 2)));
        let deeper_effect_recoveries = parse_direct_recovered("G '[F\n  A]");
        assert!(matches!(deeper_effect_recoveries.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::EffectRowSeparator)
                && record.site.range == (8..8)
                && record.kind == crate::session::RecoveryKind::Missing), "{deeper_effect_recoveries:#?}");
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

        let (remainder, boundary) = parse_direct_prefix("T -> @)");
        assert_eq!(remainder, ")");
        assert!(matches!(boundary.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::ArrowRhs)
                && record.kind == RecoveryKind::Error
                && record.site.range == (5..6)));
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
    fn shared_type_delimited_driver_covers_malformed_gaps_and_close_retry() {
        for (source, role) in [
            ("T(@ )", TypeRole::CallArgument),
            ("T(@)", TypeRole::CallArgument),
            ("(@)", TypeRole::ParenthesizedItem),
            ("'[@]", TypeRole::EffectRowItem),
        ] {
            let recoveries = parse_direct_recovered(source);
            assert!(matches!(recoveries.as_slice(), [record]
                if record.site.role == GrammarRole::Type(role)
                    && record.kind == RecoveryKind::Error), "{source}: {recoveries:#?}");
        }
        assert!(matches!(parse("T(@)").postfix.as_slice(), [TypePostfixTail::Call(TypeCallTail {
            arguments, close: Recovered::Complete(_), ..
        })] if matches!(arguments.as_slice(), [Recovered::Incomplete])));
        assert!(matches!(parse("(@)").primary, TypePrimary::Parenthesized(ParenthesizedTypeGroup {
            elements, close: Recovered::Complete(_), ..
        }) if matches!(elements.as_slice(), [Recovered::Incomplete])));
        assert!(matches!(parse("'[@]").primary, TypePrimary::EffectRow(EffectRowType {
            items, close: Recovered::Complete(_), ..
        }) if matches!(items.as_slice(), [Recovered::Incomplete])));

        for (source, role) in [
            ("T(@ , A)", TypeRole::CallArgument),
            ("(@ ; A)", TypeRole::ParenthesizedItem),
            ("'[@ , A]", TypeRole::EffectRowItem),
        ] {
            let recoveries = parse_direct_recovered(source);
            assert!(matches!(recoveries.as_slice(), [record]
                if record.site.role == GrammarRole::Type(role)
                    && record.kind == RecoveryKind::Error), "{source}: {recoveries:#?}");
        }

        for (source, owner) in [
            ("T(])", ConstructRole::TypeCall),
            ("(])", ConstructRole::ParenthesizedTypeGroup),
            ("'[)]", ConstructRole::EffectRowType),
        ] {
            let recoveries = parse_direct_recovered(source);
            assert!(matches!(recoveries.as_slice(), [record]
                if matches!(record.site.role, GrammarRole::ClosingDelimiter { owner: found, .. }
                    if found == owner)
                    && record.kind == RecoveryKind::Error), "{source}: {recoveries:#?}");
        }

        assert!(matches!(parse("T(A])").postfix.as_slice(), [TypePostfixTail::Call(TypeCallTail {
            close: Recovered::Complete(close), ..
        })] if *close == (4..5)));
        let close_retry = parse_direct_recovered("T(A])");
        assert!(matches!(close_retry.as_slice(), [record]
            if matches!(record.site.role, GrammarRole::ClosingDelimiter {
                owner: ConstructRole::TypeCall,
                delimiter: Delimiter::Parenthesis,
            })
                && record.site.range == (3..4)
                && record.kind == RecoveryKind::Error), "{close_retry:#?}");

        let deeper_close = parse("T(for 'a: A\n  )");
        assert!(matches!(deeper_close.postfix.as_slice(), [TypePostfixTail::Call(TypeCallTail {
            close: Recovered::Complete(_), ..
        })]));
        let deeper_mismatch = parse_direct_recovered("T(for 'a: A\n  ])");
        assert!(deeper_mismatch.iter().any(|record| matches!(record.site.role,
            GrammarRole::ClosingDelimiter {
                owner: ConstructRole::TypeCall,
                delimiter: Delimiter::Parenthesis,
            }
        ) && record.kind == RecoveryKind::Error), "{deeper_mismatch:#?}");
    }

    #[test]
    fn malformed_delimited_item_separator_continues_the_same_sequence() {
        for (source, role) in [
            ("T(@, A)", TypeRole::CallArgument),
            ("(@, A)", TypeRole::ParenthesizedItem),
            ("'[@, A]", TypeRole::EffectRowItem),
        ] {
            let recoveries = parse_direct_recovered(source);
            assert!(matches!(recoveries.as_slice(), [record]
                if record.site.role == GrammarRole::Type(role)
                    && record.kind == RecoveryKind::Error), "{source}: {recoveries:#?}");
        }
        assert!(matches!(parse("T(@, A)").postfix.as_slice(), [TypePostfixTail::Call(TypeCallTail {
            arguments, close: Recovered::Complete(_), ..
        })] if matches!(arguments.as_slice(), [Recovered::Incomplete, Recovered::Complete(_)])));
        assert!(matches!(parse("(@, A)").primary, TypePrimary::Parenthesized(ParenthesizedTypeGroup {
            elements, close: Recovered::Complete(_), ..
        }) if matches!(elements.as_slice(), [Recovered::Incomplete, Recovered::Complete(_)])));
        assert!(matches!(parse("'[@, A]").primary, TypePrimary::EffectRow(EffectRowType {
            items, close: Recovered::Complete(_), ..
        }) if matches!(items.as_slice(), [Recovered::Incomplete, Recovered::Complete(_)])));
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
    fn type_close_slot_retries_past_local_trivia() {
        for (source, owner, delimiter, mismatch, close) in [
            ("T(A] )", ConstructRole::TypeCall, Delimiter::Parenthesis, 3..4, 5..6),
            ("(A] )", ConstructRole::ParenthesizedTypeGroup, Delimiter::Parenthesis, 2..3, 4..5),
            ("{a:A] }", ConstructRole::NamedRecordType, Delimiter::Brace, 4..5, 6..7),
            ("'[A) ]", ConstructRole::EffectRowType, Delimiter::Bracket, 3..4, 5..6),
            ("T(A]/*c*/)", ConstructRole::TypeCall, Delimiter::Parenthesis, 3..4, 9..10),
            (":{A] }", ConstructRole::PolymorphicVariantType, Delimiter::Brace, 3..4, 5..6),
        ] {
            let recoveries = parse_direct_recovered(source);
            assert!(recoveries.iter().any(|record| matches!(record.site.role,
                GrammarRole::ClosingDelimiter { owner: found, delimiter: found_delimiter }
                    if found == owner && found_delimiter == delimiter
            ) && record.kind == RecoveryKind::Error && record.site.range == mismatch),
                "missing local mismatch for {source}: {recoveries:#?}");
            assert!(!recoveries.iter().any(|record| matches!(record.site.role,
                GrammarRole::ClosingDelimiter { owner: found, delimiter: found_delimiter }
                    if found == owner && found_delimiter == delimiter
            ) && record.kind == RecoveryKind::Missing),
                "spurious missing close for {source}: {recoveries:#?}");
            let direct = parse_direct(source);
            assert_eq!(direct.to_string(), source, "lossless CST for {source}");
            let matching_kind = match delimiter {
                Delimiter::Parenthesis => SyntaxKind::RParen,
                Delimiter::Bracket => SyntaxKind::RBracket,
                Delimiter::Brace => SyntaxKind::RBrace,
            };
            assert!(direct.descendants_with_tokens().filter_map(|element| element.into_token()).any(|token| {
                let range = token.text_range();
                token.kind() == matching_kind
                    && (u32::from(range.start()) as usize..u32::from(range.end()) as usize) == close
            }), "missing {matching_kind:?} token at {close:?} for {source}");
        }

        assert!(matches!(parse("T(A] )").postfix.as_slice(), [TypePostfixTail::Call(TypeCallTail {
            close: Recovered::Complete(close), ..
        })] if *close == (5..6)));
        assert!(matches!(parse("(A] )").primary, TypePrimary::Parenthesized(ParenthesizedTypeGroup {
            close: Recovered::Complete(close), ..
        }) if close == (4..5)));
        assert!(matches!(parse("{a:A] }").primary, TypePrimary::Record(NamedRecordType {
            close: Recovered::Complete(close), ..
        }) if close == (6..7)));
        assert!(matches!(parse("'[A) ]").primary, TypePrimary::EffectRow(EffectRowType {
            close: Recovered::Complete(close), ..
        }) if close == (5..6)));
        assert!(matches!(parse("T(A]/*c*/)").postfix.as_slice(), [TypePostfixTail::Call(TypeCallTail {
            close: Recovered::Complete(close), ..
        })] if *close == (9..10)));
        assert!(matches!(parse(":{A] }").primary, TypePrimary::PolymorphicVariant(PolymorphicVariantType {
            close: Recovered::Complete(close), ..
        }) if close == (5..6)));
    }

    #[test]
    fn type_close_slot_leaves_caller_owned_newlines_unconsumed() {
        let (remainder, call) = parse_prefix_with_outer_stop("T(A]\n)", StopKind::Newline);
        assert_eq!(remainder, "\n)");
        assert!(matches!(call.postfix.as_slice(), [TypePostfixTail::Call(TypeCallTail {
            close: Recovered::Incomplete, ..
        })]));
        let (remainder, call_recoveries) =
            parse_direct_prefix_with_outer_stop("T(A]\n)", StopKind::Newline);
        assert_eq!(remainder, "\n)");
        assert!(call_recoveries.iter().any(|record| matches!(record.site.role,
            GrammarRole::ClosingDelimiter {
                owner: ConstructRole::TypeCall,
                delimiter: Delimiter::Parenthesis,
            }
        ) && record.kind == RecoveryKind::Error && record.site.range == (3..4)));
        assert!(call_recoveries.iter().any(|record| matches!(record.site.role,
            GrammarRole::ClosingDelimiter {
                owner: ConstructRole::TypeCall,
                delimiter: Delimiter::Parenthesis,
            }
        ) && record.kind == RecoveryKind::Missing && record.site.range == (4..4)));

        let (remainder, variant) = parse_prefix_with_outer_stop(":{A]\n}", StopKind::Newline);
        assert_eq!(remainder, "\n}");
        assert!(matches!(variant.primary, TypePrimary::PolymorphicVariant(PolymorphicVariantType {
            close: Recovered::Incomplete, ..
        })));
        let (remainder, variant_recoveries) =
            parse_direct_prefix_with_outer_stop(":{A]\n}", StopKind::Newline);
        assert_eq!(remainder, "\n}");
        assert!(variant_recoveries.iter().any(|record| matches!(record.site.role,
            GrammarRole::ClosingDelimiter {
                owner: ConstructRole::PolymorphicVariantType,
                delimiter: Delimiter::Brace,
            }
        ) && record.kind == RecoveryKind::Error && record.site.range == (3..4)));
        assert!(variant_recoveries.iter().any(|record| matches!(record.site.role,
            GrammarRole::ClosingDelimiter {
                owner: ConstructRole::PolymorphicVariantType,
                delimiter: Delimiter::Brace,
            }
        ) && record.kind == RecoveryKind::Missing && record.site.range == (4..4)));
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
    fn comment_prefixed_path_and_record_colon_recovery_keep_their_boundaries() {
        for (source, expected_remainder, expected_range) in [
            ("A::@\nT", "\nT", 3..4),
            ("A::@//x\nT", "//x\nT", 3..4),
            ("A::@ B", "", 3..4),
            ("A::@/*x*/ B", "", 3..9),
        ] {
            let (ast_remainder, ast) = parse_prefix(source);
            let (direct_remainder, recoveries) = parse_direct_prefix(source);
            assert_eq!(ast_remainder, expected_remainder, "AST {source}");
            assert_eq!(direct_remainder, expected_remainder, "direct {source}");
            assert!(matches!(ast.postfix.first(), Some(TypePostfixTail::Path(TypePathTail {
                segment: Recovered::Incomplete, ..
            }))), "AST shape {source}");
            assert!(matches!(recoveries.as_slice(), [error]
                if error.site.role == GrammarRole::Type(TypeRole::PathSegment)
                    && error.kind == RecoveryKind::Error
                    && error.site.range == expected_range), "{source}: {recoveries:#?}");
        }

        for (source, expected_range) in [
            ("{name @ A}", 6..7),
            ("{name @/*x*/ A}", 6..12),
        ] {
            let (ast_remainder, _) = parse_prefix(source);
            let (direct_remainder, recoveries) = parse_direct_prefix(source);
            assert_eq!(ast_remainder, "A}", "AST {source}");
            assert_eq!(direct_remainder, "A}", "direct {source}");
            assert!(recoveries.iter().any(|error|
                error.site.role == GrammarRole::Type(TypeRole::RecordFieldColon)
                    && error.kind == RecoveryKind::Error
                    && error.site.range == expected_range), "{source}: {recoveries:#?}");
        }
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
    fn named_record_malformed_field_boundary_does_not_cascade() {
        for source in ["{@", "{@ "] {
            let recoveries = parse_direct_recovered(source);
            assert!(recoveries.iter().any(|record|
                record.site.role == GrammarRole::Type(TypeRole::RecordField)
                    && record.kind == RecoveryKind::Error), "{source}: {recoveries:#?}");
            assert!(!recoveries.iter().any(|record|
                record.site.role == GrammarRole::Type(TypeRole::RecordField)
                    && record.kind == RecoveryKind::Missing), "{source}: {recoveries:#?}");
        }

        let separator = parse_direct_recovered("{@,}");
        assert!(matches!(separator.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::RecordField)
                && record.kind == RecoveryKind::Error), "{separator:#?}");
        assert!(matches!(parse("{@,}").primary, TypePrimary::Record(NamedRecordType {
            fields, close: Recovered::Complete(_), ..
        }) if matches!(fields.as_slice(), [Recovered::Incomplete])));

        let continued = parse_direct_recovered("{@, a: A}");
        assert!(matches!(continued.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::RecordField)
                && record.kind == RecoveryKind::Error), "{continued:#?}");
        assert!(matches!(parse("{@, a: A}").primary, TypePrimary::Record(NamedRecordType {
            fields, close: Recovered::Complete(_), ..
        }) if matches!(fields.as_slice(), [Recovered::Incomplete, Recovered::Complete(_)])));

        let outer_close = parse_direct_recovered("'[{@]");
        assert!(outer_close.iter().any(|record|
            record.site.role == GrammarRole::Type(TypeRole::RecordField)
                && record.kind == RecoveryKind::Error
                && record.site.range == (3..4)), "{outer_close:#?}");
        assert!(outer_close.iter().any(|record| matches!(record.site.role,
            GrammarRole::ClosingDelimiter {
                owner: ConstructRole::NamedRecordType,
                delimiter: Delimiter::Brace,
            }
        ) && record.kind == RecoveryKind::Missing && record.site.range == (4..4)), "{outer_close:#?}");
        assert!(!outer_close.iter().any(|record| matches!(record.site.role,
            GrammarRole::ClosingDelimiter {
                owner: ConstructRole::EffectRowType,
                delimiter: Delimiter::Bracket,
            }
        )), "{outer_close:#?}");
        assert!(matches!(parse("'[{@]").primary, TypePrimary::EffectRow(EffectRowType {
            close: Recovered::Complete(_),
            items,
            ..
        }) if matches!(items.as_slice(), [Recovered::Complete(TypeExpression {
            primary: TypePrimary::Record(NamedRecordType { close: Recovered::Incomplete, .. }), ..
        })])));

        let field_colon_outer_close = parse_direct_recovered("'[{name @]");
        assert!(field_colon_outer_close.iter().any(|record|
            record.site.role == GrammarRole::Type(TypeRole::RecordFieldColon)
                && record.kind == RecoveryKind::Error
                && record.site.range == (8..9)), "{field_colon_outer_close:#?}");
        assert!(!field_colon_outer_close.iter().any(|record| matches!(record.site.role,
            GrammarRole::ClosingDelimiter {
                owner: ConstructRole::EffectRowType,
                delimiter: Delimiter::Bracket,
            }
        )), "{field_colon_outer_close:#?}");
    }

    #[test]
    fn named_record_invalid_run_leaves_boundary_trivia_unclaimed() {
        let nested = parse_direct_recovered("'[{@ }]");
        assert!(matches!(nested.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::RecordField)
                && record.kind == RecoveryKind::Error
                && record.site.range == (3..4)), "{nested:#?}");
        assert!(matches!(parse("'[{@ }]").primary, TypePrimary::EffectRow(EffectRowType {
            close: Recovered::Complete(_),
            items,
            ..
        }) if matches!(items.as_slice(), [Recovered::Complete(TypeExpression {
            primary: TypePrimary::Record(NamedRecordType {
                fields, close: Recovered::Complete(_), ..
            }), ..
        })] if matches!(fields.as_slice(), [Recovered::Incomplete]))));

        let separator = parse_direct_recovered("{@ , a: A}");
        assert!(matches!(separator.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::RecordField)
                && record.kind == RecoveryKind::Error
                && record.site.range == (1..2)), "{separator:#?}");
        assert!(matches!(parse("{@ , a: A}").primary, TypePrimary::Record(NamedRecordType {
            fields, close: Recovered::Complete(_), ..
        }) if matches!(fields.as_slice(), [Recovered::Incomplete, Recovered::Complete(_)])));
    }

    #[test]
    fn named_record_malformed_runs_leave_local_closes_for_the_close_slot() {
        let mismatch = parse_direct_recovered("{@]}");
        assert!(mismatch.iter().any(|record|
            record.site.role == GrammarRole::Type(TypeRole::RecordField)
                && record.kind == RecoveryKind::Error
                && record.site.range == (1..2)), "{mismatch:#?}");
        assert!(mismatch.iter().any(|record| matches!(record.site.role,
            GrammarRole::ClosingDelimiter {
                owner: ConstructRole::NamedRecordType,
                delimiter: Delimiter::Brace,
            }
        ) && record.kind == RecoveryKind::Error && record.site.range == (2..3)), "{mismatch:#?}");
        assert!(matches!(parse("{@]}").primary, TypePrimary::Record(NamedRecordType {
            fields, close: Recovered::Complete(close), ..
        }) if matches!(fields.as_slice(), [Recovered::Incomplete]) && close == (3..4)));

        let semicolon = parse_direct_recovered("{@;}");
        assert!(matches!(semicolon.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::RecordField)
                && record.kind == RecoveryKind::Error
                && record.site.range == (1..3)), "{semicolon:#?}");
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

        let boundary = parse_direct_recovered("{name: @}");
        assert!(matches!(boundary.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::RecordFieldType)
                && record.kind == RecoveryKind::Error
                && record.site.range == (7..8)));

        let recovered_ast = parse("{name: @A}");
        assert!(matches!(recovered_ast.primary, TypePrimary::Record(NamedRecordType {
            close: Recovered::Complete(_),
            ref fields,
            ..
        }) if matches!(fields.as_slice(), [Recovered::Complete(TypeRecordField {
            type_expr: Recovered::Complete(type_expr),
            ..
        })] if type_expr.range == (8..9))));

        let recovered_colon_ast = parse("{name @: A}");
        assert!(matches!(recovered_colon_ast.primary, TypePrimary::Record(NamedRecordType {
            fields, close: Recovered::Complete(_), ..
        }) if matches!(fields.as_slice(), [Recovered::Complete(TypeRecordField {
            colon: Recovered::Complete(_), type_expr: Recovered::Complete(_), ..
        })])));

        let (ast_remainder, ast) = parse_prefix("{name @ A}");
        let (direct_remainder, direct) = parse_direct_prefix("{name @ A}");
        assert_eq!(ast_remainder, direct_remainder);
        assert_eq!(ast_remainder, "A}");
        assert!(direct.iter().any(|record|
            record.site.role == GrammarRole::Type(TypeRole::RecordFieldColon)
                && record.kind == RecoveryKind::Error));
        assert!(matches!(ast.primary, TypePrimary::Record(NamedRecordType { fields, .. })
            if matches!(fields.as_slice(), [Recovered::Complete(TypeRecordField {
                colon: Recovered::Incomplete, type_expr: Recovered::Incomplete, ..
            })])));
    }

    #[test]
    fn malformed_record_colon_leaves_outer_newlines_for_the_field_sequence() {
        for source in ["{name @\nA}", "{name @//x\nA}"] {
            assert!(matches!(parse(source).primary, TypePrimary::Record(NamedRecordType {
                fields, close: Recovered::Complete(_), ..
            }) if matches!(fields.as_slice(), [
                Recovered::Complete(TypeRecordField { colon: Recovered::Incomplete, .. }),
                Recovered::Complete(_),
            ])), "AST {source}");

            let (remainder, recoveries) = parse_direct_prefix(source);
            assert_eq!(remainder, "", "direct remainder {source}");
            assert!(!recoveries.iter().any(|record| matches!(record.site.role,
                GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::NamedRecordType,
                    delimiter: Delimiter::Brace,
                }
            ) && record.kind == RecoveryKind::Missing), "{source}: {recoveries:#?}");
            let direct = parse_direct(source);
            assert_eq!(direct.descendants()
                .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
                .count(), 2, "direct fields {source}");
        }

        let continuation = parse("{name @:\n  A}");
        assert!(matches!(continuation.primary, TypePrimary::Record(NamedRecordType {
            fields, close: Recovered::Complete(_), ..
        }) if matches!(fields.as_slice(), [Recovered::Complete(TypeRecordField {
            colon: Recovered::Complete(_), type_expr: Recovered::Complete(_), ..
        })])));
        let continuation_direct = parse_direct("{name @:\n  A}");
        assert_eq!(continuation_direct.descendants()
            .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
            .count(), 1);
    }

    #[test]
    fn named_record_field_colon_uses_one_chain_gap_policy_on_both_paths() {
        let after_colon = parse("{name:\nA: B}");
        assert!(matches!(after_colon.primary, TypePrimary::Record(NamedRecordType {
            fields, close: Recovered::Complete(_), ..
        }) if matches!(fields.as_slice(), [
            Recovered::Complete(TypeRecordField { type_expr: Recovered::Incomplete, .. }),
            Recovered::Complete(TypeRecordField { type_expr: Recovered::Complete(_), .. }),
        ])));
        assert_eq!(parse_direct("{name:\nA: B}").descendants()
            .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
            .count(), 2);

        let before_colon = parse("{name\nA: B}");
        assert!(matches!(before_colon.primary, TypePrimary::Record(NamedRecordType {
            fields, close: Recovered::Complete(_), ..
        }) if matches!(fields.as_slice(), [
            Recovered::Complete(TypeRecordField { colon: Recovered::Incomplete, type_expr: Recovered::Incomplete, .. }),
            Recovered::Complete(TypeRecordField { colon: Recovered::Complete(_), type_expr: Recovered::Complete(_), .. }),
        ])));
        assert_eq!(parse_direct("{name\nA: B}").descendants()
            .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
            .count(), 2);

        let same_position = parse("{a A}");
        assert!(matches!(same_position.primary, TypePrimary::Record(NamedRecordType {
            fields, close: Recovered::Complete(_), ..
        }) if matches!(fields.as_slice(), [Recovered::Complete(TypeRecordField {
            colon: Recovered::Incomplete, type_expr: Recovered::Complete(_), ..
        })])));
        let recoveries = parse_direct_recovered("{a A}");
        assert!(matches!(recoveries.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::RecordFieldColon)
                && record.kind == RecoveryKind::Missing
                && record.site.range == (3..3)), "{recoveries:#?}");
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
    fn named_record_sequence_classifies_recovery_gaps_before_consuming_them() {
        let newline = parse("{@\nA: B}");
        assert!(matches!(newline.primary, TypePrimary::Record(NamedRecordType {
            fields, close: Recovered::Complete(_), ..
        }) if matches!(fields.as_slice(), [Recovered::Incomplete, Recovered::Complete(_)])));
        let newline_recoveries = parse_direct_recovered("{@\nA: B}");
        assert!(matches!(newline_recoveries.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::RecordField)
                && record.kind == RecoveryKind::Error
                && record.site.range == (1..2)), "{newline_recoveries:#?}");

        let entry_mismatch = parse_direct_recovered("{]}");
        assert!(matches!(entry_mismatch.as_slice(), [record]
            if matches!(record.site.role, GrammarRole::ClosingDelimiter {
                owner: ConstructRole::NamedRecordType,
                delimiter: Delimiter::Brace,
            }) && record.kind == RecoveryKind::Error && record.site.range == (1..2)), "{entry_mismatch:#?}");
        assert!(matches!(parse("{]}").primary, TypePrimary::Record(NamedRecordType {
            fields, close: Recovered::Complete(close), ..
        }) if fields.is_empty() && close == (2..3)));

        let semicolon = parse("{a: A; \nB: C}");
        assert!(matches!(semicolon.primary, TypePrimary::Record(NamedRecordType {
            fields, close: Recovered::Complete(_), ..
        }) if matches!(fields.as_slice(), [Recovered::Complete(_), Recovered::Complete(_)])));
        let semicolon_recoveries = parse_direct_recovered("{a: A; \nB: C}");
        assert!(matches!(semicolon_recoveries.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::RecordFieldSeparator)
                && record.kind == RecoveryKind::Error
                && record.site.range == (5..6)), "{semicolon_recoveries:#?}");
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

        for (source, role, range) in [
            ("for @", TypeRole::ForallBinder, 4..5),
            ("for 'a @", TypeRole::ForallColon, 7..8),
            ("for 'a: @", TypeRole::ForallBody, 8..9),
        ] {
            let recoveries = parse_direct_recovered(source);
            assert_eq!(recoveries.len(), 1, "{source}: {recoveries:#?}");
            let record = &recoveries[0];
            assert_eq!(record.site.role, GrammarRole::Type(role), "{source}: {record:#?}");
            assert_eq!(record.kind, RecoveryKind::Error, "{source}: {record:#?}");
            assert_eq!(record.site.range, range, "{source}: {record:#?}");
        }
        let malformed = parse_direct_recovered("for 'a: @T");
        assert!(malformed.iter().any(|record| record.site.role == GrammarRole::Type(TypeRole::ForallBody)
            && record.kind == RecoveryKind::Error && record.site.range == (8..9)), "{malformed:#?}");

        let (trailing_remainder, trailing_trivia) = parse_direct_prefix("for 'a: @ ");
        assert_eq!(trailing_remainder, " ");
        assert!(matches!(trailing_trivia.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::ForallBody)
                && record.kind == RecoveryKind::Error), "{trailing_trivia:#?}");

        let colon_retry = parse_direct_recovered("for 'a @T");
        assert!(matches!(colon_retry.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::ForallColon)
                && record.kind == RecoveryKind::Error), "{colon_retry:#?}");
        assert!(matches!(parse("for 'a @T").primary, TypePrimary::Forall(ForallType {
            colon: Recovered::Incomplete, body: Recovered::Complete(_), ..
        })));

        let first_binder = parse_direct_recovered("for @T");
        assert!(matches!(first_binder.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::ForallBinder)
                && record.kind == RecoveryKind::Error
                && record.site.range == (4..6)), "{first_binder:#?}");

        let (newline_remainder, _) = parse_prefix("for 'a: @\nT");
        assert_eq!(newline_remainder, "\nT");
        let (newline_remainder, newline_recoveries) = parse_direct_prefix("for 'a: @\nT");
        assert_eq!(newline_remainder, "\nT");
        assert!(matches!(newline_recoveries.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::ForallBody)
                && record.kind == RecoveryKind::Error
                && record.site.range == (8..9)), "{newline_recoveries:#?}");

        for (source, expected_remainder) in [
            ("for 'a: @ \nT", " \nT"),
            ("for 'a: @ //x\nT", " //x\nT"),
        ] {
            let (ast_remainder, _) = parse_prefix(source);
            let (direct_remainder, recoveries) = parse_direct_prefix(source);
            assert_eq!(ast_remainder, direct_remainder, "AST/direct remainder: {source}");
            assert_eq!(direct_remainder, expected_remainder, "{source}");
            assert!(matches!(recoveries.as_slice(), [record]
                if record.site.role == GrammarRole::Type(TypeRole::ForallBody)
                    && record.kind == RecoveryKind::Error
                    && record.site.range == (8..9)), "{source}: {recoveries:#?}");
        }

        let binder_trivia = parse_direct_recovered("for @ 'a: T");
        assert!(matches!(binder_trivia.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::ForallBinder)
                && record.kind == RecoveryKind::Error
                && record.site.range == (4..5)), "{binder_trivia:#?}");
        assert!(matches!(parse("for @ 'a: T").primary, TypePrimary::Forall(ForallType {
            binders, colon: Recovered::Complete(_), body: Recovered::Complete(_), ..
        }) if matches!(binders.as_slice(), [Recovered::Incomplete, Recovered::Complete(_)])));

        let recovered_colon = parse_direct_recovered("for @ : T");
        assert!(matches!(recovered_colon.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::ForallBinder)
                && record.kind == RecoveryKind::Error
                && record.site.range == (4..5)), "{recovered_colon:#?}");
        assert!(matches!(parse("for @ : T").primary, TypePrimary::Forall(ForallType {
            binders, colon: Recovered::Complete(_), body: Recovered::Complete(_), ..
        }) if matches!(binders.as_slice(), [Recovered::Incomplete])));

        assert!(matches!(parse("for 'a: @ T").primary, TypePrimary::Forall(ForallType {
            colon: Recovered::Complete(_), body: Recovered::Complete(_), ..
        })));

        let first_separator = parse_direct_recovered("for , 'a: T");
        assert!(matches!(first_separator.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::ForallBinder)
                && record.kind == RecoveryKind::Error
                && record.site.range == (4..5)), "{first_separator:#?}");
        assert!(matches!(parse("for , 'a: T").primary, TypePrimary::Forall(ForallType {
            binders, colon: Recovered::Complete(_), body: Recovered::Complete(_), ..
        }) if matches!(binders.as_slice(), [Recovered::Incomplete, Recovered::Complete(_)])));

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
        assert!(!mismatch.iter().any(|record| matches!(record.site.role, GrammarRole::ClosingDelimiter {
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

    #[test]
    fn polymorphic_variant_outer_judge_preserves_owner_boundaries_and_reentry_order() {
        let (remainder, caller_semicolon) = parse_prefix_with_outer_stop(":{A;", StopKind::Semicolon);
        assert_eq!(remainder, ";");
        assert!(matches!(caller_semicolon.primary, TypePrimary::PolymorphicVariant(PolymorphicVariantType {
            close: Recovered::Incomplete, ref tags, ..
        }) if tags.len() == 1));
        let (remainder, records) = parse_direct_prefix_with_outer_stop(":{A;", StopKind::Semicolon);
        assert_eq!(remainder, ";");
        assert!(!records.iter().any(|record| record.site.role == GrammarRole::Type(TypeRole::PolymorphicVariantTagSeparator)));

        let (remainder, caller_close) = parse_prefix_with_outer_stop(":{A )", StopKind::RightParenthesis);
        assert_eq!(remainder, " )");
        assert!(matches!(caller_close.primary, TypePrimary::PolymorphicVariant(PolymorphicVariantType {
            close: Recovered::Incomplete, ref tags, ..
        }) if tags.len() == 1));
        let (remainder, _) = parse_direct_prefix_with_outer_stop(":{A )", StopKind::RightParenthesis);
        assert_eq!(remainder, " )");

        let (remainder, required_tag) = parse_prefix_with_outer_stop(":{A, )", StopKind::RightParenthesis);
        assert_eq!(remainder, " )");
        assert!(matches!(required_tag.primary, TypePrimary::PolymorphicVariant(PolymorphicVariantType {
            close: Recovered::Incomplete, tags, ..
        }) if matches!(tags.as_slice(), [Recovered::Complete(_), Recovered::Incomplete])));
        let (remainder, records) = parse_direct_prefix_with_outer_stop(":{A, )", StopKind::RightParenthesis);
        assert_eq!(remainder, " )");
        assert_eq!(records.iter().filter(|record|
            record.site.role == GrammarRole::Type(TypeRole::PolymorphicVariantTag)
                && record.kind == RecoveryKind::Missing).count(), 1);

        let (remainder, left_brace) = parse_prefix_with_outer_stop(":{A {", StopKind::LeftBrace);
        assert_eq!(remainder, " {");
        assert!(matches!(left_brace.primary, TypePrimary::PolymorphicVariant(PolymorphicVariantType {
            close: Recovered::Incomplete, ..
        })));
        let (remainder, _) = parse_direct_prefix_with_outer_stop(":{A {", StopKind::LeftBrace);
        assert_eq!(remainder, " {");
        let (remainder, with) = parse_prefix_with_outer_stop(":{A with", StopKind::With);
        assert_eq!(remainder, " with");
        assert!(matches!(with.primary, TypePrimary::PolymorphicVariant(PolymorphicVariantType {
            close: Recovered::Incomplete, ..
        })));
        let (remainder, _) = parse_direct_prefix_with_outer_stop(":{A with", StopKind::With);
        assert_eq!(remainder, " with");

        for source in [":{A;B}", ":{A ; B}"] {
            let parsed = parse(source);
            assert!(matches!(parsed.primary, TypePrimary::PolymorphicVariant(PolymorphicVariantType { ref tags, .. }) if tags.len() == 2));
            let records = parse_direct_recovered(source);
            assert_eq!(records.iter().filter(|record|
                record.site.role == GrammarRole::Type(TypeRole::PolymorphicVariantTagSeparator)
                    && record.kind == RecoveryKind::Error).count(), 1);
        }

        let mismatch = parse_direct_recovered(":{A ]}");
        assert!(mismatch.iter().any(|record| matches!(record.site.role, GrammarRole::ClosingDelimiter {
            owner: ConstructRole::PolymorphicVariantType,
            delimiter: Delimiter::Brace,
        }) && record.kind == RecoveryKind::Error && record.site.range == (4..5)));
        assert!(matches!(parse(":{A ]}").primary, TypePrimary::PolymorphicVariant(PolymorphicVariantType {
            tags, close: Recovered::Complete(close), ..
        }) if tags.len() == 1 && close == (5..6)));
    }

    #[test]
    fn polymorphic_variant_never_consumes_a_deeper_outer_newline() {
        for (source, expected_incomplete_tags, expected_missing_records) in [
            (":{A,\n  B}", 1, 1),
            (":{@\n  B}", 1, 0),
        ] {
            let (remainder, value) = parse_prefix(source);
            assert_eq!(remainder, "\n  B}", "AST leaves the deep newline for {source:?}");
            assert_eq!(match value.primary {
                TypePrimary::PolymorphicVariant(PolymorphicVariantType {
                    close: Recovered::Incomplete,
                    tags,
                    ..
                }) => tags.iter()
                    .filter(|tag| matches!(tag, Recovered::Incomplete)).count(),
                _ => unreachable!(),
            }, expected_incomplete_tags);
            let (remainder, records) = parse_direct_prefix(source);
            assert_eq!(remainder, "\n  B}", "direct CST leaves the deep newline for {source:?}");
            assert_eq!(records.iter().filter(|record|
                record.site.role == GrammarRole::Type(TypeRole::PolymorphicVariantTag)
                    && record.kind == RecoveryKind::Missing).count(), expected_missing_records);
        }
    }

    #[test]
    fn polymorphic_variant_retries_malformed_tag_and_payload_slots_in_place() {
        for source in [":{@123}", ":{@123 Int}"] {
            let parsed = parse(source);
            let TypePrimary::PolymorphicVariant(PolymorphicVariantType { tags, .. }) = parsed.primary else {
                panic!("expected polymorphic variant");
            };
            let [Recovered::Complete(PolymorphicVariantTag { name: Recovered::Incomplete, payloads, .. })] = tags.as_slice() else {
                panic!("expected one recovered tag");
            };
            assert_eq!(payloads.len(), usize::from(source == ":{@123 Int}"));
            let records = parse_direct_recovered(source);
            assert_eq!(records.iter().filter(|record|
                record.site.role == GrammarRole::Type(TypeRole::PolymorphicVariantTag)
                    && record.kind == RecoveryKind::Error).count(), 1);
            assert_eq!(records.iter().filter(|record|
                record.site.role == GrammarRole::Type(TypeRole::PolymorphicVariantTagName)
                    && record.kind == RecoveryKind::Error).count(), 1);
        }

        let direct = parse_direct(":{@123}");
        let tags = direct.descendants()
            .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
            .collect::<Vec<_>>();
        assert_eq!(tags.len(), 1);
        assert_eq!(tags[0].descendants().filter(|node| node.kind() == SyntaxKind::Error).count(), 2);

        let parsed = parse(":{A@123}");
        assert!(matches!(parsed.primary, TypePrimary::PolymorphicVariant(PolymorphicVariantType { ref tags, .. })
            if matches!(tags.as_slice(), [Recovered::Complete(PolymorphicVariantTag { payloads, .. })]
                if matches!(payloads.as_slice(), [Recovered::Complete(PolymorphicVariantPayload {
                    boundary: Recovered::Incomplete,
                    type_expr: Recovered::Complete(_),
                    ..
                })]))));
        let records = parse_direct_recovered(":{A@123}");
        assert!(records.iter().any(|record|
            record.site.role == GrammarRole::Type(TypeRole::PolymorphicVariantPayloadBoundary)
                && record.kind == RecoveryKind::Error
                && record.site.range == (3..4)));

        let trailing = parse_direct_recovered(":{,");
        assert_eq!(trailing.iter().filter(|record|
            record.site.role == GrammarRole::Type(TypeRole::PolymorphicVariantTag)
                && record.kind == RecoveryKind::Missing).count(), 1);
    }

    #[test]
    fn polymorphic_variant_nt6_and_malformed_scanners_use_canonical_primaries() {
        let forall = parse(":{for 'a: T}");
        assert!(matches!(forall.primary, TypePrimary::PolymorphicVariant(PolymorphicVariantType {
            tags, ..
        }) if matches!(tags.as_slice(), [Recovered::Complete(PolymorphicVariantTag {
            name: Recovered::Incomplete,
            payloads,
            range,
        })] if payloads.is_empty() && range == &(2..11))));
        let records = parse_direct_recovered(":{for 'a: T}");
        assert!(matches!(records.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::PolymorphicVariantTagName)
                && record.kind == RecoveryKind::Error
                && record.site.range == (2..11)));

        let malformed_tag = parse(":{@ 123}");
        assert!(matches!(malformed_tag.primary, TypePrimary::PolymorphicVariant(PolymorphicVariantType {
            tags, ..
        }) if matches!(tags.as_slice(), [Recovered::Complete(PolymorphicVariantTag {
            name: Recovered::Incomplete,
            payloads,
            ..
        })] if payloads.is_empty())));
        let records = parse_direct_recovered(":{@ 123}");
        assert_eq!(records.iter().filter(|record|
            record.site.role == GrammarRole::Type(TypeRole::PolymorphicVariantTag)
                && record.kind == RecoveryKind::Error).count(), 1);
        assert_eq!(records.iter().filter(|record|
            record.site.role == GrammarRole::Type(TypeRole::PolymorphicVariantTagName)
                && record.kind == RecoveryKind::Error).count(), 1);
        let direct = parse_direct(":{@ 123}");
        assert_eq!(direct.descendants().filter(|node| node.kind() == SyntaxKind::PolymorphicVariantTag).count(), 1);

        let malformed_payload = parse(":{A @ 123}");
        assert!(matches!(malformed_payload.primary, TypePrimary::PolymorphicVariant(PolymorphicVariantType { ref tags, .. })
            if matches!(tags.as_slice(), [Recovered::Complete(PolymorphicVariantTag { payloads, .. })]
                if matches!(payloads.as_slice(), [Recovered::Complete(PolymorphicVariantPayload {
                    boundary: Recovered::Complete(_),
                    type_expr: Recovered::Complete(_),
                    ..
                })]))));
        let records = parse_direct_recovered(":{A @ 123}");
        assert!(records.iter().any(|record|
            record.site.role == GrammarRole::Type(TypeRole::PolymorphicVariantPayload)
                && record.kind == RecoveryKind::Error
                && record.site.range == (4..6)));
        let direct = parse_direct(":{A @ 123}");
        assert_eq!(direct.descendants().filter(|node| node.kind() == SyntaxKind::PolymorphicVariantPayload).count(), 1);
    }

    #[test]
    fn polymorphic_variant_malformed_scanner_preserves_outer_gaps_and_comment_atomicity() {
        let (remainder, _) = parse_prefix_with_outer_stop(":{@ )", StopKind::RightParenthesis);
        assert_eq!(remainder, " )");
        let (remainder, records) = parse_direct_prefix_with_outer_stop(":{@ )", StopKind::RightParenthesis);
        assert_eq!(remainder, " )");
        assert!(records.iter().any(|record|
            record.site.role == GrammarRole::Type(TypeRole::PolymorphicVariantTag)
                && record.kind == RecoveryKind::Error
                && record.site.range == (2..3)));

        let (remainder, _) = parse_prefix_with_outer_stop(":{A @ )", StopKind::RightParenthesis);
        assert_eq!(remainder, " )");
        let (remainder, records) = parse_direct_prefix_with_outer_stop(":{A @ )", StopKind::RightParenthesis);
        assert_eq!(remainder, " )");
        assert!(records.iter().any(|record|
            record.site.role == GrammarRole::Type(TypeRole::PolymorphicVariantPayload)
                && record.kind == RecoveryKind::Error
                && record.site.range == (4..5)));

        let block = parse_direct_recovered(":{@ /*x*/ 123}");
        assert!(block.iter().any(|record|
            record.site.role == GrammarRole::Type(TypeRole::PolymorphicVariantTag)
                && record.kind == RecoveryKind::Error
                && record.site.range == (2..10)));
        assert!(block.iter().any(|record|
            record.site.role == GrammarRole::Type(TypeRole::PolymorphicVariantTagName)
                && record.kind == RecoveryKind::Error
                && record.site.range == (10..13)));

        let payload_block = parse_direct_recovered(":{A @ /*x*/ 123}");
        assert!(payload_block.iter().any(|record|
            record.site.role == GrammarRole::Type(TypeRole::PolymorphicVariantPayload)
                && record.kind == RecoveryKind::Error
                && record.site.range == (4..12)));

        let line = parse_direct_recovered(":{@ //x\n123}");
        assert!(line.iter().any(|record|
            record.site.role == GrammarRole::Type(TypeRole::PolymorphicVariantTag)
                && record.kind == RecoveryKind::Error
                && record.site.range == (2..3)));
        assert!(line.iter().any(|record|
            record.site.role == GrammarRole::Type(TypeRole::PolymorphicVariantTagName)
                && record.kind == RecoveryKind::Error
                && record.site.range == (8..11)));
    }

    #[test]
    fn polymorphic_variant_shared_driver_regression_matrix() {
        for source in [
            ":{A Int, B}",
            ":{A Int Bool}",
            ":{A;B}",
            ":{A ; B}",
            ":{123}",
            ":{123 Int}",
            ":{A Pair(Int, Bool) B}",
            ":{@123}",
            ":{@123 Int}",
            ":{for 'a: T}",
            ":{A@,B}",
            ":{]}",
            ":{:{A} B}",
            ":{A ]}",
            ":{@ /*x*/ 123}",
        ] {
            let parsed = parse(source);
            assert!(matches!(parsed.primary, TypePrimary::PolymorphicVariant(_)), "{source}");
            assert_eq!(parse_direct(source).to_string(), source, "{source}");
        }

        let (remainder, newline) = parse_prefix(":{A Int\n B}");
        assert_eq!(remainder, "\n B}");
        assert!(matches!(newline.primary, TypePrimary::PolymorphicVariant(PolymorphicVariantType {
            ref tags, close: Recovered::Incomplete, ..
        }) if tags.len() == 1));
        let (remainder, _) = parse_direct_prefix(":{A Int\n B}");
        assert_eq!(remainder, "\n B}");
        let nested = parse(":{:{A} B}");
        assert!(matches!(nested.primary, TypePrimary::PolymorphicVariant(PolymorphicVariantType {
            tags, ..
        }) if matches!(tags.as_slice(), [Recovered::Complete(PolymorphicVariantTag {
            name: Recovered::Incomplete,
            payloads,
            ..
        })] if payloads.len() == 1)));

        let (remainder, _) = parse_prefix(":{@\n  B}");
        assert_eq!(remainder, "\n  B}");
        let (remainder, _) = parse_direct_prefix(":{@\n  B}");
        assert_eq!(remainder, "\n  B}");

        let (remainder, comma_eof) = parse_prefix(":{,");
        assert_eq!(remainder, "");
        assert!(matches!(comma_eof.primary, TypePrimary::PolymorphicVariant(
            PolymorphicVariantType { close: Recovered::Incomplete, .. }
        )));

        for (source, stop, expected) in [
            (":{A;", StopKind::Semicolon, ";"),
            (":{A ;", StopKind::Semicolon, " ;"),
            (":{A)", StopKind::RightParenthesis, ")"),
            (":{A )", StopKind::RightParenthesis, " )"),
            (":{A{", StopKind::LeftBrace, "{"),
            (":{A {", StopKind::LeftBrace, " {"),
            (":{with", StopKind::With, "with"),
            (":{A with", StopKind::With, " with"),
        ] {
            assert_eq!(parse_prefix_with_outer_stop(source, stop).0, expected, "AST {source}");
            assert_eq!(
                parse_direct_prefix_with_outer_stop(source, stop).0,
                expected,
                "direct {source}",
            );
        }

        for source in [":{@ )}", ":{A @ )}"] {
            let (remainder, _) = parse_prefix_with_outer_stop(source, StopKind::RightParenthesis);
            assert!(remainder.starts_with(" )}"), "{source}: {remainder:?}");
            let (remainder, _) = parse_direct_prefix_with_outer_stop(source, StopKind::RightParenthesis);
            assert!(remainder.starts_with(" )}"), "{source}: {remainder:?}");
        }

        for source in [":{A  ", ":{@  "] {
            assert_eq!(parse_prefix(source).0, "  ", "AST {source:?}");
            assert_eq!(parse_direct_prefix(source).0, "  ", "direct {source:?}");
        }
    }

    #[test]
    fn polymorphic_variant_active_operator_stops_require_the_whole_spelling() {
        for (source, stop) in [
            (":{A => B}", StopKind::Equal),
            (":{A =+ B}", StopKind::Equal),
            (":{A ->= B}", StopKind::Arrow),
        ] {
            let (remainder, parsed) = parse_prefix_with_outer_stop(source, stop);
            assert_eq!(remainder, "", "AST {source}");
            assert!(matches!(parsed.primary, TypePrimary::PolymorphicVariant(
                PolymorphicVariantType { close: Recovered::Complete(_), .. }
            )));

            let (remainder, records) = parse_direct_prefix_with_outer_stop(source, stop);
            assert_eq!(remainder, "", "direct {source}");
            assert!(records.iter().any(|record|
                record.site.role == GrammarRole::Type(TypeRole::PolymorphicVariantPayload)
                    && record.kind == RecoveryKind::Error),
                "{source}: {records:#?}");
        }
    }

}
