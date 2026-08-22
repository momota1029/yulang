//! Minimal expression grammar shared by declaration values and Pratt parsing.

use std::{marker::PhantomData, ops::Range, sync::Arc};

use chasa::{
    Back as _, ErrorSink, Input as _,
    error::std::{Unexpected, UnexpectedEndOfInput},
    parser::Parser,
    prelude::{from_fn, many_skip, one_of},
};

use crate::{
    grammar::declaration::Recovered,
    grammar::pattern::{Pattern, parse_direct_pattern, parse_pattern, pattern_nud_candidate_input},
    operator::OperatorTable,
    scan::{
        operator::{LeadingTrivia, OperatorSite, ScannedFixity, ScannedOperator, scan_operator},
        punctuation::{PunctuationKind, scan_punctuation},
        trivia::{TriviaRun, scan_trivia},
        word::{WordSpan, scan_path_segment, scan_word},
    },
    session::{
        BracedStatementBlockRole, ColonApplicationRole, CommitOutput, Committed, CommittedRecoveryRecord, ConstructRole, Delimiter,
        ExpressionDelimitedOwner,
        CaseLikeRole, ExpectationSources, ExpectedSyntax, ExpressionRole, GrammarRole, IfExpressionRole, IndentationBaseline,
        IndentationBaselineKind, Probe, RecoveryKind,
        LayoutDelimitedBoundary, LayoutDelimitedFrame, RecoverySiteKey, StopKind, StopSet, SynIn, SyntaxExpectation, UnexpectedCategory,
        UnexpectedSyntax,
    },
    syntax_kind::SyntaxKind,
};

/// A precedence-neutral source-order dynamic operator chain.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct OperatorChain<'source> {
    items: Vec<OperatorChainItem<'source>>,
    range: Range<usize>,
}

impl<'source> OperatorChain<'source> {
    fn new(items: Vec<OperatorChainItem<'source>>, range: Range<usize>) -> Self {
        Self { items, range }
    }

    pub(crate) fn items(&self) -> &[OperatorChainItem<'source>] {
        &self.items
    }

    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum OperatorChainItem<'source> {
    PrefixUse(OperatorUse<'source>),
    Primary(PrimaryExpression<'source>),
    NullfixUse(OperatorUse<'source>),
    InfixUse(OperatorUse<'source>),
    SuffixUse(OperatorUse<'source>),
    FixedPostfix(FixedPostfixTail<'source>),
    MlArgument {
        argument: Box<OperatorChain<'source>>,
        range: Range<usize>,
    },
    TerminalOuter(TerminalOuterTail<'source>),
    MissingOperand { range: Range<usize> },
    Error { range: Range<usize> },
}

/// A fixed-spelling postfix continuation.  These remain flat source-order
/// items beside dynamic operator uses; they never become target-owned nodes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum FixedPostfixTail<'source> {
    Call(CallTail<'source>),
    Index(IndexTail<'source>),
    Field(FieldTail<'source>),
    Projection(ProjectionTail<'source>),
    Path(PathTail<'source>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CallTail<'source> {
    open: Range<usize>,
    arguments: Vec<OperatorChain<'source>>,
    close: Recovered<Range<usize>>,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct IndexTail<'source> {
    open: Range<usize>,
    items: Vec<OperatorChain<'source>>,
    close: Recovered<Range<usize>>,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ProjectionTail<'source> {
    Tuple(ProjectionTupleTail<'source>),
    Record(ProjectionRecordTail<'source>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ProjectionTupleTail<'source> {
    dot: Range<usize>,
    open: Range<usize>,
    items: Vec<OperatorChain<'source>>,
    close: Recovered<Range<usize>>,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ProjectionRecordTail<'source> {
    dot: Range<usize>,
    open: Range<usize>,
    items: Vec<ProjectionRecordItem<'source>>,
    close: Recovered<Range<usize>>,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ProjectionRecordItem<'source> {
    Expression(OperatorChain<'source>),
    Spread(ProjectionRecordSpreadItem<'source>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ProjectionRecordSpreadItem<'source> {
    marker: Range<usize>,
    rhs: Recovered<Box<OperatorChain<'source>>>,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct FieldTail<'source> {
    dot: Range<usize>,
    name: Recovered<WordSpan<'source>>,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct PathTail<'source> {
    separator: Range<usize>,
    segment: Recovered<PathSegment<'source>>,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum PathSegment<'source> {
    Identifier(WordSpan<'source>),
    SigilIdentifier(WordSpan<'source>),
}

/// A terminal structural continuation that is associated only after the
/// preceding source-order dynamic operator segment has been reduced.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum TerminalOuterTail<'source> {
    ColonApplication(ColonApplicationTail<'source>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ColonApplicationTail<'source> {
    colon: Range<usize>,
    rhs: Recovered<ColonApplicationRhs<'source>>,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ColonApplicationRhs<'source> {
    Inline {
        arguments: Vec<Recovered<OperatorChain<'source>>>,
    },
    Indented {
        block: IndentedStatementBlock<'source>,
    },
}

/// The currently-supported statement subset for an indented colon RHS.
/// Declaration statements remain root-owned until their colon-body grammar is
/// specified separately.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Statement<'source> {
    expression: OperatorChain<'source>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct IndentedStatementBlock<'source> {
    base_indent: usize,
    block_indent: usize,
    statements: Vec<Recovered<Statement<'source>>>,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct BracedStatementBlockExpression<'source> {
    open: Range<usize>,
    statements: Vec<Recovered<Statement<'source>>>,
    close: Recovered<Range<usize>>,
    range: Range<usize>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum OperatorRole {
    Prefix,
    Infix,
    Suffix,
    Nullfix,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct OperatorUse<'source> {
    text: &'source str,
    range: Range<usize>,
    role: OperatorRole,
}

impl<'source> OperatorUse<'source> {
    pub(crate) fn text(&self) -> &'source str { self.text }
    pub(crate) fn range(&self) -> Range<usize> { self.range.clone() }
    pub(crate) fn role(&self) -> OperatorRole { self.role }
}

/// A primary expression; dynamic operator structure lives in [`OperatorChain`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum PrimaryExpression<'source> {
    Identifier(WordSpan<'source>),
    Integer(IntegerLiteral<'source>),
    Parenthesized {
        elements: Vec<OperatorChain<'source>>,
        trailing_comma: Option<Range<usize>>,
        range: Range<usize>,
    },
    If(IfExpression<'source>),
    Case(CaseExpression<'source>),
    Catch(CatchExpression<'source>),
    BracedStatementBlock(BracedStatementBlockExpression<'source>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct IfExpression<'source> {
    arms: Vec<IfArm<'source>>,
    else_arm: Option<ElseArm<'source>>,
    base_indent: usize,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct IfArm<'source> {
    keyword: IfArmKeyword<'source>,
    condition: Recovered<OperatorChain<'source>>,
    body: Recovered<ColonIntroducedArmBody<'source>>,
    range: Range<usize>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum IfArmKeyword<'source> {
    If(WordSpan<'source>),
    Elsif(WordSpan<'source>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ElseArm<'source> {
    keyword: WordSpan<'source>,
    body: Recovered<ElseArmBody<'source>>,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ElseArmBody<'source> {
    Colon(ColonIntroducedArmBody<'source>),
    Bare(Box<OperatorChain<'source>>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ColonIntroducedArmBody<'source> {
    colon: Recovered<Range<usize>>,
    rhs: Recovered<ArmBodyRhs<'source>>,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ArmBodyRhs<'source> {
    Inline(Box<OperatorChain<'source>>),
    Indented(IndentedStatementBlock<'source>),
}

pub(crate) type Expression<'source> = PrimaryExpression<'source>;

impl PrimaryExpression<'_> {
    pub(crate) fn range(&self) -> Range<usize> {
        match self {
            Self::Identifier(identifier) => identifier.range(),
            Self::Integer(integer) => integer.range(),
            Self::Parenthesized { range, .. } => range.clone(),
            Self::If(if_expression) => if_expression.range.clone(),
            Self::Case(expression) => expression.range.clone(),
            Self::Catch(expression) => expression.range.clone(),
            Self::BracedStatementBlock(block) => block.range.clone(),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CaseLikeFamily { Case, Catch }

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ArmSequencePolicy {
    CaseInline,
    CatchInlineSingle,
    Indented { family: CaseLikeFamily, base_indent: usize, arm_indent: usize },
    CatchBraced,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CaseLikeLabel<'source> { text: &'source str, range: Range<usize> }
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CaseExpression<'source> { keyword: WordSpan<'source>, label: Option<CaseLikeLabel<'source>>, scrutinee: Recovered<Box<OperatorChain<'source>>>, block: Recovered<CaseBlock<'source>>, base_indent: usize, range: Range<usize> }
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CatchExpression<'source> { keyword: WordSpan<'source>, label: Option<CaseLikeLabel<'source>>, scrutinee: Recovered<Box<OperatorChain<'source>>>, block: Recovered<CatchBlock<'source>>, base_indent: usize, range: Range<usize> }
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CaseBlock<'source> { colon: Recovered<Range<usize>>, arms: Recovered<ArmSequence<CaseArm<'source>>>, layout: ColonArmLayout, range: Range<usize> }
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum CatchBlock<'source> { Colon { colon: Recovered<Range<usize>>, arms: Recovered<ArmSequence<CatchArm<'source>>>, layout: ColonArmLayout, range: Range<usize> }, Braced { open: Range<usize>, arms: Recovered<ArmSequence<CatchArm<'source>>>, close: Recovered<Range<usize>>, range: Range<usize> } }
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ColonArmLayout { Inline, Indented { base_indent: usize, arm_indent: usize } }
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ArmSequence<A> { arms: Vec<Recovered<A>>, trailing_comma: Option<Range<usize>> }
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CaseArm<'source> { pattern: Recovered<Pattern<'source>>, guard: Option<Recovered<CaseGuard<'source>>>, arrow: Recovered<Range<usize>>, body: Recovered<ArmBody<'source>>, terminator: Option<Range<usize>>, range: Range<usize> }
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CatchArm<'source> { pattern: Recovered<Pattern<'source>>, handler: Option<Recovered<Pattern<'source>>>, guard: Option<Recovered<CatchGuard<'source>>>, arrow: Recovered<Range<usize>>, body: Recovered<ArmBody<'source>>, terminator: Option<Range<usize>>, range: Range<usize> }
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CaseGuard<'source> { keyword: ArmGuardKeyword<'source>, condition: Recovered<Box<OperatorChain<'source>>>, range: Range<usize> }
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CatchGuard<'source> { keyword: ArmGuardKeyword<'source>, condition: Recovered<Box<OperatorChain<'source>>>, range: Range<usize> }
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ArmGuardKeyword<'source> { If(WordSpan<'source>), Where(WordSpan<'source>) }
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ArmBody<'source> { Inline(Box<OperatorChain<'source>>), Indented(IndentedStatementBlock<'source>) }


/// The source extent of one decimal integer literal.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct IntegerLiteral<'source> {
    text: &'source str,
    start: usize,
    end: usize,
}

impl<'source> IntegerLiteral<'source> {
    pub(crate) fn text(self) -> &'source str {
        self.text
    }

    pub(crate) fn range(self) -> Range<usize> {
        self.start..self.end
    }
}

/// Parses an identifier or decimal integer expression without operators.
pub(crate) fn parse_expression<'source, E>(
    i: SynIn<'_, 'source, '_, E>,
) -> Option<Expression<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_atom(i)
}

/// Parses an expression with site-aware dynamic operator resolution.
pub(crate) fn parse_expression_with_operators<'source, E>(
    table: &OperatorTable,
    i: SynIn<'_, 'source, '_, E>,
) -> Option<OperatorChain<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_operator_chain(table, i)
}

/// Minimal metadata retained by the direct flat-chain continuation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ParsedExpression<C> {
    range: Range<usize>,
    marker: PhantomData<C>,
}

impl<C> ParsedExpression<C> {
    fn new(range: Range<usize>) -> Self {
        Self { range, marker: PhantomData }
    }

    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
}

/// Parses one expression into a committed direct-CST output.
///
/// The caller owns and has already emitted any trivia preceding the expression
/// start. `leading` preserves that trivia's effect on NUD operator judgement;
/// no leading trivia is scanned or emitted here.
pub(crate) fn parse_direct_expression_with_operators<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    leading: LeadingTrivia,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<ParsedExpression<O::Checkpoint>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_direct_operator_chain(table, leading, committed)
}

fn parse_operator_chain<'source, E>(
    table: &OperatorTable,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<OperatorChain<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let mut items = Vec::new();
    let mut leading = leading_trivia(&consume_trivia(&mut i)?);
    loop {
        let nud = i.run(from_fn(|i| recognize_nud(table, leading, i)))?;
        match nud {
            NudRecognition::Prefix(operator) => {
                items.push(OperatorChainItem::PrefixUse(operator_use(&operator, OperatorRole::Prefix)));
                leading = LeadingTrivia::None;
            }
            NudRecognition::Parenthesized { open } => {
                i.cut();
                let incoming_base = i.local.indentation_baseline().map_or(0, |baseline| baseline.column);
                push_parenthesized_expression_scope(&mut i);
                let opening_trivia = consume_trivia(&mut i).expect("trivia scanning is total");
                let layout = LayoutDelimitedFrame::after_opening_trivia(
                    incoming_base,
                    &opening_trivia,
                    i.local.line().line_indent,
                );
                push_layout_delimited_baseline(layout, &mut i);
                let mut elements = Vec::new();
                let mut trailing_comma = None;
                let close = if let Some(close) = i.run(recognize_parenthesized_close) {
                    close
                } else {
                    loop {
                        elements.push(i.run(from_fn(|i| parse_operator_chain(table, i)))?);
                        let trivia = consume_trivia(&mut i).expect("trivia scanning is total");
                        if let Some(comma) = i.run(recognize_parenthesized_comma) {
                            consume_trivia(&mut i).expect("trivia scanning is total");
                            if let Some(close) = i.run(recognize_parenthesized_close) {
                                trailing_comma = Some(comma);
                                break close;
                            }
                            continue;
                        }
                        if let Some(close) = i.run(recognize_parenthesized_close) {
                            break close;
                        }
                        match layout.boundary_after_trivia(&trivia, i.local.line().line_indent) {
                            LayoutDelimitedBoundary::ImplicitNewline => continue,
                            LayoutDelimitedBoundary::DeeperNewline => break i.run(recognize_parenthesized_close)?,
                            LayoutDelimitedBoundary::None if expression_nud_candidate_input(table, &mut i) => continue,
                            LayoutDelimitedBoundary::None => break i.run(recognize_parenthesized_close)?,
                        }
                    }
                };
                pop_layout_delimited_baseline(layout, &mut i);
                pop_parenthesized_expression_scope(&mut i);
                items.push(OperatorChainItem::Primary(PrimaryExpression::Parenthesized {
                    elements, trailing_comma, range: open.start..close.end,
                }));
                break;
            }
            NudRecognition::BracedStatementBlock { open } => {
                i.cut();
                items.push(OperatorChainItem::Primary(PrimaryExpression::BracedStatementBlock(
                    parse_braced_statement_block_expression(table, open, &mut i),
                )));
                break;
            }
            NudRecognition::If { keyword, base_indent } => {
                i.cut();
                items.push(OperatorChainItem::Primary(PrimaryExpression::If(
                    parse_if_expression(table, keyword, base_indent, &mut i),
                )));
                break;
            }
            NudRecognition::Case { keyword, base_indent } => {
                i.cut();
                items.push(OperatorChainItem::Primary(PrimaryExpression::Case(
                    parse_case_expression(table, keyword, base_indent, &mut i),
                )));
                break;
            }
            NudRecognition::Catch { keyword, base_indent } => {
                i.cut();
                items.push(OperatorChainItem::Primary(PrimaryExpression::Catch(
                    parse_catch_expression(table, keyword, base_indent, &mut i),
                )));
                break;
            }
            NudRecognition::Identifier(identifier) => {
                items.push(OperatorChainItem::Primary(PrimaryExpression::Identifier(identifier)));
                break;
            }
            NudRecognition::Integer(integer) => {
                items.push(OperatorChainItem::Primary(PrimaryExpression::Integer(integer)));
                break;
            }
            NudRecognition::Nullfix(operator) => {
                items.push(OperatorChainItem::NullfixUse(operator_use(&operator, OperatorRole::Nullfix)));
                break;
            }
        }
    }

    loop {
        if let Some(tail) = i.run(from_fn(|i| recognize_led(table, i)))? {
            match tail {
                LedRecognition::Infix { operator, .. } => {
                    i.cut();
                    items.push(OperatorChainItem::InfixUse(operator_use(&operator, OperatorRole::Infix)));
                    items.extend(i.run(from_fn(|i| parse_operator_chain_operand(table, i)))?);
                }
                LedRecognition::Suffix { operator, .. } => {
                    items.push(OperatorChainItem::SuffixUse(operator_use(&operator, OperatorRole::Suffix)));
                }
            }
            continue;
        }

        if let Some(tail) = i.run(recognize_fixed_postfix) {
            i.cut();
            items.push(OperatorChainItem::FixedPostfix(parse_fixed_postfix_tail(table, tail, &mut i)));
            continue;
        }

        if let Some(_separator) = i.run(from_fn(|i| recognize_ml_argument(table, i))) {
            i.cut();
            let previous = i.local.ml_arg();
            i.local.set_ml_arg(true);
            let argument = i.run(from_fn(|i| parse_operator_chain(table, i)))
                .or_else(|| parse_dangling_prefix_ast(table, &mut i));
            i.local.set_ml_arg(previous);
            let argument = argument?;
            let range = argument.range();
            items.push(OperatorChainItem::MlArgument { argument: Box::new(argument), range });
            continue;
        }

        if let Some(colon) = i.run(recognize_colon_application_tail) {
            i.cut();
            let colon_start = colon.colon.start;
            let (rhs, end) = match colon.rhs {
                ColonApplicationRhsRecognition::WrongIndent => {
                    (Recovered::Incomplete, colon.colon.end)
                }
                ColonApplicationRhsRecognition::Inline { .. } => {
                    let outer_owns_sequence = outer_owns_inline_argument_sequence(&i);
                    let arguments = if outer_owns_sequence {
                        vec![Recovered::Complete(i.run(from_fn(|i| parse_operator_chain(table, i)))?)]
                    } else {
                        let stop_set = active_stop_set(&i).with(StopKind::Comma);
                        i.local.push_stop_set(stop_set);
                        let arguments = parse_inline_colon_arguments(table, &mut i);
                        assert_eq!(i.local.pop_stop_set(), Some(stop_set));
                        arguments?
                    };
                    let end = arguments
                        .last()
                        .and_then(|argument| match argument {
                            Recovered::Complete(chain) => Some(chain.range.end),
                            Recovered::Incomplete => None,
                        })
                        .unwrap_or(colon.colon.end);
                    (
                        Recovered::Complete(ColonApplicationRhs::Inline { arguments }),
                        end,
                    )
                }
                ColonApplicationRhsRecognition::Indented {
                    opening_trivia,
                    base_indent,
                    block_indent,
                } => {
                    let block = parse_indented_statement_block(
                        table,
                        opening_trivia,
                        base_indent,
                        block_indent,
                        &mut i,
                    );
                    let end = block.range.end;
                    (
                        Recovered::Complete(ColonApplicationRhs::Indented { block }),
                        end,
                    )
                }
            };
            items.push(OperatorChainItem::TerminalOuter(TerminalOuterTail::ColonApplication(
                ColonApplicationTail {
                    colon: colon.colon,
                    rhs,
                    range: colon_start..end,
                },
            )));
            break;
        }
        break;
    }
    let end = items.last().map_or(start, operator_chain_item_end);
    Some(OperatorChain::new(items, start..end))
}

fn parse_operator_chain_operand<'source, E>(
    table: &OperatorTable,
    i: SynIn<'_, 'source, '_, E>,
) -> Option<Vec<OperatorChainItem<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    Some(parse_operator_chain(table, i)?.items)
}

fn operator_chain_item_end(item: &OperatorChainItem<'_>) -> usize {
    match item {
        OperatorChainItem::PrefixUse(operator) | OperatorChainItem::NullfixUse(operator)
        | OperatorChainItem::InfixUse(operator) | OperatorChainItem::SuffixUse(operator) => operator.range.end,
        OperatorChainItem::Primary(primary) => primary.range().end,
        OperatorChainItem::FixedPostfix(FixedPostfixTail::Call(tail)) => tail.range.end,
        OperatorChainItem::FixedPostfix(FixedPostfixTail::Index(tail)) => tail.range.end,
        OperatorChainItem::FixedPostfix(FixedPostfixTail::Projection(ProjectionTail::Tuple(tail))) => tail.range.end,
        OperatorChainItem::FixedPostfix(FixedPostfixTail::Projection(ProjectionTail::Record(tail))) => tail.range.end,
        OperatorChainItem::FixedPostfix(FixedPostfixTail::Field(tail)) => tail.range.end,
        OperatorChainItem::FixedPostfix(FixedPostfixTail::Path(tail)) => tail.range.end,
        OperatorChainItem::MlArgument { range, .. } => range.end,
        OperatorChainItem::TerminalOuter(TerminalOuterTail::ColonApplication(tail)) => tail.range.end,
        OperatorChainItem::MissingOperand { range } | OperatorChainItem::Error { range } => range.end,
    }
}

fn operator_use<'source>(operator: &ScannedOperator<'source>, role: OperatorRole) -> OperatorUse<'source> {
    OperatorUse { text: operator.text(), range: operator.range(), role }
}

/// Sink-free NUD result shared by AST tests and the direct continuation.
#[derive(Clone, Debug, Eq, PartialEq)]
enum NudRecognition<'source> {
    Parenthesized { open: Range<usize> },
    BracedStatementBlock { open: Range<usize> },
    If { keyword: WordSpan<'source>, base_indent: usize },
    Case { keyword: WordSpan<'source>, base_indent: usize },
    Catch { keyword: WordSpan<'source>, base_indent: usize },
    Identifier(WordSpan<'source>),
    Integer(IntegerLiteral<'source>),
    Prefix(ScannedOperator<'source>),
    Nullfix(ScannedOperator<'source>),
}

/// Sink-free LED result shared by AST tests and the direct continuation.
#[derive(Clone, Debug, Eq, PartialEq)]
enum LedRecognition<'source> {
    Infix {
        leading: TriviaRun,
        operator: ScannedOperator<'source>,
    },
    Suffix {
        leading: TriviaRun,
        operator: ScannedOperator<'source>,
    },
}

/// A recognized fixed continuation.  Call and ML application deliberately do
/// not participate until their follow-up slice; this judge covers only the
/// already-authoritative field and path forms.
#[derive(Clone, Debug, Eq, PartialEq)]
enum FixedPostfixRecognition {
    Call { open: Range<usize> },
    Index { open: Range<usize> },
    ProjectionTuple { leading: TriviaRun, dot: Range<usize>, open: Range<usize> },
    ProjectionRecord { leading: TriviaRun, dot: Range<usize>, open: Range<usize> },
    Field { leading: TriviaRun, dot: Range<usize> },
    Path { leading: TriviaRun, separator: Range<usize> },
}

fn recognize_fixed_postfix<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<FixedPostfixRecognition>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let leading = consume_trivia(&mut i)?;
    if !trivia_continues_chain(&leading, &i) {
        i.rollback(checkpoint);
        return None;
    }
    let Some(punctuation) = i.run(scan_punctuation) else {
        i.rollback(checkpoint);
        return None;
    };
    match punctuation.kind() {
        PunctuationKind::Open(Delimiter::Parenthesis) if leading.is_empty() => {
            Some(FixedPostfixRecognition::Call { open: punctuation.range() })
        }
        PunctuationKind::Open(Delimiter::Bracket) if leading.is_empty() => {
            Some(FixedPostfixRecognition::Index { open: punctuation.range() })
        }
        PunctuationKind::Dot if matches!(i.input.remainder().chars().next(), Some('(')) => {
            let open = i.input.next()?;
            Some(FixedPostfixRecognition::ProjectionTuple { leading, dot: punctuation.range(), open: (i.pos() - open.len_utf8())..i.pos() })
        }
        PunctuationKind::Dot if matches!(i.input.remainder().chars().next(), Some('{')) => {
            let open = i.input.next()?;
            Some(FixedPostfixRecognition::ProjectionRecord { leading, dot: punctuation.range(), open: (i.pos() - open.len_utf8())..i.pos() })
        }
        PunctuationKind::Dot => {
            Some(FixedPostfixRecognition::Field { leading, dot: punctuation.range() })
        }
        PunctuationKind::ColonColon => {
            Some(FixedPostfixRecognition::Path { leading, separator: punctuation.range() })
        }
        _ => {
            i.rollback(checkpoint);
            None
        }
    }
}

fn recognize_ml_argument<'source, E>(
    table: &OperatorTable,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<TriviaRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if i.local.ml_arg() || !ml_argument_context_allows(&i) {
        return None;
    }
    let checkpoint = i.checkpoint();
    let trivia = consume_trivia(&mut i)?;
    if trivia.is_empty() || !trivia_continues_chain(&trivia, &i)
        || !ml_argument_candidate_input(table, &mut i)
    {
        i.rollback(checkpoint);
        return None;
    }
    Some(trivia)
}

fn ml_argument_candidate_input<E>(table: &OperatorTable, i: &mut SynIn<E>) -> bool
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    expression_nud_candidate_input(table, i) || dangling_prefix_candidate_input(table, i)
}

fn dangling_prefix_candidate_input<E>(table: &OperatorTable, i: &mut SynIn<E>) -> bool
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let remainder = i.input.remainder();
    let entry = table.entries_with_sites().map(|(entry, _)| entry)
        .filter(|entry| remainder.starts_with(entry.spelling()))
        .max_by_key(|entry| entry.spelling().len())
        .filter(|entry| entry.fixities().prefix().is_some() && !entry.fixities().is_nullfix());
    let accepted = entry.is_some_and(|entry| {
        for _ in entry.spelling().chars() { if i.input.next().is_none() { return false; } }
        let _ = consume_trivia(i);
        i.input.remainder().is_empty() || matches!(i.input.remainder().chars().next(), Some(')' | ']' | '}' | ',' | ';' | ':'))
    });
    i.rollback(checkpoint);
    accepted
}

fn parse_dangling_prefix_ast<'source, E>(table: &OperatorTable, i: &mut SynIn<'_, 'source, '_, E>) -> Option<OperatorChain<'source>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    dangling_prefix_candidate_input(table, i).then_some(())?;
    let start = i.pos();
    let remainder = i.input.remainder();
    let entry = table.entries_with_sites().map(|(entry, _)| entry)
        .filter(|entry| remainder.starts_with(entry.spelling()))
        .max_by_key(|entry| entry.spelling().len())?;
    for _ in entry.spelling().chars() { i.input.next()?; }
    let end = i.pos();
    consume_trivia(i)?;
    let missing_at = i.pos();
    Some(OperatorChain::new(vec![
        OperatorChainItem::PrefixUse(OperatorUse { text: &i.input.source()[start..end], range: start..end, role: OperatorRole::Prefix }),
        OperatorChainItem::MissingOperand { range: missing_at..missing_at },
    ], start..end))
}

fn ml_argument_context_allows<E>(i: &SynIn<E>) -> bool
where E: ErrorSink<usize>,
{
    i.local.expression_delimited_owner().is_some()
        || (i.local.delimiter().is_none() && active_stop_set(i) == StopSet::default())
}

fn parse_fixed_postfix_tail<'source, E>(
    table: &OperatorTable,
    tail: FixedPostfixRecognition,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> FixedPostfixTail<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    match tail {
        FixedPostfixRecognition::Call { open } => FixedPostfixTail::Call(parse_call_tail(table, open, i)),
        FixedPostfixRecognition::Index { open } => FixedPostfixTail::Index(parse_index_tail(table, open, i)),
        FixedPostfixRecognition::ProjectionTuple { dot, open, .. } => {
            FixedPostfixTail::Projection(ProjectionTail::Tuple(parse_projection_tuple_tail(table, dot, open, i)))
        }
        FixedPostfixRecognition::ProjectionRecord { dot, open, .. } => {
            FixedPostfixTail::Projection(ProjectionTail::Record(parse_projection_record_tail(table, dot, open, i)))
        }
        FixedPostfixRecognition::Field { dot, .. } => {
            let name = if let Some(name) = i.run(scan_word) {
                Recovered::Complete(name)
            } else {
                let _ = consume_fixed_tail_invalid_run(table, i);
                Recovered::Incomplete
            };
            FixedPostfixTail::Field(FieldTail {
                dot: dot.clone(),
                name,
                range: dot.start..i.pos(),
            })
        }
        FixedPostfixRecognition::Path { separator, .. } => {
            consume_trivia(i).expect("trivia scanning is total");
            let segment = if let Some(segment) = i.run(scan_path_segment) {
                Recovered::Complete(path_segment(segment))
            } else {
                let _ = consume_fixed_tail_invalid_run(table, i);
                Recovered::Incomplete
            };
            FixedPostfixTail::Path(PathTail {
                separator: separator.clone(),
                segment,
                range: separator.start..i.pos(),
            })
        }
    }
}

fn parse_call_tail<'source, E>(
    table: &OperatorTable,
    open: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> CallTail<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let incoming_base = i.local.indentation_baseline().map_or(0, |baseline| baseline.column);
    i.local.push_delimiter(Delimiter::Parenthesis);
    let stops = active_stop_set(i).with(StopKind::Comma).with(StopKind::Semicolon).with(StopKind::RightParenthesis);
    i.local.push_stop_set(stops);
    i.local.push_expression_delimited_owner(ExpressionDelimitedOwner::Call);
    let opening = consume_trivia(i).expect("trivia scanning is total");
    let layout = LayoutDelimitedFrame::after_opening_trivia(incoming_base, &opening, i.local.line().line_indent);
    push_layout_delimited_baseline(layout, i);
    let mut arguments = Vec::new();
    let close = if let Some(close) = i.run(recognize_parenthesized_close) {
        Recovered::Complete(close)
    } else {
        loop {
            if let Some(argument) = i.run(from_fn(|i| parse_operator_chain(table, i))) {
                arguments.push(argument);
            } else {
                if let Some(range) = call_argument_error_retry_ast(table, i) {
                    arguments.push(OperatorChain::new(
                        vec![OperatorChainItem::Error { range: range.clone() }],
                        range,
                    ));
                    continue;
                }
                let at = i.pos();
                if let Some(_) = i.run(recognize_call_separator) {
                    arguments.push(OperatorChain::new(
                        vec![OperatorChainItem::MissingOperand { range: at..at }],
                        at..at,
                    ));
                    consume_trivia(i).expect("trivia scanning is total");
                    if let Some(close) = i.run(recognize_parenthesized_close) { break Recovered::Complete(close); }
                    continue;
                }
                break Recovered::Incomplete;
            }
            let trivia = consume_trivia(i).expect("trivia scanning is total");
            if let Some(_) = i.run(recognize_call_separator) {
                consume_trivia(i).expect("trivia scanning is total");
                if let Some(close) = i.run(recognize_parenthesized_close) { break Recovered::Complete(close); }
                continue;
            }
            if let Some(close) = i.run(recognize_parenthesized_close) { break Recovered::Complete(close); }
            if layout.boundary_after_trivia(&trivia, i.local.line().line_indent) == LayoutDelimitedBoundary::ImplicitNewline {
                continue;
            }
            break Recovered::Incomplete;
        }
    };
    pop_layout_delimited_baseline(layout, i);
    assert_eq!(
        i.local.pop_expression_delimited_owner(),
        Some(ExpressionDelimitedOwner::Call)
    );
    assert_eq!(i.local.pop_stop_set(), Some(stops));
    assert_eq!(i.local.pop_delimiter(), Some(Delimiter::Parenthesis));
    CallTail { open: open.clone(), arguments, close, range: open.start..i.pos() }
}

fn parse_index_tail<'source, E>(
    table: &OperatorTable,
    open: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> IndexTail<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let incoming_base = i.local.indentation_baseline().map_or(0, |baseline| baseline.column);
    i.local.push_delimiter(Delimiter::Bracket);
    let stops = active_stop_set(i).with(StopKind::Comma).with(StopKind::Semicolon).with(StopKind::RightBracket);
    i.local.push_stop_set(stops);
    i.local.push_expression_delimited_owner(ExpressionDelimitedOwner::Index);
    let opening = consume_trivia(i).expect("trivia scanning is total");
    let layout = LayoutDelimitedFrame::after_opening_trivia(incoming_base, &opening, i.local.line().line_indent);
    push_layout_delimited_baseline(layout, i);
    let mut items = Vec::new();
    let close = if let Some(close) = i.run(recognize_index_close) {
        Recovered::Complete(close)
    } else {
        loop {
            if let Some(item) = i.run(from_fn(|i| parse_operator_chain(table, i))) {
                items.push(item);
            } else {
                if let Some(range) = call_argument_error_retry_ast(table, i) {
                    items.push(OperatorChain::new(
                        vec![OperatorChainItem::Error { range: range.clone() }],
                        range,
                    ));
                    continue;
                }
                let at = i.pos();
                if i.run(recognize_call_separator).is_some() {
                    items.push(OperatorChain::new(
                        vec![OperatorChainItem::MissingOperand { range: at..at }],
                        at..at,
                    ));
                    consume_trivia(i).expect("trivia scanning is total");
                    if let Some(close) = i.run(recognize_index_close) { break Recovered::Complete(close); }
                    continue;
                }
                break Recovered::Incomplete;
            }
            let trivia = consume_trivia(i).expect("trivia scanning is total");
            if i.run(recognize_call_separator).is_some() {
                consume_trivia(i).expect("trivia scanning is total");
                if let Some(close) = i.run(recognize_index_close) { break Recovered::Complete(close); }
                continue;
            }
            if let Some(close) = i.run(recognize_index_close) { break Recovered::Complete(close); }
            if layout.boundary_after_trivia(&trivia, i.local.line().line_indent) == LayoutDelimitedBoundary::ImplicitNewline {
                continue;
            }
            break Recovered::Incomplete;
        }
    };
    pop_layout_delimited_baseline(layout, i);
    assert_eq!(
        i.local.pop_expression_delimited_owner(),
        Some(ExpressionDelimitedOwner::Index)
    );
    assert_eq!(i.local.pop_stop_set(), Some(stops));
    assert_eq!(i.local.pop_delimiter(), Some(Delimiter::Bracket));
    IndexTail { open: open.clone(), items, close, range: open.start..i.pos() }
}

fn parse_projection_tuple_tail<'source, E>(table: &OperatorTable, dot: Range<usize>, open: Range<usize>, i: &mut SynIn<'_, 'source, '_, E>) -> ProjectionTupleTail<'source>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    let incoming_base = i.local.indentation_baseline().map_or(0, |baseline| baseline.column);
    i.local.push_delimiter(Delimiter::Parenthesis);
    let stops = active_stop_set(i).with(StopKind::Comma).with(StopKind::Semicolon).with(StopKind::RightParenthesis);
    i.local.push_stop_set(stops); i.local.push_expression_delimited_owner(ExpressionDelimitedOwner::ProjectionTuple);
    let opening = consume_trivia(i).expect("trivia scanning is total");
    let layout = LayoutDelimitedFrame::after_opening_trivia(incoming_base, &opening, i.local.line().line_indent);
    push_layout_delimited_baseline(layout, i);
    let mut items = Vec::new();
    let close = match parse_projection_items_ast(table, i, layout, &mut items, recognize_parenthesized_close) {
        Recovered::Complete(close) => Recovered::Complete(close),
        Recovered::Incomplete => parse_projection_close_ast(i, Delimiter::Parenthesis),
    };
    pop_layout_delimited_baseline(layout, i);
    assert_eq!(i.local.pop_expression_delimited_owner(), Some(ExpressionDelimitedOwner::ProjectionTuple));
    assert_eq!(i.local.pop_stop_set(), Some(stops)); assert_eq!(i.local.pop_delimiter(), Some(Delimiter::Parenthesis));
    ProjectionTupleTail { dot: dot.clone(), open, items, close, range: dot.start..i.pos() }
}

fn parse_projection_items_ast<'source, E>(table: &OperatorTable, i: &mut SynIn<'_, 'source, '_, E>, layout: LayoutDelimitedFrame, items: &mut Vec<OperatorChain<'source>>, close: fn(SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>) -> Recovered<Range<usize>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    if let Some(close) = i.run(close) { return Recovered::Complete(close); }
    loop {
        if let Some(item) = i.run(from_fn(|i| parse_operator_chain(table, i))) { items.push(item); }
        else {
            if let Some(range) = call_argument_error_retry_ast(table, i) {
                items.push(OperatorChain::new(vec![OperatorChainItem::Error { range: range.clone() }], range));
                continue;
            }
            let at = i.pos();
            if i.run(recognize_call_separator).is_some() {
                items.push(OperatorChain::new(vec![OperatorChainItem::MissingOperand { range: at..at }], at..at));
                consume_trivia(i).expect("trivia scanning is total");
                if let Some(close) = i.run(close) { return Recovered::Complete(close); }
                continue;
            }
            return Recovered::Incomplete;
        }
        let trivia = consume_trivia(i).expect("trivia scanning is total");
        if i.run(recognize_call_separator).is_some() {
            consume_trivia(i).expect("trivia scanning is total");
            if let Some(close) = i.run(close) { return Recovered::Complete(close); }
            continue;
        }
        if let Some(close) = i.run(close) { return Recovered::Complete(close); }
        if layout.boundary_after_trivia(&trivia, i.local.line().line_indent) == LayoutDelimitedBoundary::ImplicitNewline { continue; }
        if expression_nud_candidate_input(table, i) {
            let at = i.pos();
            items.push(OperatorChain::new(vec![OperatorChainItem::MissingOperand { range: at..at }], at..at));
            continue;
        }
        return Recovered::Incomplete;
    }
}

fn parse_projection_record_tail<'source, E>(table: &OperatorTable, dot: Range<usize>, open: Range<usize>, i: &mut SynIn<'_, 'source, '_, E>) -> ProjectionRecordTail<'source>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    let incoming_base = i.local.indentation_baseline().map_or(0, |baseline| baseline.column);
    i.local.push_delimiter(Delimiter::Brace);
    let stops = active_stop_set(i).with(StopKind::Comma).with(StopKind::Semicolon).with(StopKind::RightBrace);
    i.local.push_stop_set(stops); i.local.push_expression_delimited_owner(ExpressionDelimitedOwner::ProjectionRecord);
    let opening = consume_trivia(i).expect("trivia scanning is total");
    let layout = LayoutDelimitedFrame::after_opening_trivia(incoming_base, &opening, i.local.line().line_indent);
    push_layout_delimited_baseline(layout, i);
    let mut items = Vec::new();
    let close = if let Some(close) = i.run(recognize_record_projection_close) { Recovered::Complete(close) } else { loop {
        if let Some(marker) = i.run(scan_exact_dot_dot) {
            let rhs_start = i.pos(); consume_trivia(i).expect("trivia scanning is total");
            let rhs = if let Some(rhs) = i.run(from_fn(|i| parse_operator_chain(table, i))) {
                Recovered::Complete(Box::new(rhs))
            } else if let Some(range) = call_argument_error_retry_ast(table, i) {
                Recovered::Complete(Box::new(OperatorChain::new(vec![OperatorChainItem::Error { range: range.clone() }], range)))
            } else { Recovered::Incomplete };
            items.push(ProjectionRecordItem::Spread(ProjectionRecordSpreadItem { marker: marker.clone(), rhs, range: marker.start..i.pos().max(rhs_start) }));
        } else if let Some(item) = i.run(from_fn(|i| parse_operator_chain(table, i))) { items.push(ProjectionRecordItem::Expression(item)); }
        else if let Some(range) = call_argument_error_retry_ast(table, i) { items.push(ProjectionRecordItem::Expression(OperatorChain::new(vec![OperatorChainItem::Error { range: range.clone() }], range))); continue; }
        else { break Recovered::Incomplete; }
        let trivia = consume_trivia(i).expect("trivia scanning is total");
        if i.run(recognize_call_separator).is_some() { consume_trivia(i).expect("trivia scanning is total"); if let Some(close) = i.run(recognize_record_projection_close) { break Recovered::Complete(close); } continue; }
        if let Some(close) = i.run(recognize_record_projection_close) { break Recovered::Complete(close); }
        if layout.boundary_after_trivia(&trivia, i.local.line().line_indent) == LayoutDelimitedBoundary::ImplicitNewline { continue; }
        if expression_nud_candidate_input(table, i) || exact_dot_dot_pending(i) {
            let at = i.pos(); items.push(ProjectionRecordItem::Expression(OperatorChain::new(vec![OperatorChainItem::MissingOperand { range: at..at }], at..at))); continue;
        }
        break Recovered::Incomplete;
    }};
    let close = match close {
        Recovered::Complete(close) => Recovered::Complete(close),
        Recovered::Incomplete => parse_projection_close_ast(i, Delimiter::Brace),
    };
    pop_layout_delimited_baseline(layout, i);
    assert_eq!(i.local.pop_expression_delimited_owner(), Some(ExpressionDelimitedOwner::ProjectionRecord));
    assert_eq!(i.local.pop_stop_set(), Some(stops)); assert_eq!(i.local.pop_delimiter(), Some(Delimiter::Brace));
    ProjectionRecordTail { dot: dot.clone(), open, items, close, range: dot.start..i.pos() }
}

fn exact_dot_dot_pending<E>(i: &mut SynIn<E>) -> bool
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint(); let pending = i.run(scan_exact_dot_dot).is_some(); i.rollback(checkpoint); pending
}

/// AST-side counterpart to the direct-CST projection closing-slot recovery.
/// A mismatched closer belongs to this committed tail's close slot; only EOF
/// and semicolon remain boundaries for an enclosing owner to handle.
fn parse_projection_close_ast<E>(i: &mut SynIn<E>, delimiter: Delimiter) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    loop {
        if i.input.remainder().is_empty()
            || matches!(i.input.remainder().chars().next(), Some(';'))
        {
            return Recovered::Incomplete;
        }
        if let Some(punctuation) = i.run(scan_punctuation) {
            if punctuation.kind() == PunctuationKind::Close(delimiter) {
                return Recovered::Complete(punctuation.range());
            }
            continue;
        }

        let start = i.pos();
        while let Some(character) = i.input.remainder().chars().next() {
            if matches!(character, ')' | ']' | '}' | ';') {
                break;
            }
            i.input.next().expect("the scanned projection-close byte exists");
            let mut line = i.local.line();
            line.at_line_start = false;
            i.local.set_line(line);
        }
        if i.pos() == start {
            return Recovered::Incomplete;
        }
    }
}

/// AST-side counterpart to [`call_argument_error_retry`].  The CallTail owns
/// malformed bytes only when a later shared NUD can retry the same argument
/// slot; otherwise its delimiter owner remains responsible for the boundary.
fn call_argument_error_retry_ast<'source, E>(
    table: &OperatorTable,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    loop {
        let Some(character) = i.input.remainder().chars().next() else {
            return None;
        };
        if matches!(character, ')' | ']' | '}' | ',' | ';') {
            return None;
        }
        i.input.next()?;
        let end = i.pos();
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
        if expression_nud_candidate_input(table, i) {
            return Some(start..end);
        }
    }
}

fn recognize_call_separator<'source, E>(mut i: SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let punctuation = i.run(scan_punctuation)?;
    matches!(punctuation.kind(), PunctuationKind::Comma | PunctuationKind::Semicolon)
        .then(|| punctuation.range())
        .or_else(|| { i.rollback(checkpoint); None })
}

fn path_segment(word: WordSpan<'_>) -> PathSegment<'_> {
    if matches!(word.text().chars().next(), Some('$' | '&' | '\''))
        || (word.text().starts_with('_') && word.text() != "_")
    {
        PathSegment::SigilIdentifier(word)
    } else {
        PathSegment::Identifier(word)
    }
}

/// Consume one maximal malformed fixed-tail RHS, leaving an owner boundary or
/// a later fixed continuation for its same-position retry.
fn consume_fixed_tail_invalid_run<E>(
    table: &OperatorTable,
    i: &mut SynIn<E>,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    while let Some(character) = i.input.remainder().chars().next() {
        if fixed_tail_recovery_boundary(table, i, character) {
            break;
        }
        i.input.next()?;
    }
    (start < i.pos()).then(|| start..i.pos())
}

fn fixed_tail_recovery_boundary<E>(
    table: &OperatorTable,
    i: &mut SynIn<E>,
    character: char,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if character.is_whitespace() || matches!(character, ')' | ']' | '}' | ',' | ';' | ':' | '.') {
        return true;
    }
    let checkpoint = i.checkpoint();
    let dynamic = i.run(from_fn(|i| scan_led(table, i))).is_some();
    i.rollback(checkpoint);
    dynamic
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ColonApplicationRecognition {
    leading: TriviaRun,
    colon: Range<usize>,
    rhs: ColonApplicationRhsRecognition,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ColonApplicationRhsRecognition {
    Inline { trivia: TriviaRun },
    Indented {
        opening_trivia: TriviaRun,
        base_indent: usize,
        block_indent: usize,
    },
    WrongIndent,
}

enum InlineColonSeparator {
    Comma { leading: TriviaRun, comma: Range<usize>, trailing: TriviaRun },
    Newline(TriviaRun),
}

fn parse_inline_colon_arguments<'source, E>(
    table: &OperatorTable,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<Vec<Recovered<OperatorChain<'source>>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let layout = LayoutDelimitedFrame::inline(
        i.local.indentation_baseline().map_or(0, |baseline| baseline.column),
    );
    let mut arguments = vec![Recovered::Complete(i.run(from_fn(|i| parse_operator_chain(table, i)))?)];
    loop {
        let checkpoint = i.checkpoint();
        let trivia = consume_trivia(i)?;
        if i.run(recognize_parenthesized_comma).is_some() {
            consume_trivia(i)?;
            arguments.push(Recovered::Complete(i.run(from_fn(|i| parse_operator_chain(table, i)))?));
            continue;
        }
        if layout.boundary_after_trivia(&trivia, i.local.line().line_indent)
            == LayoutDelimitedBoundary::ImplicitNewline
        {
            arguments.push(Recovered::Complete(i.run(from_fn(|i| parse_operator_chain(table, i)))?));
            continue;
        }
        i.rollback(checkpoint);
        return Some(arguments);
    }
}

/// Recognizes the one terminal fixed-punctuation continuation. `scan_punctuation`
/// tries `::` before `:`, so a use-path separator can never be split here.
fn recognize_colon_application_tail<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<ColonApplicationRecognition>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if i.local.ml_arg() || active_stop_set(&i).contains(StopKind::Colon) {
        return None;
    }

    let checkpoint = i.checkpoint();
    let leading = consume_trivia(&mut i)?;
    if !trivia_continues_chain(&leading, &i) {
        i.rollback(checkpoint);
        return None;
    }
    let Some(punctuation) = i.run(scan_punctuation) else {
        i.rollback(checkpoint);
        return None;
    };
    if punctuation.kind() != PunctuationKind::Colon {
        i.rollback(checkpoint);
        return None;
    }
    let base_indent = i
        .local
        .indentation_baseline()
        .map_or(0, |baseline| baseline.column);
    i.local.push_indentation_baseline(IndentationBaseline {
        column: base_indent,
        kind: IndentationBaselineKind::Introducer,
    });
    assert_eq!(
        i.local.pop_indentation_baseline(),
        Some(IndentationBaseline {
            column: base_indent,
            kind: IndentationBaselineKind::Introducer,
        })
    );
    let rhs = match recognize_introduced_body_layout(base_indent, &mut i) {
        ArmBodyLayout::Inline { trivia } => ColonApplicationRhsRecognition::Inline { trivia },
        ArmBodyLayout::Indented { opening_trivia, block_indent } => {
            ColonApplicationRhsRecognition::Indented { opening_trivia, base_indent, block_indent }
        }
        ArmBodyLayout::WrongIndent => ColonApplicationRhsRecognition::WrongIndent,
    };
    Some(ColonApplicationRecognition {
        leading,
        colon: punctuation.range(),
        rhs,
    })
}

fn active_stop_set<E>(i: &SynIn<E>) -> StopSet
where
    E: ErrorSink<usize>,
{
    i.local.stop_set().unwrap_or_default()
}

/// An outer comma sequence owns both comma and qualifying-newline boundaries.
/// A colon tail therefore makes one ownership decision before its inline loop.
fn outer_owns_inline_argument_sequence<E>(i: &SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
{
    active_stop_set(i).contains(StopKind::Comma)
}

fn expression_nud_candidate_input<E>(table: &OperatorTable, i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let candidate = i.run(from_fn(|i| recognize_nud(table, LeadingTrivia::None, i))).is_some();
    i.rollback(checkpoint);
    candidate
}

fn trivia_continues_chain<E>(trivia: &TriviaRun, i: &SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
{
    !trivia_has_physical_newline(trivia)
        || i.local.line().line_indent
            > i.local
                .indentation_baseline()
                .map_or(0, |baseline| baseline.column)
}

fn trivia_has_physical_newline(trivia: &TriviaRun) -> bool {
    trivia
        .parts()
        .iter()
        .any(|part| matches!(part.kind(), crate::scan::trivia::TriviaPartKind::Newline))
}

fn recognize_nud<'source, E>(
    table: &OperatorTable,
    leading: LeadingTrivia,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<NudRecognition<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    i.choice((
        recognize_parenthesized_open.map(|open| NudRecognition::Parenthesized { open }),
        recognize_braced_statement_block_open.map(|open| NudRecognition::BracedStatementBlock { open }),
        from_fn(recognize_if_nud),
        from_fn(recognize_case_like_nud),
        from_fn(|i| {
            let scanned = scan_operator(OperatorSite::Nud, leading, table, i)?;
            match scanned.fixity() {
                ScannedFixity::Prefix { .. } => Some(NudRecognition::Prefix(scanned)),
                ScannedFixity::Nullfix => Some(NudRecognition::Nullfix(scanned)),
                ScannedFixity::Infix { .. } | ScannedFixity::Suffix { .. } => None,
            }
        }),
        parse_identifier.map(NudRecognition::Identifier),
        parse_integer_literal.map(NudRecognition::Integer),
    ))
}

fn recognize_case_like_nud<'source, E>(mut i: SynIn<'_, 'source, '_, E>) -> Option<NudRecognition<'source>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    let word = i.run(scan_word)?;
    let base_indent = i.local.indentation_baseline().map_or(0, |baseline| baseline.column);
    match word.text() {
        "case" => Some(NudRecognition::Case { keyword: word, base_indent }),
        "catch" => Some(NudRecognition::Catch { keyword: word, base_indent }),
        _ => None,
    }
}

/// `if` stays a contextual word: this NUD judge accepts only the exact
/// maximal spelling, leaving `ifx` and `if?` to the ordinary identifier path.
fn recognize_if_nud<'source, E>(mut i: SynIn<'_, 'source, '_, E>) -> Option<NudRecognition<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let word = i.run(scan_word)?;
    (word.text() == "if").then(|| NudRecognition::If {
        keyword: word,
        base_indent: i.local.indentation_baseline().map_or(0, |baseline| baseline.column),
    })
}

fn parse_if_expression<'source, E>(
    table: &OperatorTable,
    keyword: WordSpan<'source>,
    base_indent: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> IfExpression<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = keyword.range().start;
    let mut arms = vec![parse_if_arm(table, IfArmKeyword::If(keyword), base_indent, i)];
    let mut else_arm = None;
    while let Some(keyword) = recognize_if_arm_continuation(base_indent, i) {
        match keyword {
            IfContinuationKeyword::Elsif { keyword, .. } => {
                arms.push(parse_if_arm(table, IfArmKeyword::Elsif(keyword), base_indent, i));
            }
            IfContinuationKeyword::Else { keyword, .. } => {
                else_arm = Some(parse_else_arm(table, keyword, base_indent, i));
                break;
            }
        }
    }
    let end = else_arm.as_ref().map_or_else(
        || arms.last().expect("if has an initial arm").range.end,
        |arm| arm.range.end,
    );
    IfExpression { arms, else_arm, base_indent, range: start..end }
}

fn parse_case_expression<'source, E>(table: &OperatorTable, keyword: WordSpan<'source>, base_indent: usize, i: &mut SynIn<'_, 'source, '_, E>) -> CaseExpression<'source>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    let start = keyword.range().start;
    consume_trivia(i).expect("trivia scanning is total");
    let label = parse_case_like_label(i);
    consume_trivia(i).expect("trivia scanning is total");
    let stops = active_stop_set(i).with(StopKind::Colon);
    i.local.push_stop_set(stops);
    let scrutinee = i.run(from_fn(|i| parse_operator_chain(table, i))).map(|value| Recovered::Complete(Box::new(value))).unwrap_or(Recovered::Incomplete);
    assert_eq!(i.local.pop_stop_set(), Some(stops));
    consume_trivia(i).expect("trivia scanning is total");
    let block = recognize_arm_colon(i).map(|colon| Recovered::Complete(parse_case_block_ast(table, colon, base_indent, i))).unwrap_or(Recovered::Incomplete);
    let end = match &block { Recovered::Complete(block) => block.range.end, Recovered::Incomplete => match &scrutinee { Recovered::Complete(value) => value.range.end, Recovered::Incomplete => keyword.range().end } };
    CaseExpression { keyword, label, scrutinee, block, base_indent, range: start..end }
}

fn parse_catch_expression<'source, E>(table: &OperatorTable, keyword: WordSpan<'source>, base_indent: usize, i: &mut SynIn<'_, 'source, '_, E>) -> CatchExpression<'source>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    let start = keyword.range().start;
    consume_trivia(i).expect("trivia scanning is total");
    let label = parse_case_like_label(i);
    consume_trivia(i).expect("trivia scanning is total");
    let stops = active_stop_set(i).with(StopKind::Colon).with(StopKind::LeftBrace);
    i.local.push_stop_set(stops);
    let scrutinee = i.run(from_fn(|i| parse_operator_chain(table, i))).map(|value| Recovered::Complete(Box::new(value))).unwrap_or(Recovered::Incomplete);
    assert_eq!(i.local.pop_stop_set(), Some(stops));
    consume_trivia(i).expect("trivia scanning is total");
    let block = if let Some(colon) = recognize_arm_colon(i) {
        Recovered::Complete(parse_catch_colon_block_ast(table, colon, base_indent, i))
    } else if let Some(open) = i.run(recognize_braced_statement_block_open) {
        Recovered::Complete(parse_catch_braced_block_ast(table, open, i))
    } else { Recovered::Incomplete };
    let end = match &block { Recovered::Complete(CatchBlock::Colon { range, .. } | CatchBlock::Braced { range, .. }) => range.end, Recovered::Incomplete => match &scrutinee { Recovered::Complete(value) => value.range.end, Recovered::Incomplete => keyword.range().end } };
    CatchExpression { keyword, label, scrutinee, block, base_indent, range: start..end }
}

fn parse_case_like_label<'source, E>(i: &mut SynIn<'_, 'source, '_, E>) -> Option<CaseLikeLabel<'source>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let Some(punctuation) = i.run(scan_punctuation) else { return None; };
    if punctuation.kind() != PunctuationKind::Apostrophe { i.rollback(checkpoint); return None; }
    let Some(word) = i.run(scan_word) else { i.rollback(checkpoint); return None; };
    let range = punctuation.range().start..word.range().end;
    Some(CaseLikeLabel { text: &i.input.source()[range.clone()], range })
}

fn parse_case_block_ast<'source, E>(table: &OperatorTable, colon: Range<usize>, base_indent: usize, i: &mut SynIn<'_, 'source, '_, E>) -> CaseBlock<'source>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    let layout = recognize_introduced_body_layout(base_indent, i);
    let (layout_kind, policy) = match layout {
        ArmBodyLayout::Inline { .. } => (ColonArmLayout::Inline, ArmSequencePolicy::CaseInline),
        ArmBodyLayout::Indented { opening_trivia, block_indent } => { let _ = opening_trivia; (ColonArmLayout::Indented { base_indent, arm_indent: block_indent }, ArmSequencePolicy::Indented { family: CaseLikeFamily::Case, base_indent, arm_indent: block_indent }) }
        ArmBodyLayout::WrongIndent => return CaseBlock { colon: Recovered::Complete(colon.clone()), arms: Recovered::Incomplete, layout: ColonArmLayout::Inline, range: colon.clone() },
    };
    let arms = Recovered::Complete(parse_case_arm_sequence_ast(table, policy, i));
    let end = i.pos();
    CaseBlock { colon: Recovered::Complete(colon.clone()), arms, layout: layout_kind, range: colon.start..end }
}

fn parse_catch_colon_block_ast<'source, E>(table: &OperatorTable, colon: Range<usize>, base_indent: usize, i: &mut SynIn<'_, 'source, '_, E>) -> CatchBlock<'source>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    let layout = recognize_introduced_body_layout(base_indent, i);
    let (layout_kind, policy) = match layout {
        ArmBodyLayout::Inline { .. } => (ColonArmLayout::Inline, ArmSequencePolicy::CatchInlineSingle),
        ArmBodyLayout::Indented { opening_trivia, block_indent } => { let _ = opening_trivia; (ColonArmLayout::Indented { base_indent, arm_indent: block_indent }, ArmSequencePolicy::Indented { family: CaseLikeFamily::Catch, base_indent, arm_indent: block_indent }) }
        ArmBodyLayout::WrongIndent => return CatchBlock::Colon { colon: Recovered::Complete(colon.clone()), arms: Recovered::Incomplete, layout: ColonArmLayout::Inline, range: colon.clone() },
    };
    let arms = Recovered::Complete(parse_catch_arm_sequence_ast(table, policy, i));
    CatchBlock::Colon { colon: Recovered::Complete(colon.clone()), arms, layout: layout_kind, range: colon.start..i.pos() }
}

fn parse_catch_braced_block_ast<'source, E>(table: &OperatorTable, open: Range<usize>, i: &mut SynIn<'_, 'source, '_, E>) -> CatchBlock<'source>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    let scope = push_braced_statement_block_scope(i);
    consume_trivia(i).expect("trivia scanning is total");
    let arms = Recovered::Complete(parse_catch_arm_sequence_ast(table, ArmSequencePolicy::CatchBraced, i));
    consume_trivia(i).expect("trivia scanning is total");
    let close = i.run(recognize_braced_statement_block_close).map_or(Recovered::Incomplete, Recovered::Complete);
    let end = match &close { Recovered::Complete(close) => close.end, Recovered::Incomplete => i.pos() };
    pop_braced_statement_block_scope(i, scope);
    CatchBlock::Braced { open: open.clone(), arms, close, range: open.start..end }
}

fn parse_case_arm_sequence_ast<'source, E>(table: &OperatorTable, policy: ArmSequencePolicy, i: &mut SynIn<'_, 'source, '_, E>) -> ArmSequence<CaseArm<'source>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    let mut arms = vec![Recovered::Complete(parse_case_arm_ast(table, policy, i))];
    let mut trailing_comma = None;
    while policy_allows_multiple(policy) {
        let checkpoint = i.checkpoint();
        let trivia = consume_trivia(i).expect("trivia scanning is total");
        if let Some(comma) = i.run(recognize_parenthesized_comma) {
            consume_trivia(i).expect("trivia scanning is total");
            if arm_sequence_boundary(policy, i) { trailing_comma = Some(comma); break; }
            arms.push(Recovered::Complete(parse_case_arm_ast(table, policy, i)));
        } else if policy_newline_separator(policy, &trivia, i) {
            arms.push(Recovered::Complete(parse_case_arm_ast(table, policy, i)));
        } else if pattern_nud_candidate_input(i) {
            arms.push(Recovered::Complete(parse_case_arm_ast(table, policy, i)));
        } else { i.rollback(checkpoint); break; }
    }
    ArmSequence { arms, trailing_comma }
}

fn parse_catch_arm_sequence_ast<'source, E>(table: &OperatorTable, policy: ArmSequencePolicy, i: &mut SynIn<'_, 'source, '_, E>) -> ArmSequence<CatchArm<'source>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    let mut arms = vec![Recovered::Complete(parse_catch_arm_ast(table, policy, i))];
    let mut trailing_comma = None;
    while policy_allows_multiple(policy) {
        let checkpoint = i.checkpoint();
        let trivia = consume_trivia(i).expect("trivia scanning is total");
        if let Some(comma) = i.run(recognize_parenthesized_comma) {
            consume_trivia(i).expect("trivia scanning is total");
            if arm_sequence_boundary(policy, i) { trailing_comma = Some(comma); break; }
            arms.push(Recovered::Complete(parse_catch_arm_ast(table, policy, i)));
        } else if policy_newline_separator(policy, &trivia, i) {
            arms.push(Recovered::Complete(parse_catch_arm_ast(table, policy, i)));
        } else if pattern_nud_candidate_input(i) {
            arms.push(Recovered::Complete(parse_catch_arm_ast(table, policy, i)));
        } else { i.rollback(checkpoint); break; }
    }
    ArmSequence { arms, trailing_comma }
}

fn policy_allows_multiple(policy: ArmSequencePolicy) -> bool { !matches!(policy, ArmSequencePolicy::CatchInlineSingle) }
fn arm_sequence_boundary<E>(policy: ArmSequencePolicy, i: &mut SynIn<E>) -> bool where E: ErrorSink<usize> {
    if i.input.remainder().is_empty() || (matches!(policy, ArmSequencePolicy::CatchBraced) && i.input.remainder().starts_with('}')) { return true; }
    match policy { ArmSequencePolicy::Indented { arm_indent, .. } => i.local.line().line_indent < arm_indent, _ => false }
}
fn policy_newline_separator<E>(policy: ArmSequencePolicy, trivia: &TriviaRun, i: &SynIn<E>) -> bool where E: ErrorSink<usize> {
    if !trivia_has_physical_newline(trivia) { return false; }
    match policy { ArmSequencePolicy::Indented { arm_indent, .. } => i.local.line().line_indent == arm_indent, ArmSequencePolicy::CatchBraced => true, _ => false }
}

fn parse_case_arm_ast<'source, E>(table: &OperatorTable, policy: ArmSequencePolicy, i: &mut SynIn<'_, 'source, '_, E>) -> CaseArm<'source>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let stops = active_stop_set(i).with(StopKind::Arrow).with(StopKind::ArmGuardIf).with(StopKind::ArmGuardWhere);
    i.local.push_stop_set(stops);
    let pattern = i.run(from_fn(|i| parse_pattern(table, i))).map_or(Recovered::Incomplete, Recovered::Complete);
    assert_eq!(i.local.pop_stop_set(), Some(stops));
    let guard = parse_case_guard_ast(table, i);
    let arrow = parse_arm_arrow(i).map_or(Recovered::Incomplete, Recovered::Complete);
    let body = parse_arm_body_ast(table, policy, i);
    let terminator = parse_optional_semicolon(i);
    let end = i.pos();
    CaseArm { pattern, guard, arrow, body, terminator, range: start..end }
}

fn parse_catch_arm_ast<'source, E>(table: &OperatorTable, policy: ArmSequencePolicy, i: &mut SynIn<'_, 'source, '_, E>) -> CatchArm<'source>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let stops = active_stop_set(i).with(StopKind::Arrow).with(StopKind::ArmGuardIf).with(StopKind::ArmGuardWhere).with(StopKind::Comma);
    i.local.push_stop_set(stops);
    let pattern = i.run(from_fn(|i| parse_pattern(table, i))).map_or(Recovered::Incomplete, Recovered::Complete);
    assert_eq!(i.local.pop_stop_set(), Some(stops));
    let handler = if let Some(_) = i.run(recognize_parenthesized_comma) {
        consume_trivia(i).expect("trivia scanning is total");
        let stops = active_stop_set(i).with(StopKind::Arrow).with(StopKind::ArmGuardIf).with(StopKind::ArmGuardWhere);
        i.local.push_stop_set(stops);
        let handler = i.run(from_fn(|i| parse_pattern(table, i))).map_or(Recovered::Incomplete, Recovered::Complete);
        assert_eq!(i.local.pop_stop_set(), Some(stops));
        Some(handler)
    } else { None };
    let guard = parse_catch_guard_ast(table, i);
    let arrow = parse_arm_arrow(i).map_or(Recovered::Incomplete, Recovered::Complete);
    let body = parse_arm_body_ast(table, policy, i);
    let terminator = parse_optional_semicolon(i);
    let end = i.pos();
    CatchArm { pattern, handler, guard, arrow, body, terminator, range: start..end }
}

fn parse_case_guard_ast<'source, E>(table: &OperatorTable, i: &mut SynIn<'_, 'source, '_, E>) -> Option<Recovered<CaseGuard<'source>>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>, { parse_arm_guard_ast(table, i).map(|(keyword, condition, range)| Recovered::Complete(CaseGuard { keyword, condition, range })) }
fn parse_catch_guard_ast<'source, E>(table: &OperatorTable, i: &mut SynIn<'_, 'source, '_, E>) -> Option<Recovered<CatchGuard<'source>>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>, { parse_arm_guard_ast(table, i).map(|(keyword, condition, range)| Recovered::Complete(CatchGuard { keyword, condition, range })) }
fn parse_arm_guard_ast<'source, E>(table: &OperatorTable, i: &mut SynIn<'_, 'source, '_, E>) -> Option<(ArmGuardKeyword<'source>, Recovered<Box<OperatorChain<'source>>>, Range<usize>)>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint(); let Some(trivia) = consume_trivia(i) else { return None; }; let Some(word) = i.run(scan_word) else { i.rollback(checkpoint); return None; };
    let keyword = match word.text() { "if" => ArmGuardKeyword::If(word), "where" => ArmGuardKeyword::Where(word), _ => { i.rollback(checkpoint); return None; } };
    let _ = trivia; consume_trivia(i).expect("trivia scanning is total");
    let stops = active_stop_set(i).with(StopKind::Arrow); i.local.push_stop_set(stops);
    let condition = i.run(from_fn(|i| parse_operator_chain(table, i))).map(|value| Recovered::Complete(Box::new(value))).unwrap_or(Recovered::Incomplete);
    assert_eq!(i.local.pop_stop_set(), Some(stops)); let end = match &condition { Recovered::Complete(value) => value.range.end, Recovered::Incomplete => word.range().end };
    Some((keyword, condition, word.range().start..end))
}

fn parse_arm_arrow<E>(i: &mut SynIn<E>) -> Option<Range<usize>> where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> { consume_trivia(i)?; i.run(scan_exact_arrow) }
fn parse_optional_semicolon<E>(i: &mut SynIn<E>) -> Option<Range<usize>> where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> { let checkpoint = i.checkpoint(); consume_trivia(i)?; let semicolon = i.run(scan_punctuation).and_then(|punctuation| (punctuation.kind() == PunctuationKind::Semicolon).then(|| punctuation.range())); if semicolon.is_none() { i.rollback(checkpoint); } semicolon }
fn parse_arm_body_ast<'source, E>(table: &OperatorTable, policy: ArmSequencePolicy, i: &mut SynIn<'_, 'source, '_, E>) -> Recovered<ArmBody<'source>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    let baseline = push_arm_body_baseline(policy, i);
    let stops = arm_body_stop(policy, active_stop_set(i));
    i.local.push_stop_set(stops);
    let base_indent = i.local.line().line_indent;
    let body = match recognize_introduced_body_layout(base_indent, i) {
        ArmBodyLayout::Inline { .. } => i.run(from_fn(|i| parse_operator_chain(table, i))).map(|value| Recovered::Complete(ArmBody::Inline(Box::new(value)))).unwrap_or(Recovered::Incomplete),
        ArmBodyLayout::Indented { opening_trivia, block_indent } => Recovered::Complete(ArmBody::Indented(parse_indented_statement_block(table, opening_trivia, base_indent, block_indent, i))),
        ArmBodyLayout::WrongIndent => Recovered::Incomplete,
    };
    assert_eq!(i.local.pop_stop_set(), Some(stops));
    pop_arm_body_baseline(baseline, i);
    body
}

fn scan_exact_arrow<'source, E>(mut i: SynIn<'_, 'source, '_, E>) -> Option<Range<usize>> where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> { let start = i.pos(); if !i.input.remainder().starts_with("->") || i.input.remainder().starts_with("->>") { return None; } i.input.next()?; i.input.next()?; let end = i.pos(); let mut line = i.local.line(); line.at_line_start = false; i.local.set_line(line); Some(start..end) }

fn parse_if_arm<'source, E>(
    table: &OperatorTable,
    keyword: IfArmKeyword<'source>,
    base_indent: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> IfArm<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = match keyword { IfArmKeyword::If(word) | IfArmKeyword::Elsif(word) => word.range().start };
    consume_trivia(i).expect("trivia scanning is total");
    let condition_stop = active_stop_set(i)
        .with(StopKind::Colon)
        .with(StopKind::LeftBrace)
        .with(StopKind::Elsif)
        .with(StopKind::Else);
    i.local.push_stop_set(condition_stop);
    let condition = i.run(from_fn(|i| parse_operator_chain(table, i))).map_or(Recovered::Incomplete, Recovered::Complete);
    assert_eq!(i.local.pop_stop_set(), Some(condition_stop));
    let colon = recognize_arm_colon(i);
    let body = colon.map_or(Recovered::Incomplete, |colon| {
        Recovered::Complete(parse_colon_introduced_arm_body(table, colon, base_indent, i))
    });
    let end = match &body {
        Recovered::Complete(body) => body.range.end,
        Recovered::Incomplete => condition_end(&condition).unwrap_or_else(|| keyword_end(keyword)),
    };
    IfArm { keyword, condition, body, range: start..end }
}

fn parse_else_arm<'source, E>(
    table: &OperatorTable,
    keyword: WordSpan<'source>,
    base_indent: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> ElseArm<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    consume_trivia(i).expect("trivia scanning is total");
    let body = if let Some(colon) = recognize_arm_colon(i) {
        Recovered::Complete(ElseArmBody::Colon(parse_colon_introduced_arm_body(table, colon, base_indent, i)))
    } else {
        let stop_set = active_stop_set(i).with(StopKind::Elsif).with(StopKind::Else);
        i.local.push_stop_set(stop_set);
        let body = i.run(from_fn(|i| parse_operator_chain(table, i))).map(|chain| ElseArmBody::Bare(Box::new(chain)));
        assert_eq!(i.local.pop_stop_set(), Some(stop_set));
        body.map_or(Recovered::Incomplete, Recovered::Complete)
    };
    let end = match &body {
        Recovered::Complete(ElseArmBody::Colon(body)) => body.range.end,
        Recovered::Complete(ElseArmBody::Bare(chain)) => chain.range.end,
        Recovered::Incomplete => keyword.range().end,
    };
    ElseArm { keyword, body, range: keyword.range().start..end }
}

fn condition_end(condition: &Recovered<OperatorChain<'_>>) -> Option<usize> {
    match condition { Recovered::Complete(chain) => Some(chain.range.end), Recovered::Incomplete => None }
}

fn keyword_end(keyword: IfArmKeyword<'_>) -> usize {
    match keyword { IfArmKeyword::If(word) | IfArmKeyword::Elsif(word) => word.range().end }
}

fn recognize_arm_colon<'source, E>(i: &mut SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let punctuation = i.run(scan_punctuation)?;
    let colon = (punctuation.kind() == PunctuationKind::Colon).then(|| punctuation.range());
    if colon.is_none() { i.rollback(checkpoint); }
    colon
}

fn parse_colon_introduced_arm_body<'source, E>(
    table: &OperatorTable,
    colon: Range<usize>,
    base_indent: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> ColonIntroducedArmBody<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let layout = recognize_introduced_body_layout(base_indent, i);
    let rhs = match layout {
        ArmBodyLayout::Inline { trivia: _ } => {
            let chain = i.run(from_fn(|i| parse_operator_chain(table, i)));
            chain.map(|chain| ArmBodyRhs::Inline(Box::new(chain))).map_or(Recovered::Incomplete, Recovered::Complete)
        }
        ArmBodyLayout::Indented { opening_trivia, block_indent } => Recovered::Complete(ArmBodyRhs::Indented(
            parse_indented_statement_block_with_options(
                table,
                opening_trivia,
                base_indent,
                block_indent,
                IndentedStatementBlockOptions::if_arm(base_indent),
                i,
            ),
        )),
        ArmBodyLayout::WrongIndent => Recovered::Incomplete,
    };
    let end = match &rhs {
        Recovered::Complete(ArmBodyRhs::Inline(chain)) => chain.range.end,
        Recovered::Complete(ArmBodyRhs::Indented(block)) => block.range.end,
        Recovered::Incomplete => colon.end,
    };
    ColonIntroducedArmBody { colon: Recovered::Complete(colon.clone()), rhs, range: colon.start..end }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ArmBodyLayout {
    Inline { trivia: TriviaRun },
    Indented { opening_trivia: TriviaRun, block_indent: usize },
    WrongIndent,
}

/// Classifies a body after its owner has already consumed an introducer.
fn recognize_introduced_body_layout<'source, E>(base_indent: usize, i: &mut SynIn<'_, 'source, '_, E>) -> ArmBodyLayout
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = consume_trivia(i).expect("trivia scanning is total");
    if !trivia_has_physical_newline(&trivia) {
        return ArmBodyLayout::Inline { trivia };
    }
    let block_indent = i.local.line().line_indent;
    if block_indent > base_indent {
        ArmBodyLayout::Indented { opening_trivia: trivia, block_indent }
    } else {
        i.rollback(checkpoint);
        ArmBodyLayout::WrongIndent
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum IfContinuationKeyword<'source> {
    Elsif { keyword: WordSpan<'source>, trivia: TriviaRun },
    Else { keyword: WordSpan<'source>, trivia: TriviaRun },
}

fn recognize_if_arm_continuation<'source, E>(base_indent: usize, i: &mut SynIn<'_, 'source, '_, E>) -> Option<IfContinuationKeyword<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = consume_trivia(i)?;
    if trivia_has_physical_newline(&trivia) && i.local.line().line_indent < base_indent {
        i.rollback(checkpoint);
        return None;
    }
    let Some(word) = i.run(scan_word) else { i.rollback(checkpoint); return None; };
    let keyword = match word.text() {
        "elsif" => IfContinuationKeyword::Elsif { keyword: word, trivia },
        "else" => IfContinuationKeyword::Else { keyword: word, trivia },
        _ => { i.rollback(checkpoint); return None; }
    };
    Some(keyword)
}

fn recognize_parenthesized_open<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let punctuation = i.run(scan_punctuation)?;
    matches!(
        punctuation.kind(),
        PunctuationKind::Open(Delimiter::Parenthesis)
    )
    .then(|| punctuation.range())
}

fn recognize_parenthesized_close<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let punctuation = i.run(scan_punctuation)?;
    let close = matches!(
        punctuation.kind(),
        PunctuationKind::Close(Delimiter::Parenthesis)
    )
    .then(|| punctuation.range());
    if close.is_none() {
        i.rollback(checkpoint);
    }
    close
}

fn recognize_index_close<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let punctuation = i.run(scan_punctuation)?;
    let close = matches!(punctuation.kind(), PunctuationKind::Close(Delimiter::Bracket))
        .then(|| punctuation.range());
    if close.is_none() {
        i.rollback(checkpoint);
    }
    close
}

fn recognize_record_projection_close<'source, E>(mut i: SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>,
{
    let checkpoint = i.checkpoint(); let punctuation = i.run(scan_punctuation)?;
    let close = (punctuation.kind() == PunctuationKind::Close(Delimiter::Brace)).then(|| punctuation.range());
    if close.is_none() { i.rollback(checkpoint); }
    close
}

fn scan_exact_dot_dot<'source, E>(mut i: SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint(); let start = i.pos();
    while i.input.remainder().chars().next().is_some_and(is_operator_shaped_character) { i.input.next()?; }
    let end = i.pos();
    if &i.input.source()[start..end] != ".." { i.rollback(checkpoint); return None; }
    let mut line = i.local.line(); line.at_line_start = false; i.local.set_line(line); Some(start..end)
}

fn is_operator_shaped_character(character: char) -> bool {
    !character.is_whitespace()
        && !character.is_ascii_digit()
        && character != '_'
        && !unicode_ident::is_xid_continue(character)
        && !matches!(character, '(' | ')' | '[' | ']' | '{' | '}' | ',' | ':' | '/' | ';' | '\\' | '\'' | '@')
}

fn recognize_braced_statement_block_open<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let punctuation = i.run(scan_punctuation)?;
    matches!(punctuation.kind(), PunctuationKind::Open(Delimiter::Brace)).then(|| punctuation.range())
}

fn recognize_braced_statement_block_close<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let punctuation = i.run(scan_punctuation)?;
    let close = matches!(punctuation.kind(), PunctuationKind::Close(Delimiter::Brace))
        .then(|| punctuation.range());
    if close.is_none() {
        i.rollback(checkpoint);
    }
    close
}

fn recognize_parenthesized_comma<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let punctuation = i.run(scan_punctuation)?;
    let comma = (punctuation.kind() == PunctuationKind::Comma).then(|| punctuation.range());
    if comma.is_none() {
        i.rollback(checkpoint);
    }
    comma
}

fn recognize_led<'source, E>(
    table: &OperatorTable,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<Option<LedRecognition<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    i.maybe(from_fn(|i| scan_led(table, i)))
}

fn scan_led<'source, E>(
    table: &OperatorTable,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<LedRecognition<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let leading = consume_trivia(&mut i)?;
    if active_stop_set(&i).contains(StopKind::Arrow) && i.input.remainder().starts_with("->") {
        return None;
    }
    let leading_presence = leading_trivia(&leading);
    let scanned = scan_operator(OperatorSite::Led, leading_presence, table, i)?;

    match scanned.fixity() {
        ScannedFixity::Infix { .. } => Some(LedRecognition::Infix { leading, operator: scanned }),
        ScannedFixity::Suffix { .. } => Some(LedRecognition::Suffix { leading, operator: scanned }),
        ScannedFixity::Prefix { .. } | ScannedFixity::Nullfix => None,
    }
}

fn consume_trivia<E>(i: &mut SynIn<E>) -> Option<TriviaRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    i.run(scan_trivia)
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
    committed.probe(|probe| consume_trivia(probe.input()).expect("trivia scanning is total"))
}

fn commit_fixed_postfix_tail<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    tail: FixedPostfixRecognition,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    match tail {
        FixedPostfixRecognition::Call { open } => commit_call_tail(table, open, committed),
        FixedPostfixRecognition::Index { open } => commit_index_tail(table, open, committed),
        FixedPostfixRecognition::ProjectionTuple { leading, dot, open } => commit_projection_tuple_tail(table, leading, dot, open, committed),
        FixedPostfixRecognition::ProjectionRecord { leading, dot, open } => commit_projection_record_tail(table, leading, dot, open, committed),
        FixedPostfixRecognition::Field { leading, dot } => {
            committed.emit_trivia(&leading);
            committed.start_node(SyntaxKind::FieldTail);
            committed.token(SyntaxKind::Dot, dot);
            if let Some(name) = committed.probe(|probe| probe.input().run(scan_word)) {
                committed.token(SyntaxKind::Identifier, name.range());
            } else if let Some(range) = committed.probe(|probe| consume_fixed_tail_invalid_run(table, probe.input())) {
                emit_fixed_tail_error(committed, ExpressionRole::FieldName, range);
            } else {
                emit_fixed_tail_missing(committed, ExpressionRole::FieldName);
            }
            committed.finish_node();
        }
        FixedPostfixRecognition::Path { leading, separator } => {
            committed.emit_trivia(&leading);
            committed.start_node(SyntaxKind::PathTail);
            committed.token(SyntaxKind::ColonColon, separator);
            let trivia = consume_direct_trivia(committed);
            committed.emit_trivia(&trivia);
            if let Some(segment) = committed.probe(|probe| probe.input().run(scan_path_segment)) {
                committed.token(path_segment_kind(segment), segment.range());
            } else if let Some(range) = committed.probe(|probe| consume_fixed_tail_invalid_run(table, probe.input())) {
                emit_fixed_tail_error(committed, ExpressionRole::PathSegment, range);
            } else {
                emit_fixed_tail_missing(committed, ExpressionRole::PathSegment);
            }
            committed.finish_node();
        }
    }
}

fn commit_call_tail<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    open: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>, O: CommitOutput<'source>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::CallTail);
    committed.token(SyntaxKind::LParen, open);
    let incoming_base = committed.probe(|probe| probe.input().local.indentation_baseline().map_or(0, |baseline| baseline.column));
    let stops = committed.probe(|probe| active_stop_set(probe.input()).with(StopKind::Comma).with(StopKind::Semicolon).with(StopKind::RightParenthesis));
    committed.probe(|probe| { probe.input().local.push_delimiter(Delimiter::Parenthesis); probe.input().local.push_stop_set(stops); probe.input().local.push_expression_delimited_owner(ExpressionDelimitedOwner::Call); });
    let opening = consume_direct_trivia(committed); committed.emit_trivia(&opening);
    let layout = committed.probe(|probe| LayoutDelimitedFrame::after_opening_trivia(incoming_base, &opening, probe.input().local.line().line_indent));
    committed.probe(|probe| push_layout_delimited_baseline(layout, probe.input()));

    if !parenthesized_close_pending(committed) {
        loop {
            if parse_direct_operator_chain(table, LeadingTrivia::None, committed).is_none() {
                if call_argument_error_retry(table, committed) {
                    parse_direct_operator_chain(table, LeadingTrivia::None, committed)
                        .expect("a retried call argument must commit its shared NUD candidate");
                } else {
                    emit_call_missing(committed, ExpressionRole::CallArgument, ExpectedSyntax::Expression);
                }
            }
            let trivia = consume_direct_trivia(committed); committed.emit_trivia(&trivia);
            if let Some(separator) = commit_call_separator(committed) {
                committed.token(if separator.0 { SyntaxKind::Semicolon } else { SyntaxKind::Comma }, separator.1);
                let trailing = consume_direct_trivia(committed); committed.emit_trivia(&trailing);
                if parenthesized_close_pending(committed) { break; }
                continue;
            }
            if parenthesized_close_pending(committed) { break; }
            let boundary = committed.probe(|probe| layout.boundary_after_trivia(&trivia, probe.input().local.line().line_indent));
            if boundary == LayoutDelimitedBoundary::ImplicitNewline { continue; }
            if boundary == LayoutDelimitedBoundary::None && parenthesized_element_pending(table, committed) {
                emit_call_missing(committed, ExpressionRole::CallArgumentSeparator, ExpectedSyntax::DelimitedSequenceSeparator);
                continue;
            }
            break;
        }
    }
    match commit_call_close(committed) {
        ParenthesizedClose::Matched(close) => committed.token(SyntaxKind::RParen, close),
        ParenthesizedClose::Missing { .. } => emit_call_close_missing(committed),
    }
    committed.probe(|probe| { pop_layout_delimited_baseline(layout, probe.input()); assert_eq!(probe.input().local.pop_expression_delimited_owner(), Some(ExpressionDelimitedOwner::Call)); assert_eq!(probe.input().local.pop_stop_set(), Some(stops)); assert_eq!(probe.input().local.pop_delimiter(), Some(Delimiter::Parenthesis)); });
    committed.finish_node();
}

fn commit_projection_tuple_tail<'parse, 'source, 'local, E, O>(table: &OperatorTable, leading: TriviaRun, dot: Range<usize>, open: Range<usize>, committed: &mut Committed<'parse, 'source, 'local, E, O>)
where E: ErrorSink<usize>, O: CommitOutput<'source>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    committed.emit_trivia(&leading); committed.start_node(SyntaxKind::ProjectionTupleTail); committed.token(SyntaxKind::Dot, dot); committed.token(SyntaxKind::LParen, open);
    let incoming_base = committed.probe(|probe| probe.input().local.indentation_baseline().map_or(0, |baseline| baseline.column));
    let stops = committed.probe(|probe| active_stop_set(probe.input()).with(StopKind::Comma).with(StopKind::Semicolon).with(StopKind::RightParenthesis));
    committed.probe(|probe| { probe.input().local.push_delimiter(Delimiter::Parenthesis); probe.input().local.push_stop_set(stops); probe.input().local.push_expression_delimited_owner(ExpressionDelimitedOwner::ProjectionTuple); });
    let opening = consume_direct_trivia(committed); committed.emit_trivia(&opening);
    let layout = committed.probe(|probe| LayoutDelimitedFrame::after_opening_trivia(incoming_base, &opening, probe.input().local.line().line_indent)); committed.probe(|probe| push_layout_delimited_baseline(layout, probe.input()));
    commit_projection_items(table, committed, layout, ProjectionKind::Tuple);
    match commit_parenthesized_close_for_owner(committed, GrammarRole::ClosingDelimiter { owner: ConstructRole::ProjectionTupleTail, delimiter: Delimiter::Parenthesis }) {
        ParenthesizedClose::Matched(close) => committed.token(SyntaxKind::RParen, close),
        ParenthesizedClose::Missing { .. } => emit_projection_close_missing(committed, ConstructRole::ProjectionTupleTail, Delimiter::Parenthesis),
    }
    committed.probe(|probe| { pop_layout_delimited_baseline(layout, probe.input()); assert_eq!(probe.input().local.pop_expression_delimited_owner(), Some(ExpressionDelimitedOwner::ProjectionTuple)); assert_eq!(probe.input().local.pop_stop_set(), Some(stops)); assert_eq!(probe.input().local.pop_delimiter(), Some(Delimiter::Parenthesis)); }); committed.finish_node();
}

fn commit_projection_record_tail<'parse, 'source, 'local, E, O>(table: &OperatorTable, leading: TriviaRun, dot: Range<usize>, open: Range<usize>, committed: &mut Committed<'parse, 'source, 'local, E, O>)
where E: ErrorSink<usize>, O: CommitOutput<'source>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    committed.emit_trivia(&leading); committed.start_node(SyntaxKind::ProjectionRecordTail); committed.token(SyntaxKind::Dot, dot); committed.token(SyntaxKind::LBrace, open);
    let incoming_base = committed.probe(|probe| probe.input().local.indentation_baseline().map_or(0, |baseline| baseline.column));
    let stops = committed.probe(|probe| active_stop_set(probe.input()).with(StopKind::Comma).with(StopKind::Semicolon).with(StopKind::RightBrace));
    committed.probe(|probe| { probe.input().local.push_delimiter(Delimiter::Brace); probe.input().local.push_stop_set(stops); probe.input().local.push_expression_delimited_owner(ExpressionDelimitedOwner::ProjectionRecord); });
    let opening = consume_direct_trivia(committed); committed.emit_trivia(&opening);
    let layout = committed.probe(|probe| LayoutDelimitedFrame::after_opening_trivia(incoming_base, &opening, probe.input().local.line().line_indent)); committed.probe(|probe| push_layout_delimited_baseline(layout, probe.input()));
    commit_projection_items(table, committed, layout, ProjectionKind::Record);
    match commit_record_projection_close(committed) {
        IndexClose::Matched(close) => committed.token(SyntaxKind::RBrace, close),
        IndexClose::Missing => emit_projection_close_missing(committed, ConstructRole::ProjectionRecordTail, Delimiter::Brace),
    }
    committed.probe(|probe| { pop_layout_delimited_baseline(layout, probe.input()); assert_eq!(probe.input().local.pop_expression_delimited_owner(), Some(ExpressionDelimitedOwner::ProjectionRecord)); assert_eq!(probe.input().local.pop_stop_set(), Some(stops)); assert_eq!(probe.input().local.pop_delimiter(), Some(Delimiter::Brace)); }); committed.finish_node();
}

#[derive(Clone, Copy)]
enum ProjectionKind { Tuple, Record }

fn commit_projection_items<'parse, 'source, 'local, E, O>(table: &OperatorTable, committed: &mut Committed<'parse, 'source, 'local, E, O>, layout: LayoutDelimitedFrame, kind: ProjectionKind)
where E: ErrorSink<usize>, O: CommitOutput<'source>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    let close_pending = |committed: &mut Committed<'parse, 'source, 'local, E, O>| match kind { ProjectionKind::Tuple => parenthesized_close_pending(committed), ProjectionKind::Record => record_projection_close_pending(committed) };
    if close_pending(committed) { return; }
    loop {
        let marker = matches!(kind, ProjectionKind::Record).then(|| committed.probe(|probe| probe.input().run(scan_exact_dot_dot))).flatten();
        if let Some(marker) = marker {
            committed.start_node(SyntaxKind::ProjectionRecordSpreadItem);
            committed.token(SyntaxKind::DotDot, marker);
            let trivia = consume_direct_trivia(committed); committed.emit_trivia(&trivia);
            if parse_direct_operator_chain(table, LeadingTrivia::None, committed).is_none() {
                if projection_item_error_retry(table, committed, ExpressionRole::ProjectionRecordSpreadRhs) {
                    parse_direct_operator_chain(table, LeadingTrivia::None, committed).expect("a retried spread rhs must commit");
                } else { emit_projection_missing(committed, ExpressionRole::ProjectionRecordSpreadRhs, ExpectedSyntax::Expression); }
            }
            committed.finish_node();
        } else if parse_direct_operator_chain(table, LeadingTrivia::None, committed).is_none() {
            let role = match kind { ProjectionKind::Tuple => ExpressionRole::ProjectionTupleItem, ProjectionKind::Record => ExpressionRole::ProjectionRecordItem };
            if projection_item_error_retry(table, committed, role) {
                parse_direct_operator_chain(table, LeadingTrivia::None, committed).expect("a retried projection item must commit");
            } else { emit_projection_missing(committed, role, ExpectedSyntax::Expression); }
        }
        let trivia = consume_direct_trivia(committed); committed.emit_trivia(&trivia);
        if let Some(separator) = commit_call_separator(committed) { committed.token(if separator.0 { SyntaxKind::Semicolon } else { SyntaxKind::Comma }, separator.1); let trailing = consume_direct_trivia(committed); committed.emit_trivia(&trailing); if close_pending(committed) { break; } continue; }
        if close_pending(committed) { break; }
        if committed.probe(|probe| layout.boundary_after_trivia(&trivia, probe.input().local.line().line_indent)) == LayoutDelimitedBoundary::ImplicitNewline { continue; }
        let separator_role = match kind { ProjectionKind::Tuple => ExpressionRole::ProjectionTupleSeparator, ProjectionKind::Record => ExpressionRole::ProjectionRecordSeparator };
        if parenthesized_element_pending(table, committed) { emit_projection_missing(committed, separator_role, ExpectedSyntax::DelimitedSequenceSeparator); continue; }
        break;
    }
}

fn projection_item_error_retry<'parse, 'source, 'local, E, O>(table: &OperatorTable, committed: &mut Committed<'parse, 'source, 'local, E, O>, role: ExpressionRole) -> bool
where E: ErrorSink<usize>, O: CommitOutput<'source>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    let recovered = committed.probe(|probe| {
        let start = probe.input().pos(); let mut end = start;
        loop { let i = probe.input(); let Some(character) = i.input.remainder().chars().next() else { return None; };
            if matches!(character, ')' | ']' | '}' | ',' | ';') { return None; }
            i.input.next()?; end = i.pos(); let mut line = i.local.line(); line.at_line_start = false; i.local.set_line(line);
            if direct_expression_nud_candidate(table, LeadingTrivia::None, probe) { return Some(start..end); }
        }
    });
    let Some(range) = recovered else { return false; }; emit_projection_error(committed, role, range); true
}

fn record_projection_close_pending<'parse, 'source, 'local, E, O>(committed: &mut Committed<'parse, 'source, 'local, E, O>) -> bool
where E: ErrorSink<usize>, O: CommitOutput<'source>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{ committed.probe(|probe| { let i = probe.input(); let checkpoint = i.checkpoint(); let pending = i.run(recognize_record_projection_close).is_some(); i.rollback(checkpoint); pending }) }

fn commit_record_projection_close<'parse, 'source, 'local, E, O>(committed: &mut Committed<'parse, 'source, 'local, E, O>) -> IndexClose
where E: ErrorSink<usize>, O: CommitOutput<'source>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    loop {
        if committed.probe(|probe| probe.input().input.remainder().is_empty() || matches!(probe.input().input.remainder().chars().next(), Some(';'))) { return IndexClose::Missing; }
        if let Some(punctuation) = committed.probe(|probe| probe.input().run(scan_punctuation)) {
            if punctuation.kind() == PunctuationKind::Close(Delimiter::Brace) { return IndexClose::Matched(punctuation.range()); }
            emit_projection_close_error(committed, punctuation.range(), punctuation.kind()); continue;
        }
        let range = committed.probe(|probe| { let start = probe.input().pos(); let mut end = start; loop { let i = probe.input(); let Some(character) = i.input.remainder().chars().next() else { return (start < end).then_some(start..end); }; if matches!(character, ')' | ']' | '}' | ';') { return (start < end).then_some(start..end); } i.input.next()?; end = i.pos(); } }).expect("record close recovery consumes invalid source");
        emit_projection_close_error(committed, range, PunctuationKind::Close(Delimiter::Brace));
    }
}

fn commit_index_tail<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    open: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>, O: CommitOutput<'source>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::IndexTail);
    committed.token(SyntaxKind::LBracket, open);
    let incoming_base = committed.probe(|probe| probe.input().local.indentation_baseline().map_or(0, |baseline| baseline.column));
    let stops = committed.probe(|probe| active_stop_set(probe.input()).with(StopKind::Comma).with(StopKind::Semicolon).with(StopKind::RightBracket));
    committed.probe(|probe| { probe.input().local.push_delimiter(Delimiter::Bracket); probe.input().local.push_stop_set(stops); probe.input().local.push_expression_delimited_owner(ExpressionDelimitedOwner::Index); });
    let opening = consume_direct_trivia(committed); committed.emit_trivia(&opening);
    let layout = committed.probe(|probe| LayoutDelimitedFrame::after_opening_trivia(incoming_base, &opening, probe.input().local.line().line_indent));
    committed.probe(|probe| push_layout_delimited_baseline(layout, probe.input()));
    if !index_close_pending(committed) {
        loop {
            if parse_direct_operator_chain(table, LeadingTrivia::None, committed).is_none() {
                if index_item_error_retry(table, committed) {
                    parse_direct_operator_chain(table, LeadingTrivia::None, committed)
                        .expect("a retried index item must commit its shared NUD candidate");
                } else {
                    emit_index_missing(committed, ExpressionRole::IndexItem, ExpectedSyntax::Expression);
                }
            }
            let trivia = consume_direct_trivia(committed); committed.emit_trivia(&trivia);
            if let Some(separator) = commit_call_separator(committed) {
                committed.token(if separator.0 { SyntaxKind::Semicolon } else { SyntaxKind::Comma }, separator.1);
                let trailing = consume_direct_trivia(committed); committed.emit_trivia(&trailing);
                if index_close_pending(committed) { break; }
                continue;
            }
            if index_close_pending(committed) { break; }
            let boundary = committed.probe(|probe| layout.boundary_after_trivia(&trivia, probe.input().local.line().line_indent));
            if boundary == LayoutDelimitedBoundary::ImplicitNewline { continue; }
            if boundary == LayoutDelimitedBoundary::None && parenthesized_element_pending(table, committed) {
                emit_index_missing(committed, ExpressionRole::IndexSeparator, ExpectedSyntax::DelimitedSequenceSeparator);
                continue;
            }
            break;
        }
    }
    match commit_index_close(committed) {
        IndexClose::Matched(close) => committed.token(SyntaxKind::RBracket, close),
        IndexClose::Missing => emit_index_close_missing(committed),
    }
    committed.probe(|probe| { pop_layout_delimited_baseline(layout, probe.input()); assert_eq!(probe.input().local.pop_expression_delimited_owner(), Some(ExpressionDelimitedOwner::Index)); assert_eq!(probe.input().local.pop_stop_set(), Some(stops)); assert_eq!(probe.input().local.pop_delimiter(), Some(Delimiter::Bracket)); });
    committed.finish_node();
}

fn index_item_error_retry<'parse, 'source, 'local, E, O>(table: &OperatorTable, committed: &mut Committed<'parse, 'source, 'local, E, O>) -> bool
where E: ErrorSink<usize>, O: CommitOutput<'source>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    let recovered = committed.probe(|probe| {
        let start = probe.input().pos(); let mut end = start;
        loop {
            let i = probe.input(); let Some(character) = i.input.remainder().chars().next() else { return None; };
            if matches!(character, ')' | ']' | '}' | ',' | ';') { return None; }
            i.input.next()?; end = i.pos();
            let mut line = i.local.line(); line.at_line_start = false; i.local.set_line(line);
            if direct_expression_nud_candidate(table, LeadingTrivia::None, probe) { return Some(start..end); }
        }
    });
    let Some(range) = recovered else { return false; };
    emit_index_error(committed, ExpressionRole::IndexItem, range);
    true
}

fn call_argument_error_retry<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where E: ErrorSink<usize>, O: CommitOutput<'source>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    let recovered = committed.probe(|probe| {
        let start = probe.input().pos(); let mut end = start;
        loop {
            let i = probe.input();
            let Some(character) = i.input.remainder().chars().next() else { return None; };
            if matches!(character, ')' | ']' | '}' | ',' | ';') { return None; }
            i.input.next()?; end = i.pos();
            let mut line = i.local.line(); line.at_line_start = false; i.local.set_line(line);
            if direct_expression_nud_candidate(table, LeadingTrivia::None, probe) { return Some(start..end); }
        }
    });
    let Some(range) = recovered else { return false; };
    emit_call_error(committed, ExpressionRole::CallArgument, range);
    true
}

fn commit_call_separator<'parse, 'source, 'local, E, O>(committed: &mut Committed<'parse, 'source, 'local, E, O>) -> Option<(bool, Range<usize>)>
where E: ErrorSink<usize>, O: CommitOutput<'source>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input(); let checkpoint = i.checkpoint();
        let separator = i.run(scan_punctuation).and_then(|punctuation| match punctuation.kind() { PunctuationKind::Comma => Some((false, punctuation.range())), PunctuationKind::Semicolon => Some((true, punctuation.range())), _ => None });
        if separator.is_none() { i.rollback(checkpoint); }
        separator
    })
}

fn path_segment_kind(word: WordSpan<'_>) -> SyntaxKind {
    match path_segment(word) {
        PathSegment::Identifier(_) => SyntaxKind::Identifier,
        PathSegment::SigilIdentifier(_) => SyntaxKind::SigilIdentifier,
    }
}

fn leading_trivia(trivia: &TriviaRun) -> LeadingTrivia {
    if trivia.is_empty() {
        LeadingTrivia::None
    } else {
        LeadingTrivia::Present
    }
}

fn parse_direct_operator_chain<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    leading: LeadingTrivia,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<ParsedExpression<O::Checkpoint>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = committed_position(committed);
    let nud = committed.probe(|probe| probe_nud(table, leading, probe));
    if nud.is_none() {
        let (range, trailing) = committed.probe(|probe| {
            let checkpoint = probe.input().checkpoint();
            let recovered = probe_dangling_prefix(table, probe);
            if recovered.is_none() {
                probe.input().rollback(checkpoint);
            }
            recovered
        })?;
        cut_after_acceptance(committed);
        committed.start_node(SyntaxKind::OperatorChain);
        emit_operator_range(committed, SyntaxKind::PrefixOperatorUse, range);
        committed.emit_trivia(&trailing);
        emit_expression_missing(committed);
        committed.finish_node();
        return Some(ParsedExpression::new(start..committed_position(committed)));
    }
    committed.start_node(SyntaxKind::OperatorChain);
    commit_direct_operand_slot_from(table, nud.expect("checked above"), committed)?;
    loop {
        if let Some(led) = committed.probe(|probe| probe_led(table, probe)) {
            cut_after_acceptance(committed);
            match led {
                LedRecognition::Infix { leading, operator } => {
                    committed.emit_trivia(&leading);
                    emit_operator_use(committed, SyntaxKind::InfixOperatorUse, &operator);
                    committed.emit_trivia(operator.trailing_trivia());
                    if commit_direct_operand_slot(table, committed, LeadingTrivia::None).is_none() {
                        emit_expression_missing(committed);
                        break;
                    }
                }
                LedRecognition::Suffix { leading, operator } => {
                    committed.emit_trivia(&leading);
                    emit_operator_use(committed, SyntaxKind::SuffixOperatorUse, &operator);
                    committed.emit_trivia(operator.trailing_trivia());
                }
            }
            continue;
        }

        if let Some(tail) = committed.probe(|probe| probe.input().run(recognize_fixed_postfix)) {
            cut_after_acceptance(committed);
            commit_fixed_postfix_tail(table, tail, committed);
            continue;
        }

        if let Some(separator) = committed.probe(|probe| probe.input().run(from_fn(|i| recognize_ml_argument(table, i)))) {
            cut_after_acceptance(committed);
            committed.emit_trivia(&separator);
            committed.start_node(SyntaxKind::MlArgument);
            let previous = committed.probe(|probe| { let previous = probe.input().local.ml_arg(); probe.input().local.set_ml_arg(true); previous });
            if parse_direct_operator_chain(table, LeadingTrivia::None, committed).is_none() {
                emit_call_missing(committed, ExpressionRole::MlArgument, ExpectedSyntax::Expression);
            }
            committed.probe(|probe| probe.input().local.set_ml_arg(previous));
            committed.finish_node();
            continue;
        }

        if let Some(colon) = committed.probe(|probe| {
            probe.input().run(recognize_colon_application_tail)
        }) {
            cut_after_acceptance(committed);
            commit_colon_application_tail(table, colon, committed);
            break;
        }
        break;
    }
    if let Some((leading, range, trailing)) = committed.probe(|probe| {
        let checkpoint = probe.input().checkpoint();
        let recovered = probe_dangling_infix(table, probe);
        if recovered.is_none() {
            probe.input().rollback(checkpoint);
        }
        recovered
    }) {
        cut_after_acceptance(committed);
        committed.emit_trivia(&leading);
        emit_operator_range(committed, SyntaxKind::InfixOperatorUse, range);
        committed.emit_trivia(&trailing);
        emit_expression_missing(committed);
    }
    let end = committed_position(committed);
    committed.finish_node();
    Some(ParsedExpression::new(start..end))
}

/// Emits an accepted terminal colon tail. The target remains a sibling of this
/// node in the enclosing flat chain; only the colon and its RHS live here.
fn commit_colon_application_tail<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    colon: ColonApplicationRecognition,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.emit_trivia(&colon.leading);
    committed.start_node(SyntaxKind::ColonApplicationTail);
    committed.token(SyntaxKind::Colon, colon.colon);
    match colon.rhs {
        ColonApplicationRhsRecognition::WrongIndent => {
            emit_colon_application_missing(committed, ColonApplicationRole::Rhs);
        }
        ColonApplicationRhsRecognition::Indented {
            opening_trivia,
            base_indent,
            block_indent,
        } => commit_indented_statement_block(
            table,
            opening_trivia,
            base_indent,
            block_indent,
            committed,
        ),
        ColonApplicationRhsRecognition::Inline { trivia } => {
            committed.emit_trivia(&trivia);
            let outer_owns_sequence = committed.probe(|probe| {
                outer_owns_inline_argument_sequence(probe.input())
            });
            if outer_owns_sequence {
                commit_colon_inline_argument(
                    table,
                    leading_trivia(&trivia),
                    ColonApplicationRole::Rhs,
                    committed,
                );
            } else {
                let layout = committed.probe(|probe| LayoutDelimitedFrame::inline(
                    probe.input().local.indentation_baseline().map_or(0, |baseline| baseline.column),
                ));
                let stop_set = committed.probe(|probe| active_stop_set(probe.input()).with(StopKind::Comma));
                committed.probe(|probe| probe.input().local.push_stop_set(stop_set));
                commit_colon_inline_argument(
                    table,
                    leading_trivia(&trivia),
                    ColonApplicationRole::Rhs,
                    committed,
                );

                while let Some(separator) = committed.probe(|probe| {
                    let i = probe.input();
                    let checkpoint = i.checkpoint();
                    let leading = consume_trivia(i).expect("trivia scanning is total");
                    if let Some(comma) = i.run(recognize_parenthesized_comma) {
                        return Some(InlineColonSeparator::Comma {
                            leading,
                            comma,
                            trailing: consume_trivia(i).expect("trivia scanning is total"),
                        });
                    }
                    if layout.boundary_after_trivia(&leading, i.local.line().line_indent)
                        == LayoutDelimitedBoundary::ImplicitNewline
                    {
                        return Some(InlineColonSeparator::Newline(leading));
                    }
                    i.rollback(checkpoint);
                    None
                }) {
                    match separator {
                        InlineColonSeparator::Comma { leading, comma, trailing } => {
                            committed.emit_trivia(&leading);
                            committed.token(SyntaxKind::Comma, comma);
                            committed.emit_trivia(&trailing);
                            commit_colon_inline_argument(
                                table,
                                leading_trivia(&trailing),
                                ColonApplicationRole::InlineArgument,
                                committed,
                            );
                        }
                        InlineColonSeparator::Newline(trivia) => {
                            committed.emit_trivia(&trivia);
                            commit_colon_inline_argument(
                                table,
                                LeadingTrivia::None,
                                ColonApplicationRole::InlineArgument,
                                committed,
                            );
                        }
                    }
                }
                committed.probe(|probe| assert_eq!(probe.input().local.pop_stop_set(), Some(stop_set)));
            }
        }
    }
    committed.finish_node();
}

/// Parses the expression-statement subset of a colon-introduced block.  The
/// root statement dispatcher remains intentionally separate: colon bodies do
/// not yet own declarations.
fn parse_indented_statement_block<'source, E>(
    table: &OperatorTable,
    opening_trivia: TriviaRun,
    base_indent: usize,
    block_indent: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> IndentedStatementBlock<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_indented_statement_block_with_options(
        table,
        opening_trivia,
        base_indent,
        block_indent,
        IndentedStatementBlockOptions::default(),
        i,
    )
}

fn parse_indented_statement_block_with_options<'source, E>(
    table: &OperatorTable,
    opening_trivia: TriviaRun,
    base_indent: usize,
    block_indent: usize,
    options: IndentedStatementBlockOptions,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> IndentedStatementBlock<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = opening_trivia.range().start;
    let scope = push_indented_statement_block_scope(i, block_indent);
    let statements = parse_statement_sequence(
        table,
        StatementSequencePolicy::Indented {
            block_indent,
            options,
        },
        i,
    );

    let end = i.pos();
    pop_indented_statement_block_scope(i, scope, block_indent);
    IndentedStatementBlock {
        base_indent,
        block_indent,
        statements,
        range: start..end,
    }
}

/// The two current statement-sequence owners deliberately share this closed
/// policy rather than exposing a general block-parser abstraction.  The
/// indented wrapper still owns layout entry/exit; the brace wrapper will own
/// delimiters and closing recovery.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum StatementSequencePolicy {
    Indented {
        block_indent: usize,
        options: IndentedStatementBlockOptions,
    },
    BracedPrimary,
}

/// Parsed statements are the AST-side projection of the shared sequence core.
struct ParsedStatementSequence<'source> {
    statements: Vec<Recovered<Statement<'source>>>,
}

fn parse_statement_sequence<'source, E>(
    table: &OperatorTable,
    policy: StatementSequencePolicy,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Vec<Recovered<Statement<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if matches!(policy, StatementSequencePolicy::BracedPrimary) {
        return parse_braced_statement_sequence(table, i);
    }
    let StatementSequencePolicy::Indented { block_indent, options } = policy else {
        unreachable!("braced policy returns above");
    };
    let mut parsed = ParsedStatementSequence {
        statements: Vec::new(),
    };

    if let Some(expression) = i.run(from_fn(|i| parse_operator_chain(table, i))) {
        parsed.statements.push(Recovered::Complete(Statement { expression }));
        while !options.companion_stop(i) {
            let Some(separator) = recognize_statement_sequence_separator(i, policy) else { break; };
            if separator.is_semicolon() && indented_block_terminal_boundary(i, block_indent) {
                break;
            }
            let Some(expression) = i.run(from_fn(|i| parse_operator_chain(table, i))) else {
                parsed.statements.push(Recovered::Incomplete);
                break;
            };
            parsed.statements.push(Recovered::Complete(Statement { expression }));
        }
    } else {
        parsed.statements.push(Recovered::Incomplete);
    }

    parsed.statements
}

fn parse_braced_statement_block_expression<'source, E>(
    table: &OperatorTable,
    open: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> BracedStatementBlockExpression<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let scope = push_braced_statement_block_scope(i);
    consume_trivia(i).expect("trivia scanning is total");
    let statements = parse_statement_sequence(table, StatementSequencePolicy::BracedPrimary, i);
    consume_trivia(i).expect("trivia scanning is total");
    let close = i
        .run(recognize_braced_statement_block_close)
        .map_or(Recovered::Incomplete, Recovered::Complete);
    let end = match &close {
        Recovered::Complete(range) => range.end,
        Recovered::Incomplete => i.pos(),
    };
    pop_braced_statement_block_scope(i, scope);
    BracedStatementBlockExpression {
        open: open.clone(),
        statements,
        close,
        range: open.start..end,
    }
}

fn parse_braced_statement_sequence<'source, E>(
    table: &OperatorTable,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Vec<Recovered<Statement<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if braced_statement_block_close_pending(i) {
        return Vec::new();
    }
    let mut statements = Vec::new();
    let Some(expression) = i.run(from_fn(|i| parse_operator_chain(table, i))) else {
        return statements;
    };
    statements.push(Recovered::Complete(Statement { expression }));
    loop {
        if braced_statement_block_close_pending(i) {
            break;
        }
        let Some(_) = recognize_statement_sequence_separator(i, StatementSequencePolicy::BracedPrimary) else {
            break;
        };
        if braced_statement_block_close_pending(i) {
            break;
        }
        let Some(expression) = i.run(from_fn(|i| parse_operator_chain(table, i))) else {
            statements.push(Recovered::Incomplete);
            break;
        };
        statements.push(Recovered::Complete(Statement { expression }));
    }
    statements
}

fn braced_statement_block_close_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    consume_trivia(i).expect("trivia scanning is total");
    let pending = i.run(recognize_braced_statement_block_close).is_some();
    i.rollback(checkpoint);
    pending
}

fn recognize_braced_statement_separator<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<StatementSequenceSeparator>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = consume_trivia(i)?;
    if trivia_has_physical_newline(&trivia) {
        return Some(StatementSequenceSeparator::Newline { trivia });
    }
    let Some(punctuation) = i.run(scan_punctuation) else {
        i.rollback(checkpoint);
        return None;
    };
    let kind = punctuation.kind();
    if !matches!(kind, PunctuationKind::Comma | PunctuationKind::Semicolon) {
        i.rollback(checkpoint);
        return None;
    }
    let trailing_trivia = consume_trivia(i)?;
    Some(match kind {
        PunctuationKind::Comma => StatementSequenceSeparator::Comma {
            leading_trivia: trivia,
            range: punctuation.range(),
            trailing_trivia,
        },
        PunctuationKind::Semicolon => StatementSequenceSeparator::Semicolon {
            leading_trivia: trivia,
            range: punctuation.range(),
            trailing_trivia,
        },
        _ => unreachable!("checked brace separator punctuation"),
    })
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum StatementSequenceSeparator {
    Newline { trivia: TriviaRun },
    Semicolon {
        leading_trivia: TriviaRun,
        range: Range<usize>,
        trailing_trivia: TriviaRun,
    },
    Comma {
        leading_trivia: TriviaRun,
        range: Range<usize>,
        trailing_trivia: TriviaRun,
    },
}

impl StatementSequenceSeparator {
    fn is_semicolon(&self) -> bool {
        matches!(self, Self::Semicolon { .. })
    }

    fn following_leading_trivia(&self) -> LeadingTrivia {
        match self {
            Self::Newline { trivia } => leading_trivia(trivia),
            Self::Semicolon { trailing_trivia, .. } | Self::Comma { trailing_trivia, .. } => {
                leading_trivia(trailing_trivia)
            }
        }
    }
}

/// Consumes only a separator whose final physical line is the block's own
/// indentation.  A dedent probe rolls its trivia back so the enclosing owner
/// retains it.
fn recognize_statement_sequence_separator<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
    policy: StatementSequencePolicy,
) -> Option<StatementSequenceSeparator>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if matches!(policy, StatementSequencePolicy::BracedPrimary) {
        return recognize_braced_statement_separator(i);
    }
    let StatementSequencePolicy::Indented { block_indent, .. } = policy else {
        unreachable!("braced policy returns above");
    };
    let checkpoint = i.checkpoint();
    let trivia = consume_trivia(i)?;
    if trivia_has_physical_newline(&trivia) {
        if i.local.line().line_indent == block_indent {
            return Some(StatementSequenceSeparator::Newline { trivia });
        }
        i.rollback(checkpoint);
        return None;
    }
    let Some(punctuation) = i.run(scan_punctuation) else {
        i.rollback(checkpoint);
        return None;
    };
    if punctuation.kind() != PunctuationKind::Semicolon {
        i.rollback(checkpoint);
        return None;
    }
    let trailing_checkpoint = i.checkpoint();
    let trailing_trivia = consume_trivia(i)?;
    if trivia_has_physical_newline(&trailing_trivia)
        && i.local.line().line_indent < block_indent
    {
        i.rollback(trailing_checkpoint);
        return Some(StatementSequenceSeparator::Semicolon {
            leading_trivia: trivia,
            range: punctuation.range(),
            trailing_trivia: TriviaRun::empty_at(punctuation.range().end),
        });
    }
    Some(StatementSequenceSeparator::Semicolon {
        leading_trivia: trivia,
        range: punctuation.range(),
        trailing_trivia,
    })
}

fn indented_block_terminal_boundary<E>(i: &mut SynIn<E>, block_indent: usize) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if i.input.remainder().is_empty() {
        return true;
    }
    if matches!(i.input.remainder().chars().next(), Some(')' | ']' | '}')) {
        return true;
    }
    let checkpoint = i.checkpoint();
    let trivia = consume_trivia(i).expect("trivia scanning is total");
    let terminal = trivia_has_physical_newline(&trivia)
        && i.local.line().line_indent < block_indent;
    i.rollback(checkpoint);
    terminal
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct IndentedStatementBlockScope {
    inline: bool,
    ml_arg: bool,
    stop_set: StopSet,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct BracedStatementBlockScope {
    inline: bool,
    ml_arg: bool,
}

fn braced_statement_block_stop_set() -> StopSet {
    StopSet::default()
        .with(StopKind::Comma)
        .with(StopKind::Semicolon)
        .with(StopKind::RightBrace)
}

fn push_braced_statement_block_scope<E>(i: &mut SynIn<E>) -> BracedStatementBlockScope
where
    E: ErrorSink<usize>,
{
    let scope = BracedStatementBlockScope {
        inline: i.local.inline(),
        ml_arg: i.local.ml_arg(),
    };
    i.local.push_delimiter(Delimiter::Brace);
    i.local.set_inline(true);
    i.local.set_ml_arg(false);
    i.local.push_stop_set(braced_statement_block_stop_set());
    scope
}

fn pop_braced_statement_block_scope<E>(i: &mut SynIn<E>, scope: BracedStatementBlockScope)
where
    E: ErrorSink<usize>,
{
    assert_eq!(i.local.pop_stop_set(), Some(braced_statement_block_stop_set()));
    i.local.set_inline(scope.inline);
    i.local.set_ml_arg(scope.ml_arg);
    assert_eq!(i.local.pop_delimiter(), Some(Delimiter::Brace));
}

fn push_indented_statement_block_scope<E>(
    i: &mut SynIn<E>,
    block_indent: usize,
) -> IndentedStatementBlockScope
where
    E: ErrorSink<usize>,
{
    let scope = IndentedStatementBlockScope {
        inline: i.local.inline(),
        ml_arg: i.local.ml_arg(),
        stop_set: active_stop_set(i),
    };
    i.local.push_indentation_baseline(IndentationBaseline {
        column: block_indent,
        kind: IndentationBaselineKind::Block,
    });
    i.local.set_inline(false);
    i.local.set_ml_arg(false);
    i.local.push_stop_set(scope.stop_set);
    scope
}

fn pop_indented_statement_block_scope<E>(
    i: &mut SynIn<E>,
    scope: IndentedStatementBlockScope,
    block_indent: usize,
) where
    E: ErrorSink<usize>,
{
    assert_eq!(i.local.pop_stop_set(), Some(scope.stop_set));
    i.local.set_inline(scope.inline);
    i.local.set_ml_arg(scope.ml_arg);
    assert_eq!(
        i.local.pop_indentation_baseline(),
        Some(IndentationBaseline {
            column: block_indent,
            kind: IndentationBaselineKind::Block,
        })
    );
}

fn commit_indented_statement_block<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    opening_trivia: TriviaRun,
    _base_indent: usize,
    block_indent: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    commit_indented_statement_block_with_options(
        table,
        opening_trivia,
        _base_indent,
        block_indent,
        IndentedStatementBlockOptions::default(),
        committed,
    );
}

/// Shared colon-body block loop.  Owners can supply a companion-stop policy
/// without copying statement/separator/recovery ownership.
fn commit_indented_statement_block_with_options<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    opening_trivia: TriviaRun,
    _base_indent: usize,
    block_indent: usize,
    options: IndentedStatementBlockOptions,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::IndentedStatementBlock);
    committed.emit_trivia(&opening_trivia);
    let scope = committed.probe(|probe| {
        push_indented_statement_block_scope(probe.input(), block_indent)
    });

    let policy = StatementSequencePolicy::Indented {
        block_indent,
        options,
    };
    commit_statement_sequence(table, policy, committed);

    committed.probe(|probe| {
        pop_indented_statement_block_scope(probe.input(), scope, block_indent)
    });
    committed.finish_node();
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct IndentedStatementBlockOptions {
    companion_stop: Option<IndentedBlockCompanionStop>,
}

impl IndentedStatementBlockOptions {
    fn if_arm(base_indent: usize) -> Self {
        Self { companion_stop: Some(IndentedBlockCompanionStop::ArmKeyword { base_indent }) }
    }

    /// This is deliberately a sink-free, owner-provided hook.  The generic
    /// block loop knows neither `if` nor its arm grammar; it only asks whether
    /// its owner retains the following boundary.
    fn companion_stop<'source, E>(self, i: &mut SynIn<'_, 'source, '_, E>) -> bool
    where
        E: ErrorSink<usize>,
        Unexpected<char>: Into<E::Error>,
        UnexpectedEndOfInput: Into<E::Error>,
    {
        let Some(stop) = self.companion_stop else { return false; };
        stop.matches(i)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum IndentedBlockCompanionStop {
    ArmKeyword { base_indent: usize },
}

impl IndentedBlockCompanionStop {
    fn matches<'source, E>(self, i: &mut SynIn<'_, 'source, '_, E>) -> bool
    where
        E: ErrorSink<usize>,
        Unexpected<char>: Into<E::Error>,
        UnexpectedEndOfInput: Into<E::Error>,
    {
        let checkpoint = i.checkpoint();
        let result = match self {
            Self::ArmKeyword { base_indent } => {
                let trivia = consume_trivia(i).expect("trivia scanning is total");
                trivia_has_physical_newline(&trivia)
                    && i.local.line().line_indent >= base_indent
                    && matches!(i.run(scan_word).map(|word| word.text()), Some("elsif" | "else"))
            }
        };
        i.rollback(checkpoint);
        result
    }
}

fn commit_statement_sequence<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    policy: StatementSequencePolicy,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if matches!(policy, StatementSequencePolicy::BracedPrimary) {
        commit_braced_statement_sequence(table, committed);
        return;
    }
    let StatementSequencePolicy::Indented {
        block_indent,
        options,
    } = policy else {
        unreachable!("braced policy returns above");
    };
    commit_statement_sequence_statement(table, policy, LeadingTrivia::None, committed);
    while !committed.probe(|probe| options.companion_stop(probe.input())) {
        let Some(separator) = commit_statement_sequence_separator(policy, committed) else { break; };
        if separator.is_semicolon()
            && committed.probe(|probe| indented_block_terminal_boundary(probe.input(), block_indent))
        {
            break;
        }
        commit_statement_sequence_statement(
            table,
            policy,
            separator.following_leading_trivia(),
            committed,
        );
    }
}

fn commit_braced_statement_block_expression<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    open: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::BracedStatementBlockExpression);
    committed.token(SyntaxKind::LBrace, open);
    let scope = committed.probe(|probe| push_braced_statement_block_scope(probe.input()));
    let opening_trivia = committed
        .probe(|probe| probe.input().run(scan_trivia))
        .expect("trivia scanning is total");
    committed.emit_trivia(&opening_trivia);
    commit_statement_sequence(table, StatementSequencePolicy::BracedPrimary, committed);
    commit_braced_statement_block_close(committed);
    committed.probe(|probe| pop_braced_statement_block_scope(probe.input(), scope));
    committed.finish_node();
}

fn commit_braced_statement_sequence<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let policy = StatementSequencePolicy::BracedPrimary;
    if braced_statement_slot_absent_boundary(committed) {
        return;
    }
    commit_statement_sequence_statement(table, policy, LeadingTrivia::None, committed);
    loop {
        if braced_close_pending(committed) {
            return;
        }
        if let Some(separator) = commit_statement_sequence_separator(policy, committed) {
            if braced_statement_slot_absent_boundary(committed) {
                return;
            }
            commit_statement_sequence_statement(
                table,
                policy,
                separator.following_leading_trivia(),
                committed,
            );
            continue;
        }
        if let Some(leading) = braced_next_statement_leading(table, committed) {
            emit_braced_statement_separator_missing(committed);
            commit_statement_sequence_statement(table, policy, leading, committed);
            continue;
        }
        return;
    }
}

fn braced_next_statement_leading<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<LeadingTrivia>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let _trivia = committed.probe(|probe| {
        let checkpoint = probe.input().checkpoint();
        let trivia = consume_trivia(probe.input()).expect("trivia scanning is total");
        let leading = leading_trivia(&trivia);
        let candidate = direct_expression_nud_candidate(table, leading, probe);
        probe.input().rollback(checkpoint);
        candidate.then_some(trivia)
    })?;
    let consumed = committed
        .probe(|probe| consume_trivia(probe.input()))
        .expect("the accepted statement-leading trivia remains available");
    committed.emit_trivia(&consumed);
    Some(leading_trivia(&consumed))
}

fn braced_close_pending<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| braced_statement_block_close_pending(probe.input()))
}

fn braced_statement_slot_absent_boundary<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if braced_close_pending(committed) {
        return true;
    }
    committed.probe(|probe| probe.input().input.remainder().is_empty())
}

fn commit_braced_statement_block_close<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let trailing = committed
        .probe(|probe| probe.input().run(scan_trivia))
        .expect("trivia scanning is total");
    committed.emit_trivia(&trailing);
    loop {
        if committed.probe(|probe| probe.input().input.remainder().is_empty()) {
            emit_braced_close_missing(committed);
            return;
        }
        let punctuation = committed.probe(|probe| probe.input().run(scan_punctuation));
        if let Some(punctuation) = punctuation {
            match punctuation.kind() {
                PunctuationKind::Close(Delimiter::Brace) => {
                    committed.token(SyntaxKind::RBrace, punctuation.range());
                    return;
                }
                PunctuationKind::Close(actual @ (Delimiter::Parenthesis | Delimiter::Bracket)) => {
                    emit_braced_close_error(committed, punctuation.range(), actual);
                }
                _ => emit_braced_close_other_error(committed, punctuation.range()),
            }
            continue;
        }
        let range = committed.probe(|probe| {
            let start = probe.input().pos();
            let mut end = start;
            loop {
                let i = probe.input();
                let Some(character) = i.input.remainder().chars().next() else {
                    return (start < end).then_some(start..end);
                };
                if matches!(character, '}' | ')' | ']') {
                    return (start < end).then_some(start..end);
                }
                i.input.next().expect("the scanned brace-close byte exists");
                end = i.pos();
                let mut line = i.local.line();
                line.at_line_start = false;
                i.local.set_line(line);
            }
        });
        if let Some(range) = range {
            emit_braced_close_other_error(committed, range);
        } else {
            emit_braced_close_missing(committed);
            return;
        }
    }
}

fn commit_statement_sequence_statement<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    policy: StatementSequencePolicy,
    leading: LeadingTrivia,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::Statement);
    if parse_direct_operator_chain(table, leading, committed).is_none() {
        match statement_sequence_error_retry(table, policy, committed) {
            Some(true) => {
                parse_direct_operator_chain(table, LeadingTrivia::None, committed)
                    .expect("a retried block statement must commit its shared NUD candidate");
            }
            Some(false) => {}
            None => emit_statement_sequence_missing(policy, committed),
        }
    }
    committed.finish_node();
}

/// A statement recovery records one non-empty invalid episode and retries the
/// same statement slot only when the shared expression start judge finds a
/// later candidate before a block boundary.
fn statement_sequence_error_retry<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    policy: StatementSequencePolicy,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<bool>
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
                return (start < end).then_some((start..end, false));
            };
            if matches!(character, '\r' | '\n' | ')' | ']' | '}' | ';' | ',') {
                return (start < end).then_some((start..end, false));
            }
            i.input.next()?;
            end = i.pos();
            let mut line = i.local.line();
            line.at_line_start = false;
            i.local.set_line(line);
            if direct_expression_nud_candidate(table, LeadingTrivia::None, probe) {
                return Some((start..end, true));
            }
        }
    });
    let Some((range, retry)) = recovered else {
        return None;
    };
    emit_statement_sequence_error(policy, committed, range);
    Some(retry)
}

fn commit_statement_sequence_separator<'parse, 'source, 'local, E, O>(
    policy: StatementSequencePolicy,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<StatementSequenceSeparator>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let separator = committed.probe(|probe| recognize_statement_sequence_separator(probe.input(), policy))?;
    committed.start_node(SyntaxKind::BlockStatementSeparator);
    match &separator {
        StatementSequenceSeparator::Newline { trivia } => committed.emit_trivia(trivia),
        StatementSequenceSeparator::Semicolon {
            leading_trivia,
            range,
            trailing_trivia,
        } => {
            committed.emit_trivia(leading_trivia);
            committed.token(SyntaxKind::Semicolon, range.clone());
            committed.emit_trivia(trailing_trivia);
        }
        StatementSequenceSeparator::Comma {
            leading_trivia,
            range,
            trailing_trivia,
        } => {
            committed.emit_trivia(leading_trivia);
            committed.token(SyntaxKind::Comma, range.clone());
            committed.emit_trivia(trailing_trivia);
        }
    }
    committed.finish_node();
    Some(separator)
}

/// A colon-owned comma makes every following position mandatory; unlike a
/// parenthesized list, a terminal comma has no valid trailing-comma marker.
fn commit_colon_inline_argument<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    leading: LeadingTrivia,
    role: ColonApplicationRole,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if parse_direct_operator_chain(table, leading, committed).is_some() {
        return;
    }
    if colon_inline_argument_error_retry(table, role, committed) {
        parse_direct_operator_chain(table, LeadingTrivia::None, committed)
            .expect("a retried colon argument must commit its shared NUD candidate");
    } else {
        emit_colon_application_missing(committed, role);
    }
}

fn colon_inline_argument_error_retry<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    role: ColonApplicationRole,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
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
                return (start < end).then_some((start..end, false));
            };
            if matches!(character, ')' | ']' | '}' | ';' | ',') {
                return (start < end).then_some((start..end, false));
            }
            i.input.next()?;
            end = i.pos();
            let mut line = i.local.line();
            line.at_line_start = false;
            i.local.set_line(line);
            if direct_expression_nud_candidate(table, LeadingTrivia::None, probe) {
                return Some((start..end, true));
            }
        }
    });
    let Some((range, retry)) = recovered else {
        return false;
    };
    emit_colon_application_error(committed, role, range);
    retry
}

/// Probes a NUD candidate without granting access to the output sink.
fn probe_nud<'parse, 'source, 'local, E>(
    table: &OperatorTable,
    leading: LeadingTrivia,
    probe: &mut Probe<'parse, 'source, 'local, E>,
) -> Option<NudRecognition<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    probe
        .input()
        .run(from_fn(|i| recognize_nud(table, leading, i)))
}

/// Tests whether the current position can begin a direct expression without
/// granting a continuation access to its output sink. Declaration recovery
/// uses this to decide whether an invalid occupying byte can be skipped and
/// the same mandatory value slot retried.
pub(crate) fn direct_expression_nud_candidate<'parse, 'source, 'local, E>(
    table: &OperatorTable,
    leading: LeadingTrivia,
    probe: &mut Probe<'parse, 'source, 'local, E>,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let i = probe.input();
    let checkpoint = i.checkpoint();
    let candidate = i
        .run(from_fn(|i| recognize_nud(table, leading, i)))
        .is_some();
    i.rollback(checkpoint);
    candidate
}

/// Probes a LED candidate and rolls back its trivia with every rejection.
fn probe_led<'parse, 'source, 'local, E>(
    table: &OperatorTable,
    probe: &mut Probe<'parse, 'source, 'local, E>,
) -> Option<LedRecognition<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    probe
        .input()
        .run(from_fn(|i| recognize_led(table, i)))?
}

fn cut_after_acceptance<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.probe(|probe| probe.input().cut());
}

fn commit_case_like_expression<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    family: CaseLikeFamily,
    keyword: WordSpan<'source>,
    base_indent: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where E: ErrorSink<usize>, O: CommitOutput<'source>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(family.expression_kind());
    committed.token(family.keyword_kind(), keyword.range());
    let trivia = consume_direct_trivia(committed); committed.emit_trivia(&trivia);
    if let Some(label) = committed.probe(|probe| probe_case_like_label(probe.input())) {
        committed.start_node(family.label_kind()); committed.token(SyntaxKind::SigilIdentifier, label); committed.finish_node();
        let trivia = consume_direct_trivia(committed); committed.emit_trivia(&trivia);
    }
    let stops = committed.probe(|probe| family.scrutinee_stop(active_stop_set(probe.input())));
    committed.probe(|probe| probe.input().local.push_stop_set(stops));
    committed.start_node(family.scrutinee_kind());
    if parse_direct_operator_chain(table, leading_trivia(&trivia), committed).is_none() { emit_case_like_missing(committed, CaseLikeRole::Scrutinee, ExpectedSyntax::Expression); }
    committed.finish_node();
    committed.probe(|probe| assert_eq!(probe.input().local.pop_stop_set(), Some(stops)));
    let block_trivia = consume_direct_trivia(committed); committed.emit_trivia(&block_trivia);
    if let Some(colon) = committed.probe(|probe| recognize_arm_colon(probe.input())) {
        committed.start_node(family.block_kind()); committed.token(SyntaxKind::Colon, colon);
        let layout = committed.probe(|probe| recognize_introduced_body_layout(base_indent, probe.input()));
        let policy = match layout {
            ArmBodyLayout::Inline { trivia } => { committed.emit_trivia(&trivia); family.inline_policy() }
            ArmBodyLayout::Indented { opening_trivia, block_indent } => { committed.emit_trivia(&opening_trivia); ArmSequencePolicy::Indented { family, base_indent, arm_indent: block_indent } }
            ArmBodyLayout::WrongIndent => { emit_case_like_missing(committed, CaseLikeRole::Arm, ExpectedSyntax::Pattern); committed.finish_node(); committed.finish_node(); return; }
        };
        commit_arm_sequence(table, family, policy, committed);
        committed.finish_node();
    } else if family == CaseLikeFamily::Catch {
        if let Some(open) = committed.probe(|probe| probe.input().run(recognize_braced_statement_block_open)) {
            committed.start_node(SyntaxKind::CatchBlock); committed.token(SyntaxKind::LBrace, open);
            let scope = committed.probe(|probe| push_braced_statement_block_scope(probe.input()));
            let trivia = consume_direct_trivia(committed); committed.emit_trivia(&trivia);
            commit_arm_sequence(table, family, ArmSequencePolicy::CatchBraced, committed);
            let trailing = consume_direct_trivia(committed); committed.emit_trivia(&trailing);
            if let Some(close) = committed.probe(|probe| probe.input().run(recognize_braced_statement_block_close)) { committed.token(SyntaxKind::RBrace, close); } else { emit_case_like_missing(committed, CaseLikeRole::Block, ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Close(Delimiter::Brace))); }
            committed.probe(|probe| pop_braced_statement_block_scope(probe.input(), scope)); committed.finish_node();
        } else { emit_case_like_missing(committed, CaseLikeRole::Block, ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Colon)); }
    } else { emit_case_like_missing(committed, CaseLikeRole::Block, ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Colon)); }
    committed.finish_node();
}

impl CaseLikeFamily {
    fn expression_kind(self) -> SyntaxKind { match self { Self::Case => SyntaxKind::CaseExpression, Self::Catch => SyntaxKind::CatchExpression } }
    fn keyword_kind(self) -> SyntaxKind { match self { Self::Case => SyntaxKind::CaseKw, Self::Catch => SyntaxKind::CatchKw } }
    fn label_kind(self) -> SyntaxKind { match self { Self::Case => SyntaxKind::CaseLabel, Self::Catch => SyntaxKind::CatchLabel } }
    fn scrutinee_kind(self) -> SyntaxKind { match self { Self::Case => SyntaxKind::CaseScrutinee, Self::Catch => SyntaxKind::CatchScrutinee } }
    fn block_kind(self) -> SyntaxKind { match self { Self::Case => SyntaxKind::CaseBlock, Self::Catch => SyntaxKind::CatchBlock } }
    fn arm_kind(self) -> SyntaxKind { match self { Self::Case => SyntaxKind::CaseArm, Self::Catch => SyntaxKind::CatchArm } }
    fn guard_kind(self) -> SyntaxKind { match self { Self::Case => SyntaxKind::CaseGuard, Self::Catch => SyntaxKind::CatchGuard } }
    fn separator_kind(self) -> SyntaxKind { match self { Self::Case => SyntaxKind::CaseArmSeparator, Self::Catch => SyntaxKind::CatchArmSeparator } }
    fn inline_policy(self) -> ArmSequencePolicy { match self { Self::Case => ArmSequencePolicy::CaseInline, Self::Catch => ArmSequencePolicy::CatchInlineSingle } }
    fn scrutinee_stop(self, outer: StopSet) -> StopSet { let stops = outer.with(StopKind::Colon); match self { Self::Case => stops, Self::Catch => stops.with(StopKind::LeftBrace) } }
}

fn probe_case_like_label<'source, E>(i: &mut SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{ let checkpoint = i.checkpoint(); let Some(apostrophe) = i.run(scan_punctuation) else { return None; }; if apostrophe.kind() != PunctuationKind::Apostrophe { i.rollback(checkpoint); return None; } let Some(word) = i.run(scan_word) else { i.rollback(checkpoint); return None; }; Some(apostrophe.range().start..word.range().end) }

fn commit_arm_sequence<'parse, 'source, 'local, E, O>(table: &OperatorTable, family: CaseLikeFamily, policy: ArmSequencePolicy, committed: &mut Committed<'parse, 'source, 'local, E, O>)
where E: ErrorSink<usize>, O: CommitOutput<'source>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    commit_one_arm(table, family, policy, committed);
    while policy_allows_multiple(policy) {
        let checkpoint = committed.probe(|probe| probe.input().checkpoint());
        let trivia = consume_direct_trivia(committed);
        if let Some(comma) = committed.probe(|probe| probe.input().run(recognize_parenthesized_comma)) {
            committed.start_node(family.separator_kind()); committed.emit_trivia(&trivia); committed.token(SyntaxKind::Comma, comma); committed.finish_node();
            let next = consume_direct_trivia(committed); committed.emit_trivia(&next);
            if committed.probe(|probe| arm_sequence_boundary(policy, probe.input())) { return; }
            commit_one_arm(table, family, policy, committed); continue;
        }
        let newline = committed.probe(|probe| policy_newline_separator(policy, &trivia, probe.input()));
        if newline { committed.emit_trivia(&trivia); commit_one_arm(table, family, policy, committed); continue; }
        if committed.probe(|probe| pattern_nud_candidate_input(probe.input())) {
            committed.emit_trivia(&trivia);
            emit_case_like_missing(
                committed,
                CaseLikeRole::Separator,
                ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Comma),
            );
            commit_one_arm(table, family, policy, committed);
            continue;
        }
        committed.probe(|probe| probe.input().rollback(checkpoint)); return;
    }
}

fn commit_one_arm<'parse, 'source, 'local, E, O>(table: &OperatorTable, family: CaseLikeFamily, policy: ArmSequencePolicy, committed: &mut Committed<'parse, 'source, 'local, E, O>)
where E: ErrorSink<usize>, O: CommitOutput<'source>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(family.arm_kind());
    let stops = committed.probe(|probe| { let mut stops = active_stop_set(probe.input()).with(StopKind::Arrow).with(StopKind::ArmGuardIf).with(StopKind::ArmGuardWhere); if family == CaseLikeFamily::Catch { stops = stops.with(StopKind::Comma); } stops });
    committed.probe(|probe| probe.input().local.push_stop_set(stops));
    if parse_direct_pattern(table, LeadingTrivia::None, committed).is_none() { emit_case_like_missing(committed, CaseLikeRole::Pattern, ExpectedSyntax::Pattern); }
    committed.probe(|probe| assert_eq!(probe.input().local.pop_stop_set(), Some(stops)));
    if family == CaseLikeFamily::Catch && let Some(comma) = committed.probe(|probe| probe.input().run(recognize_parenthesized_comma)) {
        committed.token(SyntaxKind::Comma, comma);
        let trivia = consume_direct_trivia(committed); committed.emit_trivia(&trivia);
        let stops = committed.probe(|probe| active_stop_set(probe.input()).with(StopKind::Arrow).with(StopKind::ArmGuardIf).with(StopKind::ArmGuardWhere)); committed.probe(|probe| probe.input().local.push_stop_set(stops));
        if parse_direct_pattern(table, LeadingTrivia::None, committed).is_none() { emit_case_like_missing(committed, CaseLikeRole::Handler, ExpectedSyntax::Pattern); }
        committed.probe(|probe| assert_eq!(probe.input().local.pop_stop_set(), Some(stops)));
    }
    commit_arm_guard(table, family, committed);
    let arrow_trivia = consume_direct_trivia(committed); committed.emit_trivia(&arrow_trivia);
    if let Some(arrow) = committed.probe(|probe| probe.input().run(scan_exact_arrow)) {
        committed.token(SyntaxKind::Arrow, arrow);
        commit_arm_body(table, family, policy, committed);
    } else {
        emit_case_like_missing(committed, CaseLikeRole::Arrow, ExpectedSyntax::Expression);
        if committed.probe(|probe| direct_expression_nud_candidate(table, LeadingTrivia::None, probe)) {
            commit_arm_body(table, family, policy, committed);
        } else {
            commit_case_like_invalid_arrow(committed);
        }
    }
    let checkpoint = committed.probe(|probe| probe.input().checkpoint());
    let terminal_trivia = consume_direct_trivia(committed);
    if let Some(semicolon) = committed.probe(|probe| direct_semicolon(probe.input())) { committed.emit_trivia(&terminal_trivia); committed.token(SyntaxKind::Semicolon, semicolon); } else { committed.probe(|probe| probe.input().rollback(checkpoint)); }
    committed.finish_node();
}

fn commit_arm_guard<'parse, 'source, 'local, E, O>(table: &OperatorTable, family: CaseLikeFamily, committed: &mut Committed<'parse, 'source, 'local, E, O>)
where E: ErrorSink<usize>, O: CommitOutput<'source>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    let Some((trivia, keyword)) = committed.probe(|probe| probe_arm_guard(probe.input())) else { return; };
    committed.emit_trivia(&trivia); committed.start_node(family.guard_kind());
    committed.token(if keyword.text() == "if" { SyntaxKind::IfKw } else { SyntaxKind::WhereKw }, keyword.range());
    let trivia = consume_direct_trivia(committed); committed.emit_trivia(&trivia);
    let stops = committed.probe(|probe| active_stop_set(probe.input()).with(StopKind::Arrow)); committed.probe(|probe| probe.input().local.push_stop_set(stops));
    if parse_direct_operator_chain(table, leading_trivia(&trivia), committed).is_none() { emit_case_like_missing(committed, CaseLikeRole::Guard, ExpectedSyntax::Expression); }
    committed.probe(|probe| assert_eq!(probe.input().local.pop_stop_set(), Some(stops))); committed.finish_node();
}

fn probe_arm_guard<'source, E>(i: &mut SynIn<'_, 'source, '_, E>) -> Option<(TriviaRun, WordSpan<'source>)>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{ let checkpoint = i.checkpoint(); let Some(trivia) = consume_trivia(i) else { return None; }; let Some(word) = i.run(scan_word) else { i.rollback(checkpoint); return None; }; if matches!(word.text(), "if" | "where") { Some((trivia, word)) } else { i.rollback(checkpoint); None } }

fn commit_arm_body<'parse, 'source, 'local, E, O>(table: &OperatorTable, family: CaseLikeFamily, policy: ArmSequencePolicy, committed: &mut Committed<'parse, 'source, 'local, E, O>)
where E: ErrorSink<usize>, O: CommitOutput<'source>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    let baseline = committed.probe(|probe| push_arm_body_baseline(policy, probe.input()));
    let base_indent = committed.probe(|probe| probe.input().local.line().line_indent);
    match committed.probe(|probe| recognize_introduced_body_layout(base_indent, probe.input())) {
        ArmBodyLayout::Inline { trivia } => {
            committed.emit_trivia(&trivia);
            let stops = committed.probe(|probe| arm_body_stop(policy, active_stop_set(probe.input()))); committed.probe(|probe| probe.input().local.push_stop_set(stops));
            if parse_direct_operator_chain(table, leading_trivia(&trivia), committed).is_none() { emit_case_like_missing(committed, CaseLikeRole::Body, ExpectedSyntax::Expression); }
            committed.probe(|probe| assert_eq!(probe.input().local.pop_stop_set(), Some(stops)));
        }
        ArmBodyLayout::Indented { opening_trivia, block_indent } => commit_indented_statement_block(table, opening_trivia, base_indent, block_indent, committed),
        ArmBodyLayout::WrongIndent => emit_case_like_missing(committed, CaseLikeRole::Body, ExpectedSyntax::Expression),
    }
    committed.probe(|probe| pop_arm_body_baseline(baseline, probe.input()));
    let _ = family;
}

fn arm_body_stop(policy: ArmSequencePolicy, outer: StopSet) -> StopSet { match policy { ArmSequencePolicy::CaseInline | ArmSequencePolicy::Indented { .. } | ArmSequencePolicy::CatchBraced => outer.with(StopKind::Comma).with(StopKind::Semicolon), ArmSequencePolicy::CatchInlineSingle => outer.with(StopKind::Semicolon) } }

fn push_arm_body_baseline<E>(policy: ArmSequencePolicy, i: &mut SynIn<E>) -> Option<IndentationBaseline>
where E: ErrorSink<usize>,
{
    let ArmSequencePolicy::Indented { arm_indent, .. } = policy else { return None; };
    let baseline = IndentationBaseline { column: arm_indent, kind: IndentationBaselineKind::Block };
    i.local.push_indentation_baseline(baseline);
    Some(baseline)
}

fn pop_arm_body_baseline<E>(baseline: Option<IndentationBaseline>, i: &mut SynIn<E>)
where E: ErrorSink<usize>,
{
    if let Some(baseline) = baseline { assert_eq!(i.local.pop_indentation_baseline(), Some(baseline)); }
}
fn direct_semicolon<E>(i: &mut SynIn<E>) -> Option<Range<usize>> where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> { let checkpoint = i.checkpoint(); let punctuation = i.run(scan_punctuation)?; let range = (punctuation.kind() == PunctuationKind::Semicolon).then(|| punctuation.range()); if range.is_none() { i.rollback(checkpoint); } range }

fn commit_direct_operand_slot<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    leading: LeadingTrivia,
) -> Option<()>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let accepted = committed.probe(|probe| probe_nud(table, leading, probe))?;
    commit_direct_operand_slot_from(table, accepted, committed)
}

fn commit_direct_operand_slot_from<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    mut accepted: NudRecognition<'source>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<()>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    loop {
        match accepted {
        NudRecognition::Parenthesized { open } => {
            cut_after_acceptance(committed);
            commit_parenthesized_nud(table, open, committed)?;
            return Some(());
        }
        NudRecognition::BracedStatementBlock { open } => {
            cut_after_acceptance(committed);
            commit_braced_statement_block_expression(table, open, committed);
            return Some(());
        }
        NudRecognition::If { keyword, base_indent } => {
            cut_after_acceptance(committed);
            commit_if_expression(table, keyword, base_indent, committed);
            return Some(());
        }
        NudRecognition::Case { keyword, base_indent } => {
            cut_after_acceptance(committed);
            commit_case_like_expression(table, CaseLikeFamily::Case, keyword, base_indent, committed);
            return Some(());
        }
        NudRecognition::Catch { keyword, base_indent } => {
            cut_after_acceptance(committed);
            commit_case_like_expression(table, CaseLikeFamily::Catch, keyword, base_indent, committed);
            return Some(());
        }
        NudRecognition::Identifier(identifier) => {
            let range = identifier.range();
            committed.start_node(SyntaxKind::IdentifierExpression);
            committed.token(SyntaxKind::Identifier, range.clone());
            committed.finish_node();
            return Some(());
        }
        NudRecognition::Integer(integer) => {
            let range = integer.range();
            committed.start_node(SyntaxKind::IntegerLiteral);
            committed.token(SyntaxKind::Integer, range.clone());
            committed.finish_node();
            return Some(());
        }
            NudRecognition::Prefix(operator) => {
            cut_after_acceptance(committed);
            emit_operator_use(committed, SyntaxKind::PrefixOperatorUse, &operator);
            committed.emit_trivia(operator.trailing_trivia());
            accepted = committed.probe(|probe| probe_nud(table, LeadingTrivia::None, probe))?;
        }
        NudRecognition::Nullfix(operator) => {
            emit_operator_use(committed, SyntaxKind::NullfixOperatorUse, &operator);
            committed.emit_trivia(operator.trailing_trivia());
            return Some(());
        }
        }
    }
}

fn commit_if_expression<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    keyword: WordSpan<'source>,
    base_indent: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::IfExpression);
    commit_if_arm(table, IfArmKeyword::If(keyword), base_indent, committed);
    loop {
        let Some(continuation) = committed.probe(|probe| {
            recognize_if_arm_continuation(base_indent, probe.input())
        }) else { break; };
        match continuation {
            IfContinuationKeyword::Elsif { keyword, trivia } => {
                cut_after_acceptance(committed);
                committed.emit_trivia(&trivia);
                commit_if_arm(table, IfArmKeyword::Elsif(keyword), base_indent, committed);
            }
            IfContinuationKeyword::Else { keyword, trivia } => {
                cut_after_acceptance(committed);
                committed.emit_trivia(&trivia);
                commit_else_arm(table, keyword, base_indent, committed);
                break;
            }
        }
    }
    committed.finish_node();
}

fn commit_if_arm<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    keyword: IfArmKeyword<'source>,
    base_indent: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::IfArm);
    let (token_kind, range) = match keyword {
        IfArmKeyword::If(word) => (SyntaxKind::IfKw, word.range()),
        IfArmKeyword::Elsif(word) => (SyntaxKind::ElsifKw, word.range()),
    };
    committed.token(token_kind, range);
    let trivia = commit_parenthesized_trivia(committed).expect("trivia scanning is total");
    committed.emit_trivia(&trivia);
    let stop_set = committed.probe(|probe| {
        active_stop_set(probe.input())
            .with(StopKind::Colon)
            .with(StopKind::LeftBrace)
            .with(StopKind::Elsif)
            .with(StopKind::Else)
    });
    committed.probe(|probe| probe.input().local.push_stop_set(stop_set));
    committed.start_node(SyntaxKind::Condition);
    let has_condition = parse_direct_operator_chain(table, leading_trivia(&trivia), committed).is_some();
    if !has_condition {
        emit_if_missing(committed, IfExpressionRole::Condition, ExpectedSyntax::Expression);
    }
    committed.finish_node();
    committed.probe(|probe| assert_eq!(probe.input().local.pop_stop_set(), Some(stop_set)));

    let colon = committed.probe(|probe| recognize_arm_colon(probe.input()));
    let Some(colon) = colon else {
        if has_condition {
            // At EOF the introducer and its body share one absence cause.
            emit_if_missing(committed, IfExpressionRole::Body, ExpectedSyntax::Expression);
        }
        committed.finish_node();
        return;
    };
    committed.token(SyntaxKind::Colon, colon);
    commit_colon_introduced_if_body(table, base_indent, IfExpressionRole::Body, committed);
    committed.finish_node();
}

fn commit_else_arm<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    keyword: WordSpan<'source>,
    base_indent: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::ElseArm);
    committed.token(SyntaxKind::ElseKw, keyword.range());
    let trivia = commit_parenthesized_trivia(committed).expect("trivia scanning is total");
    committed.emit_trivia(&trivia);
    if let Some(colon) = committed.probe(|probe| recognize_arm_colon(probe.input())) {
        committed.token(SyntaxKind::Colon, colon);
        commit_colon_introduced_if_body(table, base_indent, IfExpressionRole::ElseBody, committed);
    } else {
        let stop_set = committed.probe(|probe| active_stop_set(probe.input()).with(StopKind::Elsif).with(StopKind::Else));
        committed.probe(|probe| probe.input().local.push_stop_set(stop_set));
        if parse_direct_operator_chain(table, leading_trivia(&trivia), committed).is_none() {
            emit_if_missing(committed, IfExpressionRole::ElseBody, ExpectedSyntax::Expression);
        }
        committed.probe(|probe| assert_eq!(probe.input().local.pop_stop_set(), Some(stop_set)));
    }
    committed.finish_node();
}

fn commit_colon_introduced_if_body<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    base_indent: usize,
    role: IfExpressionRole,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let layout = committed.probe(|probe| recognize_introduced_body_layout(base_indent, probe.input()));
    match layout {
        ArmBodyLayout::Inline { trivia } => {
            committed.emit_trivia(&trivia);
            let stop_set = committed.probe(|probe| active_stop_set(probe.input()).with(StopKind::Elsif).with(StopKind::Else));
            committed.probe(|probe| probe.input().local.push_stop_set(stop_set));
            if parse_direct_operator_chain(table, leading_trivia(&trivia), committed).is_none() {
                if if_body_error_retry(table, role, committed) {
                    parse_direct_operator_chain(table, LeadingTrivia::None, committed)
                        .expect("a retried if body must commit its shared NUD candidate");
                } else {
                    emit_if_missing(committed, role, ExpectedSyntax::Expression);
                }
            }
            committed.probe(|probe| assert_eq!(probe.input().local.pop_stop_set(), Some(stop_set)));
        }
        ArmBodyLayout::Indented { opening_trivia, block_indent } => {
            commit_indented_statement_block_with_options(
                table,
                opening_trivia,
                base_indent,
                block_indent,
                IndentedStatementBlockOptions::if_arm(base_indent),
                committed,
            );
        }
        ArmBodyLayout::WrongIndent => emit_if_missing(committed, role, ExpectedSyntax::Expression),
    }
}

fn emit_operator_use<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    kind: SyntaxKind,
    operator: &ScannedOperator<'source>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.start_node(kind);
    committed.token(SyntaxKind::Operator, operator.range());
    committed.finish_node();
}

fn emit_operator_range<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    kind: SyntaxKind,
    range: Range<usize>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.start_node(kind);
    committed.token(SyntaxKind::Operator, range);
    committed.finish_node();
}

/// Recovery-only recognition preserves one unambiguous dangling infix use.
fn probe_dangling_infix<'parse, 'source, 'local, E>(
    table: &OperatorTable,
    probe: &mut Probe<'parse, 'source, 'local, E>,
) -> Option<(TriviaRun, Range<usize>, TriviaRun)>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let i = probe.input();
    let leading = consume_trivia(i)?;
    let remainder = i.input.remainder();
    let entry = table
        .entries_with_sites()
        .map(|(entry, _)| entry)
        .filter(|entry| remainder.starts_with(entry.spelling()))
        .max_by_key(|entry| entry.spelling().len())?;
    let fixities = entry.fixities();
    (fixities.infix().is_some() && fixities.suffix().is_none()).then_some(())?;
    let start = i.pos();
    for _ in entry.spelling().chars() {
        i.input.next()?;
    }
    let end = i.pos();
    let trailing = consume_trivia(i)?;
    (i.input.remainder().is_empty() || i.input.remainder().starts_with(')')).then_some(())?;
    Some((leading, start..end, trailing))
}

fn probe_dangling_prefix<'parse, 'source, 'local, E>(
    table: &OperatorTable,
    probe: &mut Probe<'parse, 'source, 'local, E>,
) -> Option<(Range<usize>, TriviaRun)>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let i = probe.input();
    let remainder = i.input.remainder();
    let entry = table
        .entries_with_sites()
        .map(|(entry, _)| entry)
        .filter(|entry| remainder.starts_with(entry.spelling()))
        .max_by_key(|entry| entry.spelling().len())?;
    let fixities = entry.fixities();
    (fixities.prefix().is_some() && !fixities.is_nullfix()).then_some(())?;
    let start = i.pos();
    for _ in entry.spelling().chars() {
        i.input.next()?;
    }
    let end = i.pos();
    let trailing = consume_trivia(i)?;
    (i.input.remainder().is_empty() || i.input.remainder().starts_with(')')).then_some(())?;
    Some((start..end, trailing))
}

/// Completes an accepted parenthesized expression without returning to the
/// NUD choice. The committed CST node owns the complete delimiter and list
/// shape, including recovery for a mandatory element after a comma.
fn commit_parenthesized_nud<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    open: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<()>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::ParenthesizedExpression);
    committed.token(SyntaxKind::LParen, open.clone());
    let incoming_base = committed.probe(|probe| {
        probe.input().local.indentation_baseline().map_or(0, |baseline| baseline.column)
    });
    push_direct_parenthesized_expression_scope(committed);

    let leading = commit_parenthesized_trivia(committed).expect("trivia scanning is total");
    let layout = committed.probe(|probe| {
        LayoutDelimitedFrame::after_opening_trivia(
            incoming_base,
            &leading,
            probe.input().local.line().line_indent,
        )
    });
    committed.probe(|probe| push_layout_delimited_baseline(layout, probe.input()));
    committed.emit_trivia(&leading);
    let mut delayed_initial_element_missing = None;

    if !parenthesized_close_pending(committed) && !parenthesized_close_absent_boundary(committed) {
        let element_start = committed_position(committed);
        let element =
            commit_parenthesized_element(table, leading_trivia(&leading), committed);
        if element.is_none() {
            let at = committed_position(committed);
            if element_start < at && parenthesized_close_absent_boundary(committed) {
                delayed_initial_element_missing = Some(at);
            } else {
                emit_expression_missing(committed);
            }
        }

        loop {
            let trivia = commit_parenthesized_trivia(committed).expect("trivia scanning is total");
            committed.emit_trivia(&trivia);
            if let Some(comma) = commit_parenthesized_comma(committed) {
                committed.token(SyntaxKind::Comma, comma);
                let leading = commit_parenthesized_trivia(committed).expect("trivia scanning is total");
                committed.emit_trivia(&leading);
                if parenthesized_close_pending(committed) {
                    break;
                }
                if commit_parenthesized_element(table, leading_trivia(&leading), committed).is_none() {
                    emit_expression_missing(committed);
                }
                continue;
            }
            if parenthesized_close_pending(committed) {
                break;
            }
            let boundary = committed.probe(|probe| {
                layout.boundary_after_trivia(&trivia, probe.input().local.line().line_indent)
            });
            if boundary == LayoutDelimitedBoundary::ImplicitNewline {
                if commit_parenthesized_element(table, LeadingTrivia::None, committed).is_none() {
                    emit_expression_missing(committed);
                }
                continue;
            }
            if boundary == LayoutDelimitedBoundary::None && parenthesized_element_pending(table, committed) {
                emit_parenthesized_separator_missing(committed);
                if commit_parenthesized_element(table, LeadingTrivia::None, committed).is_none() {
                    emit_expression_missing(committed);
                }
                continue;
            }
            break;
        }
    }

    let close = commit_parenthesized_close(committed);
    match close {
        ParenthesizedClose::Matched(range) => {
            committed.token(SyntaxKind::RParen, range.clone());
            committed.probe(|probe| pop_layout_delimited_baseline(layout, probe.input()));
            pop_direct_parenthesized_expression_scope(committed);
            committed.finish_node();
            Some(())
        }
        ParenthesizedClose::Missing { at } => {
            if delayed_initial_element_missing == Some(at) {
                emit_parenthesized_element_and_close_missing(committed, at);
            } else {
                emit_parenthesized_close_missing(committed, at);
            }
            committed.probe(|probe| pop_layout_delimited_baseline(layout, probe.input()));
            pop_direct_parenthesized_expression_scope(committed);
            committed.finish_node();
            Some(())
        }
    }
}

fn commit_parenthesized_element<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    leading: LeadingTrivia,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<ParsedExpression<O::Checkpoint>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_direct_operator_chain(table, leading, committed).or_else(|| {
        parenthesized_element_error_retry(table, committed).then(|| {
            parse_direct_operator_chain(table, LeadingTrivia::None, committed)
                .expect("a retried parenthesized element must commit its shared NUD candidate")
        })
    })
}

fn parenthesized_element_pending<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| direct_expression_nud_candidate(table, LeadingTrivia::None, probe))
}

/// A mandatory list element owns invalid bytes only until a shared NUD
/// candidate or a parenthesized-list boundary; it never hands them back to
/// an outer declaration body recovery.
fn parenthesized_element_error_retry<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
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
            let boundary = {
                let i = probe.input();
                let Some(character) = i.input.remainder().chars().next() else {
                    return (start < end).then_some((start..end, false));
                };
                matches!(character, ')' | ']' | '}' | ';' | ',')
            };
            if boundary {
                return (start < end).then_some((start..end, false));
            }
            {
                let i = probe.input();
                i.input.next()?;
                end = i.pos();
                let mut line = i.local.line();
                line.at_line_start = false;
                i.local.set_line(line);
            }
            if direct_expression_nud_candidate(table, LeadingTrivia::None, probe) {
                return Some((start..end, true));
            }
        }
    });
    let Some((range, retry)) = recovered else {
        return false;
    };
    emit_parenthesized_error(
        committed,
        GrammarRole::Expression(ExpressionRole::Nud),
        range,
    );
    retry
}

enum ParenthesizedClose {
    Matched(Range<usize>),
    Missing { at: usize },
}

/// The closing mandatory slot follows the closing-delimiter rule. A wrong
/// close is emitted as its own non-empty episode, then the same close slot
/// keeps searching rather than returning failure to the NUD dispatcher.
fn commit_parenthesized_close<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> ParenthesizedClose
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    commit_parenthesized_close_for_owner(committed, parenthesized_close_role())
}

fn commit_call_close<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> ParenthesizedClose
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    commit_parenthesized_close_for_owner(committed, call_close_role())
}

fn commit_parenthesized_close_for_owner<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: GrammarRole,
) -> ParenthesizedClose
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    loop {
        if parenthesized_close_absent_boundary(committed) {
            return ParenthesizedClose::Missing {
                at: committed_position(committed),
            };
        }

        let punctuation = committed.probe(|probe| probe.input().run(scan_punctuation));
        if let Some(punctuation) = punctuation {
            match punctuation.kind() {
                PunctuationKind::Close(Delimiter::Parenthesis) => {
                    return ParenthesizedClose::Matched(punctuation.range());
                }
                PunctuationKind::Close(actual @ (Delimiter::Bracket | Delimiter::Brace)) => {
                    emit_parenthesized_close_error(committed, role, punctuation.range(), actual);
                }
                _ => emit_parenthesized_error(
                    committed,
                    role,
                    punctuation.range(),
                ),
            }
            continue;
        }

        let range = committed
            .probe(|probe| {
                let start = probe.input().pos();
                let mut end = start;
                loop {
                    let i = probe.input();
                    let Some(character) = i.input.remainder().chars().next() else {
                        return (start < end).then_some(start..end);
                    };
                    if matches!(character, ')' | ']' | '}' | ';') {
                        return (start < end).then_some(start..end);
                    }
                    i.input
                        .next()
                        .expect("the scanned parenthesized-close byte exists");
                    end = i.pos();
                    let mut line = i.local.line();
                    line.at_line_start = false;
                    i.local.set_line(line);
                }
            })
            .expect("a non-boundary parenthesized-close position must consume invalid source");
        emit_parenthesized_error(committed, role, range);
    }
}

fn commit_parenthesized_trivia<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<TriviaRun>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| probe.input().run(scan_trivia))
}

fn parenthesized_close_pending<'parse, 'source, 'local, E, O>(
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
        let pending = i.run(recognize_parenthesized_close).is_some();
        i.rollback(checkpoint);
        pending
    })
}

fn index_close_pending<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>, O: CommitOutput<'source>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input(); let checkpoint = i.checkpoint();
        let pending = i.run(recognize_index_close).is_some();
        i.rollback(checkpoint);
        pending
    })
}

enum IndexClose {
    Matched(Range<usize>),
    Missing,
}

fn commit_index_close<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> IndexClose
where
    E: ErrorSink<usize>, O: CommitOutput<'source>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    loop {
        if committed.probe(|probe| probe.input().input.remainder().is_empty() || matches!(probe.input().input.remainder().chars().next(), Some(';'))) {
            return IndexClose::Missing;
        }
        let punctuation = committed.probe(|probe| probe.input().run(scan_punctuation));
        if let Some(punctuation) = punctuation {
            match punctuation.kind() {
                PunctuationKind::Close(Delimiter::Bracket) => return IndexClose::Matched(punctuation.range()),
                PunctuationKind::Close(actual @ (Delimiter::Parenthesis | Delimiter::Brace)) => {
                    emit_index_close_error(committed, punctuation.range(), actual);
                }
                _ => emit_index_close_error(committed, punctuation.range(), Delimiter::Bracket),
            }
            continue;
        }
        let range = committed.probe(|probe| {
            let start = probe.input().pos(); let mut end = start;
            loop {
                let i = probe.input(); let Some(character) = i.input.remainder().chars().next() else { return (start < end).then_some(start..end); };
                if matches!(character, ')' | ']' | '}' | ';') { return (start < end).then_some(start..end); }
                i.input.next()?; end = i.pos();
                let mut line = i.local.line(); line.at_line_start = false; i.local.set_line(line);
            }
        }).expect("an index close recovery consumes invalid source");
        emit_index_close_error(committed, range, Delimiter::Bracket);
    }
}

fn commit_parenthesized_comma<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| probe.input().run(recognize_parenthesized_comma))
}

fn parenthesized_close_absent_boundary<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.probe(|probe| {
        probe.input().input.remainder().is_empty()
            || matches!(probe.input().input.remainder().chars().next(), Some(';'))
    })
}

fn parenthesized_close_role() -> GrammarRole {
    GrammarRole::ClosingDelimiter {
        owner: ConstructRole::ExpressionGroup,
        delimiter: Delimiter::Parenthesis,
    }
}

fn call_close_role() -> GrammarRole {
    GrammarRole::ClosingDelimiter {
        owner: ConstructRole::ArgumentList,
        delimiter: Delimiter::Parenthesis,
    }
}

fn emit_expression_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::Expression(ExpressionRole::Nud);
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: at..at,
            },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Expression,
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

fn emit_fixed_tail_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    expression_role: ExpressionRole,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::Expression(expression_role);
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey { role, range: at..at },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Identifier,
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

fn emit_fixed_tail_error<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    expression_role: ExpressionRole,
    range: Range<usize>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let role = GrammarRole::Expression(expression_role);
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
                expected: ExpectedSyntax::Identifier,
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
}

fn emit_call_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    expression_role: ExpressionRole,
    expected: ExpectedSyntax,
) where E: ErrorSink<usize>, O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input(); let at = i.pos(); let role = GrammarRole::Expression(expression_role);
        CommittedRecoveryRecord::new(i.local, RecoverySiteKey { role, range: at..at }, RecoveryKind::Missing, Arc::from([]), Arc::from([SyntaxExpectation { role, expected, range: at..at, sources: ExpectationSources::COMMITTED_RECOVERY_RULE }]), 0)
    });
    committed.emit_missing(record);
}

fn emit_call_close_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where E: ErrorSink<usize>, O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input(); let at = i.pos();
        let role = call_close_role();
        CommittedRecoveryRecord::new(i.local, RecoverySiteKey { role, range: at..at }, RecoveryKind::Missing, Arc::from([]), Arc::from([SyntaxExpectation { role, expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Close(Delimiter::Parenthesis)), range: at..at, sources: ExpectationSources::COMMITTED_RECOVERY_RULE }]), 0)
    });
    committed.emit_missing(record);
}

fn emit_call_error<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    expression_role: ExpressionRole,
    range: Range<usize>,
) where E: ErrorSink<usize>, O: CommitOutput<'source>,
{
    let role = GrammarRole::Expression(expression_role);
    let record = committed.probe(|probe| CommittedRecoveryRecord::new(
        probe.input().local,
        RecoverySiteKey { role, range: range.clone() },
        RecoveryKind::Error,
        Arc::from([UnexpectedSyntax::Token { range: range.clone(), category: UnexpectedCategory::OtherCharacter }]),
        Arc::from([SyntaxExpectation { role, expected: ExpectedSyntax::Expression, range, sources: ExpectationSources::COMMITTED_RECOVERY_RULE }]),
        0,
    ));
    committed.emit_error(record);
}

fn emit_index_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>, expression_role: ExpressionRole, expected: ExpectedSyntax,
) where E: ErrorSink<usize>, O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input(); let at = i.pos(); let role = GrammarRole::Expression(expression_role);
        CommittedRecoveryRecord::new(i.local, RecoverySiteKey { role, range: at..at }, RecoveryKind::Missing, Arc::from([]), Arc::from([SyntaxExpectation { role, expected, range: at..at, sources: ExpectationSources::COMMITTED_RECOVERY_RULE }]), 0)
    });
    committed.emit_missing(record);
}

fn emit_projection_missing<'parse, 'source, 'local, E, O>(committed: &mut Committed<'parse, 'source, 'local, E, O>, expression_role: ExpressionRole, expected: ExpectedSyntax)
where E: ErrorSink<usize>, O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input(); let at = i.pos(); let role = GrammarRole::Expression(expression_role);
        CommittedRecoveryRecord::new(i.local, RecoverySiteKey { role, range: at..at }, RecoveryKind::Missing, Arc::from([]), Arc::from([SyntaxExpectation { role, expected, range: at..at, sources: ExpectationSources::COMMITTED_RECOVERY_RULE }]), 0)
    }); committed.emit_missing(record);
}

fn emit_projection_error<'parse, 'source, 'local, E, O>(committed: &mut Committed<'parse, 'source, 'local, E, O>, expression_role: ExpressionRole, range: Range<usize>)
where E: ErrorSink<usize>, O: CommitOutput<'source>,
{
    let role = GrammarRole::Expression(expression_role);
    let record = committed.probe(|probe| CommittedRecoveryRecord::new(
        probe.input().local, RecoverySiteKey { role, range: range.clone() }, RecoveryKind::Error,
        Arc::from([UnexpectedSyntax::Token { range: range.clone(), category: UnexpectedCategory::OtherCharacter }]),
        Arc::from([SyntaxExpectation { role, expected: ExpectedSyntax::Expression, range, sources: ExpectationSources::COMMITTED_RECOVERY_RULE }]), 0,
    )); committed.emit_error(record);
}

fn emit_projection_close_missing<'parse, 'source, 'local, E, O>(committed: &mut Committed<'parse, 'source, 'local, E, O>, owner: ConstructRole, delimiter: Delimiter)
where E: ErrorSink<usize>, O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input(); let at = i.pos(); let role = GrammarRole::ClosingDelimiter { owner, delimiter };
        CommittedRecoveryRecord::new(i.local, RecoverySiteKey { role, range: at..at }, RecoveryKind::Missing, Arc::from([]), Arc::from([SyntaxExpectation { role, expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Close(delimiter)), range: at..at, sources: ExpectationSources::COMMITTED_RECOVERY_RULE }]), 0)
    }); committed.emit_missing(record);
}

fn emit_projection_close_error<'parse, 'source, 'local, E, O>(committed: &mut Committed<'parse, 'source, 'local, E, O>, range: Range<usize>, _: PunctuationKind)
where E: ErrorSink<usize>, O: CommitOutput<'source>,
{
    let role = GrammarRole::ClosingDelimiter { owner: ConstructRole::ProjectionRecordTail, delimiter: Delimiter::Brace };
    let record = committed.probe(|probe| CommittedRecoveryRecord::new(
        probe.input().local, RecoverySiteKey { role, range: range.clone() }, RecoveryKind::Error,
        Arc::from([UnexpectedSyntax::Token { range: range.clone(), category: UnexpectedCategory::OtherCharacter }]),
        Arc::from([SyntaxExpectation { role, expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Close(Delimiter::Brace)), range, sources: ExpectationSources::COMMITTED_RECOVERY_RULE }]), 0,
    )); committed.emit_error(record);
}

fn emit_index_close_missing<'parse, 'source, 'local, E, O>(committed: &mut Committed<'parse, 'source, 'local, E, O>)
where E: ErrorSink<usize>, O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input(); let at = i.pos(); let role = GrammarRole::ClosingDelimiter { owner: ConstructRole::IndexTail, delimiter: Delimiter::Bracket };
        CommittedRecoveryRecord::new(i.local, RecoverySiteKey { role, range: at..at }, RecoveryKind::Missing, Arc::from([]), Arc::from([SyntaxExpectation { role, expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Close(Delimiter::Bracket)), range: at..at, sources: ExpectationSources::COMMITTED_RECOVERY_RULE }]), 0)
    });
    committed.emit_missing(record);
}

fn emit_index_close_error<'parse, 'source, 'local, E, O>(committed: &mut Committed<'parse, 'source, 'local, E, O>, range: Range<usize>, actual: Delimiter)
where E: ErrorSink<usize>, O: CommitOutput<'source>,
{
    let role = GrammarRole::ClosingDelimiter { owner: ConstructRole::IndexTail, delimiter: Delimiter::Bracket };
    let record = committed.probe(|probe| CommittedRecoveryRecord::new(
        probe.input().local, RecoverySiteKey { role, range: range.clone() }, RecoveryKind::Error,
        Arc::from([UnexpectedSyntax::Token { range: range.clone(), category: UnexpectedCategory::Punctuation(crate::session::PunctuationEvidence::Close(actual)) }]),
        Arc::from([SyntaxExpectation { role, expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Close(Delimiter::Bracket)), range, sources: ExpectationSources::COMMITTED_RECOVERY_RULE }]), 0,
    ));
    committed.emit_error(record);
}

fn emit_index_error<'parse, 'source, 'local, E, O>(committed: &mut Committed<'parse, 'source, 'local, E, O>, expression_role: ExpressionRole, range: Range<usize>)
where E: ErrorSink<usize>, O: CommitOutput<'source>,
{
    let role = GrammarRole::Expression(expression_role);
    let record = committed.probe(|probe| CommittedRecoveryRecord::new(
        probe.input().local, RecoverySiteKey { role, range: range.clone() }, RecoveryKind::Error,
        Arc::from([UnexpectedSyntax::Token { range: range.clone(), category: UnexpectedCategory::OtherCharacter }]),
        Arc::from([SyntaxExpectation { role, expected: ExpectedSyntax::Expression, range, sources: ExpectationSources::COMMITTED_RECOVERY_RULE }]), 0,
    ));
    committed.emit_error(record);
}

fn emit_parenthesized_separator_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::Expression(ExpressionRole::ParenthesizedSeparator);
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: at..at,
            },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Comma),
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

fn emit_case_like_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    case_role: CaseLikeRole,
    expected: ExpectedSyntax,
) where E: ErrorSink<usize>, O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input(); let at = i.pos(); let role = GrammarRole::CaseLike(case_role);
        CommittedRecoveryRecord::new(i.local, RecoverySiteKey { role, range: at..at }, RecoveryKind::Missing, Arc::from([]), Arc::from([SyntaxExpectation { role, expected, range: at..at, sources: ExpectationSources::COMMITTED_RECOVERY_RULE }]), 0)
    });
    committed.emit_missing(record);
}

fn commit_case_like_invalid_arrow<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where E: ErrorSink<usize>, O: CommitOutput<'source>,
{
    let range = committed.probe(|probe| {
        let i = probe.input(); let start = i.pos(); let mut end = start;
        while let Some(character) = i.input.remainder().chars().next() {
            if matches!(character, ',' | '}' | '\n' | '\r') { break; }
            i.input.next().expect("the inspected source character exists"); end = i.pos();
            let mut line = i.local.line(); line.at_line_start = false; i.local.set_line(line);
        }
        (start < end).then_some(start..end)
    });
    let Some(range) = range else { return; };
    let role = GrammarRole::CaseLike(CaseLikeRole::Arrow);
    let record = committed.probe(|probe| CommittedRecoveryRecord::new(probe.input().local, RecoverySiteKey { role, range: range.clone() }, RecoveryKind::Error, Arc::from([UnexpectedSyntax::Token { range: range.clone(), category: UnexpectedCategory::OperatorLike }]), Arc::from([SyntaxExpectation { role, expected: ExpectedSyntax::Expression, range, sources: ExpectationSources::COMMITTED_RECOVERY_RULE }]), 0));
    committed.emit_error(record);
}

fn emit_if_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    if_role: IfExpressionRole,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::IfExpression(if_role);
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

fn if_body_error_retry<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    role: IfExpressionRole,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
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
                return (start < end).then_some((start..end, false));
            };
            if matches!(character, '\r' | '\n' | ')' | ']' | '}' | ';' | ',') {
                return (start < end).then_some((start..end, false));
            }
            i.input.next()?;
            end = i.pos();
            let mut line = i.local.line();
            line.at_line_start = false;
            i.local.set_line(line);
            if direct_expression_nud_candidate(table, LeadingTrivia::None, probe) {
                return Some((start..end, true));
            }
        }
    });
    let Some((range, retry)) = recovered else { return false; };
    emit_if_error(committed, role, range);
    retry
}

fn emit_if_error<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    if_role: IfExpressionRole,
    range: Range<usize>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let role = GrammarRole::IfExpression(if_role);
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
                expected: ExpectedSyntax::Expression,
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
}

fn emit_colon_application_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    colon_role: ColonApplicationRole,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::ColonApplication(colon_role);
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: at..at,
            },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Expression,
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

fn emit_colon_application_error<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    colon_role: ColonApplicationRole,
    range: Range<usize>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let role = GrammarRole::ColonApplication(colon_role);
    let record = committed.probe(|probe| {
        let i = probe.input();
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            RecoveryKind::Error,
            Arc::from([UnexpectedSyntax::Token {
                range: range.clone(),
                category: UnexpectedCategory::OtherCharacter,
            }]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Expression,
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
}

fn emit_statement_sequence_missing<'parse, 'source, 'local, E, O>(
    policy: StatementSequencePolicy,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = statement_sequence_statement_role(policy);
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: at..at,
            },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Statement,
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

fn emit_statement_sequence_error<'parse, 'source, 'local, E, O>(
    policy: StatementSequencePolicy,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    range: Range<usize>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let role = statement_sequence_statement_role(policy);
    let record = committed.probe(|probe| {
        let i = probe.input();
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            RecoveryKind::Error,
            Arc::from([UnexpectedSyntax::Token {
                range: range.clone(),
                category: UnexpectedCategory::OtherCharacter,
            }]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Statement,
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
}

fn statement_sequence_statement_role(policy: StatementSequencePolicy) -> GrammarRole {
    match policy {
        StatementSequencePolicy::Indented { .. } => {
            GrammarRole::ColonApplication(ColonApplicationRole::IndentedStatement)
        }
        StatementSequencePolicy::BracedPrimary => {
            GrammarRole::BracedStatementBlock(BracedStatementBlockRole::Statement)
        }
    }
}

fn braced_close_role() -> GrammarRole {
    GrammarRole::ClosingDelimiter {
        owner: ConstructRole::BracedStatementBlockExpression,
        delimiter: Delimiter::Brace,
    }
}

fn emit_braced_statement_separator_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    emit_braced_missing(
        committed,
        GrammarRole::BracedStatementBlock(BracedStatementBlockRole::Separator),
        ExpectedSyntax::StatementSeparator,
    );
}

fn emit_braced_close_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    emit_braced_missing(
        committed,
        braced_close_role(),
        ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Close(Delimiter::Brace)),
    );
}

fn emit_braced_missing<'parse, 'source, 'local, E, O>(
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

fn emit_braced_close_error<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    range: Range<usize>,
    actual: Delimiter,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    emit_braced_error(
        committed,
        braced_close_role(),
        range.clone(),
        UnexpectedCategory::Punctuation(crate::session::PunctuationEvidence::Close(actual)),
        ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Close(Delimiter::Brace)),
    );
}

fn emit_braced_close_other_error<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    range: Range<usize>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    emit_braced_error(
        committed,
        braced_close_role(),
        range,
        UnexpectedCategory::OtherCharacter,
        ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Close(Delimiter::Brace)),
    );
}

fn emit_braced_error<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: GrammarRole,
    range: Range<usize>,
    category: UnexpectedCategory,
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
                category,
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

fn emit_parenthesized_close_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    at: usize,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let role = parenthesized_close_role();
    emit_parenthesized_missing(
        committed,
        role,
        at,
        Arc::from([SyntaxExpectation {
            role,
            expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Close(
                Delimiter::Parenthesis,
            )),
            range: at..at,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
    );
}

fn emit_parenthesized_element_and_close_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    at: usize,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let close_role = parenthesized_close_role();
    let element_role = GrammarRole::Expression(ExpressionRole::Nud);
    emit_parenthesized_missing(
        committed,
        close_role,
        at,
        Arc::from([
            SyntaxExpectation {
                role: close_role,
                expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Close(
                    Delimiter::Parenthesis,
                )),
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            },
            SyntaxExpectation {
                role: element_role,
                expected: ExpectedSyntax::Expression,
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            },
        ]),
    );
}

fn emit_parenthesized_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: GrammarRole,
    at: usize,
    expectations: Arc<[SyntaxExpectation]>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: at..at,
            },
            RecoveryKind::Missing,
            Arc::from([]),
            expectations,
            0,
        )
    });
    committed.emit_missing(record);
}

fn emit_parenthesized_close_error<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: GrammarRole,
    range: Range<usize>,
    actual: Delimiter,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            RecoveryKind::Error,
            Arc::from([UnexpectedSyntax::Token {
                range: range.clone(),
                category: UnexpectedCategory::Punctuation(
                    crate::session::PunctuationEvidence::Close(actual),
                ),
            }]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Close(
                    Delimiter::Parenthesis,
                )),
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
}

fn emit_parenthesized_error<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: GrammarRole,
    range: Range<usize>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let expected = match role {
        GrammarRole::Expression(ExpressionRole::Nud) => ExpectedSyntax::Expression,
        GrammarRole::ClosingDelimiter { .. } => ExpectedSyntax::Punctuation(
            crate::session::PunctuationEvidence::Close(Delimiter::Parenthesis),
        ),
        _ => unreachable!("parenthesized recovery only emits element or close roles"),
    };
    let record = committed.probe(|probe| {
        let i = probe.input();
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
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

fn committed_position<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> usize
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.probe(|probe| probe.input().pos())
}

fn parenthesized_expression_stop_set() -> StopSet {
    StopSet::default()
        .with(StopKind::Comma)
        .with(StopKind::RightParenthesis)
}

fn push_parenthesized_expression_scope<E>(i: &mut SynIn<E>)
where
    E: ErrorSink<usize>,
{
    i.local.push_delimiter(Delimiter::Parenthesis);
    i.local.push_stop_set(parenthesized_expression_stop_set());
}

fn pop_parenthesized_expression_scope<E>(i: &mut SynIn<E>)
where
    E: ErrorSink<usize>,
{
    assert_eq!(i.local.pop_delimiter(), Some(Delimiter::Parenthesis));
    assert_eq!(
        i.local.pop_stop_set(),
        Some(parenthesized_expression_stop_set())
    );
}

fn push_layout_delimited_baseline<E>(layout: LayoutDelimitedFrame, i: &mut SynIn<E>)
where
    E: ErrorSink<usize>,
{
    i.local.push_indentation_baseline(IndentationBaseline {
        column: layout.base_indent(),
        kind: IndentationBaselineKind::Introducer,
    });
}

fn pop_layout_delimited_baseline<E>(layout: LayoutDelimitedFrame, i: &mut SynIn<E>)
where
    E: ErrorSink<usize>,
{
    assert_eq!(
        i.local.pop_indentation_baseline(),
        Some(IndentationBaseline {
            column: layout.base_indent(),
            kind: IndentationBaselineKind::Introducer,
        })
    );
}

fn push_direct_parenthesized_expression_scope<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.probe(|probe| push_parenthesized_expression_scope(probe.input()));
}

fn pop_direct_parenthesized_expression_scope<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.probe(|probe| pop_parenthesized_expression_scope(probe.input()));
}

fn parse_atom<'source, E>(mut i: SynIn<'_, 'source, '_, E>) -> Option<Expression<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    i.choice((
        parse_identifier.map(Expression::Identifier),
        parse_integer_literal.map(Expression::Integer),
    ))
}

fn parse_identifier<'source, E>(mut i: SynIn<'_, 'source, '_, E>) -> Option<WordSpan<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    i.run(scan_word)
}

pub(crate) fn parse_integer_literal<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<IntegerLiteral<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let start = i.pos();
    i.skip(one_of(|character: char| character.is_ascii_digit()))?;
    i.skip(many_skip(one_of(|character: char| {
        character.is_ascii_digit()
    })))?;
    let end = i.pos();

    Some(IntegerLiteral {
        text: &i.input.source()[start..end],
        start,
        end,
    })
}

#[cfg(test)]
mod tests {
    use std::{cell::Cell, rc::Rc};

    use super::*;
    use chasa::{input::IsCut, prelude::In};

    use crate::{
        SyntaxKind, SyntaxNode,
        input::SourceInput,
        operator::{BindingPower, OperatorDeclaration, OperatorFixities},
        session::{CommittedRecoveryRecord, FullCstOutput, ParseLocal, Probe},
    };

    #[test]
    fn operator_chain_ast_preserves_parenthesized_element_counts_and_trailing_commas() {
        let cases = [
            ("()", 0, None, 0..2),
            ("(a)", 1, None, 0..3),
            ("(a,)", 1, Some(2..3), 0..4),
            ("(a,b)", 2, None, 0..5),
            ("(a,b,)", 2, Some(4..5), 0..6),
        ];

        for (source, expected_element_count, expected_trailing_comma, expected_range) in cases {
            let chain = parse(source, &canonical_operator_table());
            let [OperatorChainItem::Primary(PrimaryExpression::Parenthesized {
                elements,
                trailing_comma,
                range,
            })] = chain.items()
            else {
                panic!("expected parenthesized expression for {source:?}");
            };

            assert_eq!(elements.len(), expected_element_count, "{source:?}");
            assert_eq!(*trailing_comma, expected_trailing_comma, "{source:?}");
            assert_eq!(*range, expected_range, "{source:?}");
        }
    }

    #[test]
    fn parenthesized_layout_boundaries_preserve_ast_direct_shape_and_trivia() {
        for (source, element_count, trailing_comma, literal_commas) in [
            ("(a\nb)", 2, None, 0),
            ("(a,\nb\nc)", 3, None, 1),
            ("(a\n)", 1, None, 0),
            ("(a,\nb)", 2, None, 1),
        ] {
            let chain = parse(source, &canonical_operator_table());
            let [OperatorChainItem::Primary(PrimaryExpression::Parenthesized {
                elements,
                trailing_comma: actual_trailing_comma,
                ..
            })] = chain.items()
            else {
                panic!("expected a parenthesized expression for {source:?}");
            };
            assert_eq!(elements.len(), element_count, "{source:?}");
            assert_eq!(*actual_trailing_comma, trailing_comma, "{source:?}");

            let root = parse_direct(source, &canonical_operator_table());
            let outer = only_child(&root, SyntaxKind::OperatorChain);
            let group = only_child(&outer, SyntaxKind::ParenthesizedExpression);
            assert_eq!(group.to_string(), source, "{source:?}");
            assert_eq!(
                group.children().filter(|node| node.kind() == SyntaxKind::OperatorChain).count(),
                element_count,
                "{source:?}"
            );
            assert_eq!(
                group.children_with_tokens().filter(|child| child.kind() == SyntaxKind::Comma).count(),
                literal_commas,
                "{source:?}"
            );
            assert!(!group.descendants().any(|node| node.kind() == SyntaxKind::Missing));
        }

        let source = "(a\nb)";
        let low = colon_operator_table(BindingPower::scalar(1));
        let high = colon_operator_table(BindingPower::scalar(99));
        assert_eq!(parse(source, &low), parse(source, &high));
        assert_eq!(parse_direct(source, &low).green(), parse_direct(source, &high).green());

        let range_table = range_operator_table();
        for (source, operator_kind) in [
            ("xs[2..]", SyntaxKind::SuffixOperatorUse),
            ("xs[..2]", SyntaxKind::PrefixOperatorUse),
        ] {
            let chain = parse(source, &range_table);
            let [
                OperatorChainItem::Primary(_),
                OperatorChainItem::FixedPostfix(FixedPostfixTail::Index(IndexTail { items, .. })),
            ] = chain.items() else {
                panic!("expected an index tail for {source:?}");
            };
            assert!(matches!(items.as_slice(), [OperatorChain { items, .. }] if matches!(
                items.as_slice(),
                [OperatorChainItem::Primary(_), OperatorChainItem::SuffixUse(_)]
                    | [OperatorChainItem::PrefixUse(_), OperatorChainItem::Primary(_)]
            )));

            let root = parse_direct(source, &range_table);
            assert_eq!(root.to_string(), source);
            let index = root.descendants().find(|node| node.kind() == SyntaxKind::IndexTail).unwrap();
            assert_eq!(index.descendants().filter(|node| node.kind() == operator_kind).count(), 1);
            assert!(!index.descendants().any(|node| node.kind() == SyntaxKind::Missing));
        }
    }

    #[test]
    fn parenthesized_layout_keeps_deeper_newlines_and_same_line_recovery_local() {
        let (root, recoveries) = parse_direct_recovered("(a\n  b)", &canonical_operator_table());
        let outer = only_child(&root, SyntaxKind::OperatorChain);
        let group = only_child(&outer, SyntaxKind::ParenthesizedExpression);
        assert_eq!(group.children().filter(|node| node.kind() == SyntaxKind::OperatorChain).count(), 1);
        assert!(!recoveries.is_empty());

        let (root, recoveries) = parse_direct_recovered("(a b)", &canonical_operator_table());
        assert_eq!(root.to_string(), "(a b)");
        let outer = only_child(&root, SyntaxKind::OperatorChain);
        let group = only_child(&outer, SyntaxKind::ParenthesizedExpression);
        assert_eq!(group.children().filter(|node| node.kind() == SyntaxKind::OperatorChain).count(), 2);
        assert!(matches!(
            recoveries.as_slice(),
            [CommittedRecoveryRecord { kind: RecoveryKind::Missing, site, .. }]
                if site.role == GrammarRole::Expression(ExpressionRole::ParenthesizedSeparator)
                    && site.range == (3..3)
        ));

        let chain = parse("(a b)", &canonical_operator_table());
        let [OperatorChainItem::Primary(PrimaryExpression::Parenthesized { elements, .. })] = chain.items() else {
            panic!("expected parenthesized expression");
        };
        assert_eq!(elements.len(), 2);
    }

    #[test]
    fn operator_chain_ast_builds_nested_parenthesized_expressions() {
        let chain = parse("((a))", &canonical_operator_table());
        let [OperatorChainItem::Primary(PrimaryExpression::Parenthesized {
            elements,
            trailing_comma,
            range,
        })] = chain.items()
        else {
            panic!("expected outer parenthesized expression");
        };
        assert_eq!(*range, 0..5);
        assert_eq!(*trailing_comma, None);
        let [OperatorChain {
            items,
            range: inner_chain_range,
        }] = elements.as_slice() else {
            panic!("expected one nested chain");
        };
        assert_eq!(*inner_chain_range, 1..4);
        let [OperatorChainItem::Primary(PrimaryExpression::Parenthesized {
                elements,
                trailing_comma,
                range,
            })] = items.as_slice()
        else {
            panic!("expected one nested parenthesized element");
        };
        assert_eq!(*range, 1..4);
        assert_eq!(*trailing_comma, None);
        assert!(matches!(
            elements.as_slice(),
            [OperatorChain { items, .. }]
                if matches!(items.as_slice(), [OperatorChainItem::Primary(PrimaryExpression::Identifier(_))])
        ));
    }

    #[test]
    fn nud_role_selection_splits_long_infix_into_prefix_and_nullfix_uses() {
        let table = canonical_operator_table();
        let chain = parse("+!a", &table);
        assert!(matches!(
            chain.items(),
            [
                OperatorChainItem::PrefixUse(plus),
                OperatorChainItem::PrefixUse(bang),
                OperatorChainItem::Primary(PrimaryExpression::Identifier(identifier)),
            ] if plus.text() == "+" && plus.range() == (0..1)
                && bang.text() == "!" && bang.range() == (1..2)
                && identifier.text() == "a" && identifier.range() == (2..3)
        ));
    }

    #[test]
    fn led_role_selection_keeps_the_long_infix_use() {
        let table = canonical_operator_table();
        let chain = parse("a+!b", &table);
        assert!(matches!(
            chain.items(),
            [
                OperatorChainItem::Primary(PrimaryExpression::Identifier(left)),
                OperatorChainItem::InfixUse(operator),
                OperatorChainItem::Primary(PrimaryExpression::Identifier(right)),
            ] if left.text() == "a" && operator.text() == "+!" && operator.range() == (1..3)
                && right.text() == "b"
        ));
    }

    #[test]
    fn direct_nud_role_selection_emits_flat_prefix_uses_after_candidate_fallback() {
        let root = parse_direct("+!a", &canonical_operator_table());
        let chain = only_child(&root, SyntaxKind::OperatorChain);
        assert_eq!(
            chain.children().map(|node| node.kind()).collect::<Vec<_>>(),
            vec![SyntaxKind::PrefixOperatorUse, SyntaxKind::PrefixOperatorUse, SyntaxKind::IdentifierExpression]
        );
        assert_eq!(chain.children().nth(0).unwrap().first_token().unwrap().text(), "+");
        assert_eq!(chain.children().nth(1).unwrap().first_token().unwrap().text(), "!");
        assert_eq!(root.to_string(), "+!a");
    }

    #[test]
    fn direct_led_role_selection_emits_a_flat_infix_use() {
        let root = parse_direct("a+!b", &canonical_operator_table());
        let chain = only_child(&root, SyntaxKind::OperatorChain);
        assert_eq!(
            chain.children().map(|node| node.kind()).collect::<Vec<_>>(),
            vec![SyntaxKind::IdentifierExpression, SyntaxKind::InfixOperatorUse, SyntaxKind::IdentifierExpression]
        );
        let infix = chain.children().nth(1).unwrap();
        assert_eq!(direct_token_kinds(&infix), vec![SyntaxKind::Operator]);
        assert_eq!(infix.first_token().unwrap().text(), "+!");
    }

    #[test]
    fn fixed_field_and_path_tails_are_flat_and_bp_neutral() {
        let source = "x.foo::bar::baz";
        let chain = parse(source, &canonical_operator_table());
        assert!(matches!(
            chain.items(),
            [
                OperatorChainItem::Primary(PrimaryExpression::Identifier(x)),
                OperatorChainItem::FixedPostfix(FixedPostfixTail::Field(FieldTail { name: Recovered::Complete(field), .. })),
                OperatorChainItem::FixedPostfix(FixedPostfixTail::Path(PathTail { segment: Recovered::Complete(PathSegment::Identifier(bar)), .. })),
                OperatorChainItem::FixedPostfix(FixedPostfixTail::Path(PathTail { segment: Recovered::Complete(PathSegment::Identifier(baz)), .. })),
            ] if x.text() == "x" && field.text() == "foo" && bar.text() == "bar" && baz.text() == "baz"
        ));

        let root = parse_direct(source, &canonical_operator_table());
        let direct = only_child(&root, SyntaxKind::OperatorChain);
        assert_eq!(
            direct.children().map(|node| node.kind()).collect::<Vec<_>>(),
            vec![
                SyntaxKind::IdentifierExpression,
                SyntaxKind::FieldTail,
                SyntaxKind::PathTail,
                SyntaxKind::PathTail,
            ]
        );
        assert_eq!(root.to_string(), source);

        let low = colon_operator_table(BindingPower::scalar(1));
        let high = colon_operator_table(BindingPower::scalar(99));
        assert_eq!(parse(source, &low), parse(source, &high));
        assert_eq!(parse_direct(source, &low).green(), parse_direct(source, &high).green());
    }

    #[test]
    fn index_tails_are_flat_layout_delimited_and_bp_neutral() {
        for (source, item_count) in [
            ("a[]", 0),
            ("a[i]", 1),
            ("a[i, j]", 2),
            ("a[i; j]", 2),
            ("a[i\nj]", 2),
        ] {
            let chain = parse(source, &canonical_operator_table());
            let [OperatorChainItem::Primary(_), OperatorChainItem::FixedPostfix(FixedPostfixTail::Index(IndexTail { items, .. }))] = chain.items() else {
                panic!("expected index tail for {source:?}");
            };
            assert_eq!(items.len(), item_count, "{source:?}");
            let root = parse_direct(source, &canonical_operator_table());
            assert_eq!(root.to_string(), source, "{source:?}");
            assert_eq!(root.descendants().filter(|node| node.kind() == SyntaxKind::IndexTail).count(), 1, "{source:?}");
        }
        let source = "a[i].field(x)::name";
        let root = parse_direct(source, &canonical_operator_table());
        let chain = only_child(&root, SyntaxKind::OperatorChain);
        assert_eq!(
            chain.children().map(|node| node.kind()).collect::<Vec<_>>(),
            vec![SyntaxKind::IdentifierExpression, SyntaxKind::IndexTail, SyntaxKind::FieldTail, SyntaxKind::CallTail, SyntaxKind::PathTail],
        );
        let low = colon_operator_table(BindingPower::scalar(1));
        let high = colon_operator_table(BindingPower::scalar(99));
        assert_eq!(parse(source, &low), parse(source, &high));
        assert_eq!(parse_direct(source, &low).green(), parse_direct(source, &high).green());
    }

    #[test]
    fn index_tail_requires_adjacency_and_recovers_locally() {
        assert!(matches!(
            fixed_tail_after_identifier("a[i]"),
            Some(FixedPostfixRecognition::Index { .. })
        ));
        assert!(fixed_tail_after_identifier("a [i]").is_none());
        for source in ["a[,i]", "a[i,,j]", "a[@i]"] {
            let (root, recoveries) = parse_direct_recovered(source, &canonical_operator_table());
            assert_eq!(root.to_string(), source, "{source:?}");
            assert!(!recoveries.is_empty(), "{source:?}");
        }
        for source in ["a[i", "a[i)"] {
            let (root, recoveries) = parse_direct_recovered(source, &canonical_operator_table());
            assert_eq!(root.to_string(), source, "{source:?}");
            assert!(recoveries.iter().any(|record| {
                record.site.role == GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::IndexTail,
                    delimiter: Delimiter::Bracket,
                }
            }), "{source:?}");
        }
        let (_, recoveries) = parse_direct_recovered("a[i j]", &canonical_operator_table());
        assert!(recoveries.is_empty(), "a spaced shared NUD remains one ML item");
    }

    #[test]
    fn index_tail_restores_owner_frames_and_precedes_terminal_colon() {
        for source in ["f(a[i], b)", "a[f(b)]", "run:\n  a[i]\n  f(b)"] {
            let _ = parse(source, &canonical_operator_table());
            let root = parse_direct(source, &canonical_operator_table());
            assert_eq!(root.to_string(), source, "{source:?}");
            assert!(root.descendants().any(|node| node.kind() == SyntaxKind::IndexTail));
            assert!(!root.descendants().any(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error)));
        }
        let chain = parse("a[i]: rhs", &canonical_operator_table());
        assert!(matches!(
            chain.items(),
            [OperatorChainItem::Primary(_), OperatorChainItem::FixedPostfix(FixedPostfixTail::Index(_)), OperatorChainItem::TerminalOuter(TerminalOuterTail::ColonApplication(_))]
        ));
    }

    #[test]
    fn projection_tails_precede_field_dispatch_and_keep_general_expression_items() {
        let source = "a[i;j].(x,y).{left: value, ..rest}";
        let chain = parse(source, &canonical_operator_table());
        assert!(matches!(
            chain.items(),
            [
                OperatorChainItem::Primary(_),
                OperatorChainItem::FixedPostfix(FixedPostfixTail::Index(_)),
                OperatorChainItem::FixedPostfix(FixedPostfixTail::Projection(ProjectionTail::Tuple(ProjectionTupleTail { items: tuple_items, .. }))),
                OperatorChainItem::FixedPostfix(FixedPostfixTail::Projection(ProjectionTail::Record(ProjectionRecordTail { items: record_items, .. }))),
            ] if tuple_items.len() == 2
                && matches!(record_items.as_slice(), [ProjectionRecordItem::Expression(_), ProjectionRecordItem::Spread(_)])
        ));
        let root = parse_direct(source, &canonical_operator_table());
        assert_eq!(root.to_string(), source);
        let chain = only_child(&root, SyntaxKind::OperatorChain);
        assert_eq!(
            chain.children().map(|node| node.kind()).collect::<Vec<_>>(),
            vec![SyntaxKind::IdentifierExpression, SyntaxKind::IndexTail, SyntaxKind::ProjectionTupleTail, SyntaxKind::ProjectionRecordTail],
        );
        let record = chain.children().find(|node| node.kind() == SyntaxKind::ProjectionRecordTail).unwrap();
        assert_eq!(record.descendants().filter(|node| node.kind() == SyntaxKind::ColonApplicationTail).count(), 1);
        assert_eq!(record.children().filter(|node| node.kind() == SyntaxKind::ProjectionRecordSpreadItem).count(), 1);

        for source in ["a.()", "a.(x, y(f))", "a.{}", "a.{..left, middle, ..right}", "a .{x}", "a/*c*/.(x)"] {
            let root = parse_direct(source, &canonical_operator_table());
            assert_eq!(root.to_string(), source, "{source:?}");
            assert!(root.descendants().any(|node| matches!(node.kind(), SyntaxKind::ProjectionTupleTail | SyntaxKind::ProjectionRecordTail)), "{source:?}");
        }
        for source in ["a. (x)", "a. {x}"] {
            let root = parse_direct(source, &canonical_operator_table());
            assert_eq!(root.to_string(), source, "{source:?}");
            assert!(!root.descendants().any(|node| matches!(node.kind(), SyntaxKind::ProjectionTupleTail | SyntaxKind::ProjectionRecordTail)), "{source:?}");
        }
    }

    #[test]
    fn projection_tail_recovery_keeps_typed_slots_local() {
        let cases = [
            ("a.(,x)", ExpressionRole::ProjectionTupleItem, RecoveryKind::Missing, 3..3),
            ("a.(x,,y)", ExpressionRole::ProjectionTupleItem, RecoveryKind::Missing, 5..5),
            ("a.(@x)", ExpressionRole::ProjectionTupleItem, RecoveryKind::Error, 3..4),
            ("a.{,x}", ExpressionRole::ProjectionRecordItem, RecoveryKind::Missing, 3..3),
            ("a.{..}", ExpressionRole::ProjectionRecordSpreadRhs, RecoveryKind::Missing, 5..5),
            ("a.{..@rest}", ExpressionRole::ProjectionRecordSpreadRhs, RecoveryKind::Error, 5..6),
        ];
        for (source, role, kind, range) in cases {
            let (root, recoveries) = parse_direct_recovered(source, &canonical_operator_table());
            assert_eq!(root.to_string(), source, "{source:?}");
            assert!(recoveries.iter().any(|record| record.kind == kind && record.site.role == GrammarRole::Expression(role) && record.site.range == range), "{source:?}: {recoveries:?}");
        }
        for source in ["a.()", "a.(x,)", "a.(x;)", "a.(x\n)", "a.{}", "a.{..rest}", "a.{..left, middle, ..right}"] {
            let (_, recoveries) = parse_direct_recovered(source, &canonical_operator_table());
            assert!(recoveries.is_empty(), "{source:?}: {recoveries:?}");
        }
        let (_, recoveries) = parse_direct_recovered("a.(x y)", &canonical_operator_table());
        assert!(recoveries.is_empty(), "valid ML continuation stays one tuple item");
    }

    #[test]
    fn projection_tail_close_recovery_is_owner_safe_on_both_paths() {
        let eof_cases = [
            ("a.(x", ConstructRole::ProjectionTupleTail, Delimiter::Parenthesis, 4..4),
            ("a.{x", ConstructRole::ProjectionRecordTail, Delimiter::Brace, 4..4),
        ];
        for (source, owner, delimiter, range) in eof_cases {
            let (root, recoveries) = parse_direct_recovered(source, &canonical_operator_table());
            assert_eq!(root.to_string(), source, "{source:?}");
            assert!(matches!(
                recoveries.as_slice(),
                [CommittedRecoveryRecord { kind: RecoveryKind::Missing, site, .. }]
                    if site.role == GrammarRole::ClosingDelimiter { owner, delimiter }
                        && site.range == range
            ), "{source:?}: {recoveries:?}");
        }

        for (source, owner, delimiter, error_range, missing_range) in [
            ("a.(x]", ConstructRole::ProjectionTupleTail, Delimiter::Parenthesis, 4..5, 5..5),
            ("a.{x)", ConstructRole::ProjectionRecordTail, Delimiter::Brace, 4..5, 5..5),
        ] {
            let (root, recoveries) = parse_direct_recovered(source, &canonical_operator_table());
            assert_eq!(root.to_string(), source, "{source:?}");
            assert!(matches!(
                recoveries.as_slice(),
                [
                    CommittedRecoveryRecord { kind: RecoveryKind::Error, site: error_site, .. },
                    CommittedRecoveryRecord { kind: RecoveryKind::Missing, site: missing_site, .. },
                ] if error_site.role == GrammarRole::ClosingDelimiter { owner, delimiter }
                    && error_site.range == error_range
                    && missing_site.role == GrammarRole::ClosingDelimiter { owner, delimiter }
                    && missing_site.range == missing_range
            ), "{source:?}: {recoveries:?}");

            let chain = parse(source, &canonical_operator_table());
            assert_eq!(chain.range().end, source.len(), "AST recovery must consume {source:?}");
        }
    }

    #[test]
    fn record_projection_rejects_non_exact_spread_spellings() {
        for source in ["a.{...rest}", "a.{..+rest}"] {
            let root = parse_direct(source, &canonical_operator_table());
            assert_eq!(root.to_string(), source, "{source:?}");
            let record = root
                .descendants()
                .find(|node| node.kind() == SyntaxKind::ProjectionRecordTail)
                .expect("the exact projection introducer remains recognized");
            assert_eq!(
                record
                    .children()
                    .filter(|node| node.kind() == SyntaxKind::ProjectionRecordSpreadItem)
                    .count(),
                0,
                "{source:?} must not split a longer spelling into a spread marker",
            );

            let chain = parse(source, &canonical_operator_table());
            let [OperatorChainItem::Primary(_), OperatorChainItem::FixedPostfix(FixedPostfixTail::Projection(ProjectionTail::Record(record)))] = chain.items() else {
                panic!("{source:?} must remain a record projection tail: {chain:#?}");
            };
            assert!(
                !record.items.iter().any(|item| matches!(item, ProjectionRecordItem::Spread(_))),
                "{source:?} must not produce an AST spread item",
            );
        }
    }

    #[test]
    fn fixed_path_accepts_sigil_segments_and_retries_after_a_missing_segment() {
        let source = "x::::$name";
        let chain = parse(source, &canonical_operator_table());
        assert!(matches!(
            chain.items(),
            [
                OperatorChainItem::Primary(_),
                OperatorChainItem::FixedPostfix(FixedPostfixTail::Path(PathTail { segment: Recovered::Incomplete, .. })),
                OperatorChainItem::FixedPostfix(FixedPostfixTail::Path(PathTail { segment: Recovered::Complete(PathSegment::SigilIdentifier(name)), .. })),
            ] if name.text() == "$name"
        ));

        let (root, recoveries) = parse_direct_recovered(source, &canonical_operator_table());
        assert_eq!(root.to_string(), source);
        assert!(matches!(
            recoveries.as_slice(),
            [CommittedRecoveryRecord { kind: RecoveryKind::Missing, site, .. }]
                if site.role == GrammarRole::Expression(ExpressionRole::PathSegment)
                    && site.range == (3..3)
        ));
        assert_eq!(root.descendants().filter(|node| node.kind() == SyntaxKind::PathTail).count(), 2);
    }

    #[test]
    fn fixed_tail_recovery_keeps_missing_and_invalid_rhs_local() {
        for (source, role, kind, range) in [
            ("x.", ExpressionRole::FieldName, RecoveryKind::Missing, 2..2),
            ("x.@", ExpressionRole::FieldName, RecoveryKind::Error, 2..3),
            ("x::", ExpressionRole::PathSegment, RecoveryKind::Missing, 3..3),
            ("x::123", ExpressionRole::PathSegment, RecoveryKind::Error, 3..6),
        ] {
            let (root, recoveries) = parse_direct_recovered(source, &canonical_operator_table());
            assert_eq!(root.to_string(), source, "{source:?}");
            assert!(matches!(
                recoveries.as_slice(),
                [CommittedRecoveryRecord { kind: actual_kind, site, .. }]
                    if *actual_kind == kind
                        && site.role == GrammarRole::Expression(role)
                        && site.range == range
            ), "{source:?}: {recoveries:?}");
        }

        for source in ["x..", "x..."] {
            assert!(fixed_tail_after_identifier(source).is_none(), "{source:?}");
        }

        let source = "x.@+! y";
        let (root, recoveries) = parse_direct_recovered(source, &canonical_operator_table());
        assert_eq!(root.to_string(), source);
        assert!(matches!(
            recoveries.as_slice(),
            [CommittedRecoveryRecord { kind: RecoveryKind::Error, site, .. }]
                if site.role == GrammarRole::Expression(ExpressionRole::FieldName)
                    && site.range == (2..3)
        ));
        assert_eq!(root.descendants().filter(|node| node.kind() == SyntaxKind::InfixOperatorUse).count(), 1);
    }

    #[test]
    fn fixed_tails_precede_the_terminal_colon_and_dynamic_operators() {
        let colon = parse("x.foo: rhs", &canonical_operator_table());
        assert!(matches!(
            colon.items(),
            [
                OperatorChainItem::Primary(_),
                OperatorChainItem::FixedPostfix(FixedPostfixTail::Field(_)),
                OperatorChainItem::TerminalOuter(TerminalOuterTail::ColonApplication(_)),
            ]
        ));

        let source = "a.b +! c.d";
        let root = parse_direct(source, &canonical_operator_table());
        assert_eq!(root.to_string(), source);
        assert_eq!(root.descendants().filter(|node| node.kind() == SyntaxKind::FieldTail).count(), 2);
        assert_eq!(root.descendants().filter(|node| node.kind() == SyntaxKind::InfixOperatorUse).count(), 1);
    }

    #[test]
    fn call_tail_uses_adjacent_opener_and_layout_boundaries() {
        for (source, argument_count, literal_separators) in [
            ("f()", 0, 0),
            ("f(a,b;c)", 3, 2),
            ("f(a\nb)", 2, 0),
            ("f(a,\nb)", 2, 1),
            ("f(a\n)", 1, 0),
            ("f(a\n  b)", 1, 0),
            ("f(a;)", 1, 1),
        ] {
            let chain = parse(source, &canonical_operator_table());
            assert!(matches!(
                chain.items(),
                [OperatorChainItem::Primary(_), OperatorChainItem::FixedPostfix(FixedPostfixTail::Call(CallTail { arguments, .. }))]
                    if arguments.len() == argument_count
            ), "{source:?}");
            let root = parse_direct(source, &canonical_operator_table());
            assert_eq!(root.to_string(), source);
            let call = root.descendants().find(|node| node.kind() == SyntaxKind::CallTail).unwrap();
            assert_eq!(call.children().filter(|node| node.kind() == SyntaxKind::OperatorChain).count(), argument_count, "{source:?}");
            assert_eq!(call.children_with_tokens().filter(|child| matches!(child.kind(), SyntaxKind::Comma | SyntaxKind::Semicolon)).count(), literal_separators, "{source:?}");
        }
    }

    #[test]
    fn call_tail_recovers_missing_arguments_and_closing_delimiter() {
        for (source, expected_missing) in [("f(,a)", 1), ("f(a,,b)", 1), ("f(a", 1)] {
            let (root, recoveries) = parse_direct_recovered(source, &canonical_operator_table());
            assert_eq!(root.to_string(), source, "{source:?}");
            assert_eq!(recoveries.iter().filter(|record| record.kind == RecoveryKind::Missing).count(), expected_missing, "{source:?}");
        }
        let chain = parse("f(,a)", &canonical_operator_table());
        assert!(matches!(
            chain.items(),
            [OperatorChainItem::Primary(_), OperatorChainItem::FixedPostfix(FixedPostfixTail::Call(CallTail { arguments, .. }))]
                if matches!(arguments.as_slice(), [OperatorChain { items, .. }, _] if matches!(items.as_slice(), [OperatorChainItem::MissingOperand { .. }]))
        ));

        let chain = parse("f(@a)", &canonical_operator_table());
        assert!(matches!(
            chain.items(),
            [
                OperatorChainItem::Primary(_),
                OperatorChainItem::FixedPostfix(FixedPostfixTail::Call(CallTail { arguments, .. })),
            ] if matches!(
                arguments.as_slice(),
                [
                    OperatorChain { items: malformed, range: malformed_range },
                    OperatorChain { items: valid, .. },
                ] if matches!(malformed.as_slice(), [OperatorChainItem::Error { range }]
                    if *range == (2..3) && *malformed_range == (2..3))
                    && matches!(valid.as_slice(), [OperatorChainItem::Primary(PrimaryExpression::Identifier(word))]
                        if word.text() == "a")
            )
        ));

        let (root, recoveries) = parse_direct_recovered("f(a]", &canonical_operator_table());
        assert_eq!(root.to_string(), "f(a]");
        assert!(recoveries.iter().all(|record| matches!(
            record.site.role,
            GrammarRole::ClosingDelimiter { owner: ConstructRole::ArgumentList, delimiter: Delimiter::Parenthesis }
        )));
        assert!(recoveries.iter().any(|record| record.kind == RecoveryKind::Error && record.site.range == (3..4)));
        assert!(recoveries.iter().any(|record| record.kind == RecoveryKind::Missing && record.site.range == (4..4)));
    }

    #[test]
    fn call_and_ml_adjacency_keep_flat_source_order() {
        let cases = [
            ("f(x)", 1),
            ("f (x)", 0),
            ("f/*c*/(x)", 0),
            ("f\n  (x)", 0),
        ];
        for (source, call_count) in cases {
            let root = parse_direct(source, &canonical_operator_table());
            assert_eq!(root.to_string(), source);
            assert_eq!(root.descendants().filter(|node| node.kind() == SyntaxKind::CallTail).count(), call_count, "{source:?}");
            assert_eq!(root.descendants().filter(|node| node.kind() == SyntaxKind::MlArgument).count(), 1 - call_count, "{source:?}");
        }

        let source = "a.b(c)::d e";
        let root = parse_direct(source, &canonical_operator_table());
        let chain = only_child(&root, SyntaxKind::OperatorChain);
        assert_eq!(root.to_string(), source);
        assert_eq!(
            chain.children().map(|node| node.kind()).collect::<Vec<_>>(),
            vec![SyntaxKind::IdentifierExpression, SyntaxKind::FieldTail, SyntaxKind::CallTail, SyntaxKind::PathTail, SyntaxKind::MlArgument]
        );

        let low = colon_operator_table(BindingPower::scalar(1));
        let high = colon_operator_table(BindingPower::scalar(99));
        assert_eq!(parse(source, &low), parse(source, &high));
        assert_eq!(parse_direct(source, &low).green(), parse_direct(source, &high).green());
    }

    #[test]
    fn ml_arguments_split_on_trivia_but_keep_adjacent_fixed_tails_and_colon_terminality() {
        let chain = parse("f x y", &canonical_operator_table());
        assert!(matches!(chain.items(), [OperatorChainItem::Primary(_), OperatorChainItem::MlArgument { .. }, OperatorChainItem::MlArgument { .. }]));
        let root = parse_direct("f x y", &canonical_operator_table());
        let chain = only_child(&root, SyntaxKind::OperatorChain);
        let ml_arguments = chain.children().filter(|node| node.kind() == SyntaxKind::MlArgument).collect::<Vec<_>>();
        assert_eq!(ml_arguments.len(), 2);
        for argument in ml_arguments {
            let nested = only_child(&argument, SyntaxKind::OperatorChain);
            assert_eq!(nested.children().count(), 1);
            assert_eq!(nested.first_child().unwrap().kind(), SyntaxKind::IdentifierExpression);
        }

        let root = parse_direct("f x.field(y)::z", &canonical_operator_table());
        assert_eq!(root.to_string(), "f x.field(y)::z");
        let ml = root.descendants().find(|node| node.kind() == SyntaxKind::MlArgument).unwrap();
        assert_eq!(ml.children().filter(|node| node.kind() == SyntaxKind::OperatorChain).count(), 1);
        assert_eq!(ml.descendants().filter(|node| node.kind() == SyntaxKind::FieldTail).count(), 1);
        assert_eq!(ml.descendants().filter(|node| node.kind() == SyntaxKind::CallTail).count(), 1);

        let colon = parse("f x: rhs", &canonical_operator_table());
        assert!(matches!(colon.items(), [OperatorChainItem::Primary(_), OperatorChainItem::MlArgument { .. }, OperatorChainItem::TerminalOuter(TerminalOuterTail::ColonApplication(_))]));
    }

    #[test]
    fn call_and_ml_recovery_keep_owner_boundaries_local() {
        let (root, recoveries) = parse_direct_recovered("f(@a)", &canonical_operator_table());
        assert_eq!(root.to_string(), "f(@a)");
        assert!(matches!(
            recoveries.as_slice(),
            [CommittedRecoveryRecord { kind: RecoveryKind::Error, site, .. }]
                if site.role == GrammarRole::Expression(ExpressionRole::CallArgument)
                    && site.range == (2..3)
        ));

        let (root, recoveries) = parse_direct_recovered("f +", &canonical_operator_table());
        assert_eq!(root.to_string(), "f +");
        assert_eq!(root.descendants().filter(|node| node.kind() == SyntaxKind::MlArgument).count(), 1);
        assert!(recoveries.iter().any(|record| record.kind == RecoveryKind::Missing));

        for source in ["f ", "f\n(x)"] {
            assert!(ml_after_identifier(source).is_none(), "{source:?}");
        }
        assert!(ml_after_identifier("f\n  (x)").is_some());
    }

    #[test]
    fn call_tail_restores_each_enclosing_owner_frame() {
        let cases = [
            ("(f(a), b)", 1, Some(SyntaxKind::ParenthesizedExpression)),
            ("f(g(x))", 2, None),
            ("case value: { field = f(a) } -> body", 1, Some(SyntaxKind::RecordPattern)),
            ("run:\n  f(a)\n  g(b)", 2, Some(SyntaxKind::IndentedStatementBlock)),
            ("case x: p -> f(a), q -> g(b)", 2, Some(SyntaxKind::CaseArm)),
            ("catch x { p -> f(a), q -> g(b) }", 2, Some(SyntaxKind::CatchArm)),
        ];

        for (source, expected_calls, enclosing_owner) in cases {
            let _ = parse(source, &canonical_operator_table());
            let root = parse_direct(source, &canonical_operator_table());
            assert_eq!(root.to_string(), source, "{source:?}");
            assert_eq!(
                root.descendants().filter(|node| node.kind() == SyntaxKind::CallTail).count(),
                expected_calls,
                "{source:?}",
            );
            if let Some(owner) = enclosing_owner {
                assert!(root.descendants().any(|node| node.kind() == owner), "{source:?}");
            }
            assert!(
                root.descendants().all(|node| !matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error)),
                "{source:?}",
            );
        }
    }

    #[test]
    fn direct_chain_assigns_accepted_led_trivia_once() {
        let root = parse_direct("a +! b", &canonical_operator_table());
        let chain = only_child(&root, SyntaxKind::OperatorChain);

        assert_eq!(
            chain
                .children_with_tokens()
                .map(|child| child.kind())
                .collect::<Vec<_>>(),
            vec![
                SyntaxKind::IdentifierExpression,
                SyntaxKind::Whitespace,
                SyntaxKind::InfixOperatorUse,
                SyntaxKind::Whitespace,
                SyntaxKind::IdentifierExpression,
            ]
        );
        assert_eq!(root.to_string(), "a +! b");
    }

    #[test]
    fn direct_chain_emits_suffix_and_nullfix_use_nodes() {
        let table = canonical_operator_table();

        let suffix_root = parse_direct("a++", &table);
        let suffix_chain = only_child(&suffix_root, SyntaxKind::OperatorChain);
        let suffix = suffix_chain.children().nth(1).unwrap();
        assert_eq!(suffix.kind(), SyntaxKind::SuffixOperatorUse);
        assert_eq!(suffix_chain.to_string(), "a++");
        assert_eq!(
            suffix
                .children_with_tokens().map(|child| child.kind()).collect::<Vec<_>>(),
            vec![SyntaxKind::Operator]
        );

        let nullfix_root = parse_direct("!", &table);
        let nullfix_chain = only_child(&nullfix_root, SyntaxKind::OperatorChain);
        let nullfix = only_child(&nullfix_chain, SyntaxKind::NullfixOperatorUse);
        assert_eq!(nullfix_chain.to_string(), "!");
        assert_eq!(direct_token_kinds(&nullfix), vec![SyntaxKind::Operator]);
    }

    #[test]
    fn direct_chain_emits_parenthesized_trivia_and_nested_nodes_losslessly() {
        let source = "(\n/* note */ (a), b, \n)";
        let root = parse_direct(source, &canonical_operator_table());
        let outer_chain = only_child(&root, SyntaxKind::OperatorChain);
        let parenthesized = only_child(&outer_chain, SyntaxKind::ParenthesizedExpression);

        assert_eq!(parenthesized.to_string(), source);
        assert_eq!(
            parenthesized
                .children_with_tokens()
                .map(|child| child.kind())
                .collect::<Vec<_>>(),
            vec![
                SyntaxKind::LParen,
                SyntaxKind::Newline,
                SyntaxKind::BlockComment,
                SyntaxKind::Whitespace,
                SyntaxKind::OperatorChain,
                SyntaxKind::Comma,
                SyntaxKind::Whitespace,
                SyntaxKind::OperatorChain,
                SyntaxKind::Comma,
                SyntaxKind::Whitespace,
                SyntaxKind::Newline,
                SyntaxKind::RParen,
            ]
        );
        assert_eq!(
            parenthesized.children().next().unwrap().children().next().unwrap().kind(),
            SyntaxKind::ParenthesizedExpression,
        );
    }

    #[test]
    fn direct_chain_uses_one_parenthesized_node_for_every_valid_list_shape() {
        let cases = [
            ("()", vec![SyntaxKind::LParen, SyntaxKind::RParen]),
            (
                "(a)",
                vec![
                    SyntaxKind::LParen,
                    SyntaxKind::OperatorChain,
                    SyntaxKind::RParen,
                ],
            ),
            (
                "(a,)",
                vec![
                    SyntaxKind::LParen,
                    SyntaxKind::OperatorChain,
                    SyntaxKind::Comma,
                    SyntaxKind::RParen,
                ],
            ),
            (
                "(a,b)",
                vec![
                    SyntaxKind::LParen,
                    SyntaxKind::OperatorChain,
                    SyntaxKind::Comma,
                    SyntaxKind::OperatorChain,
                    SyntaxKind::RParen,
                ],
            ),
            (
                "(a,b,)",
                vec![
                    SyntaxKind::LParen,
                    SyntaxKind::OperatorChain,
                    SyntaxKind::Comma,
                    SyntaxKind::OperatorChain,
                    SyntaxKind::Comma,
                    SyntaxKind::RParen,
                ],
            ),
        ];

        for (source, expected_children) in cases {
            let root = parse_direct(source, &canonical_operator_table());
            let chain = only_child(&root, SyntaxKind::OperatorChain);
            let parenthesized = only_child(&chain, SyntaxKind::ParenthesizedExpression);
            assert_eq!(parenthesized.to_string(), source, "{source:?}");
            assert_eq!(
                parenthesized
                    .children_with_tokens()
                    .map(|child| child.kind())
                    .collect::<Vec<_>>(),
                expected_children,
                "{source:?}"
            );
        }
    }

    #[test]
    fn parenthesized_primary_continues_to_outer_infix_and_suffix_uses() {
        let expression = parse("(a+!b)*c", &canonical_operator_table());
        assert!(matches!(
            expression.items(),
            [
                OperatorChainItem::Primary(PrimaryExpression::Parenthesized { elements, .. }),
                OperatorChainItem::InfixUse(operator),
                OperatorChainItem::Primary(PrimaryExpression::Identifier(_)),
            ] if operator.text() == "*" && matches!(elements.as_slice(), [OperatorChain { items, .. }]
                if matches!(items.as_slice(), [OperatorChainItem::Primary(_), OperatorChainItem::InfixUse(_), OperatorChainItem::Primary(_)]))
        ));
        let root = parse_direct("(a+!b)*c", &canonical_operator_table());
        let outer = only_child(&root, SyntaxKind::OperatorChain);
        assert_eq!(
            outer.children().next().expect("left operand").kind(),
            SyntaxKind::ParenthesizedExpression
        );
        assert_eq!(outer.children().nth(1).unwrap().kind(), SyntaxKind::InfixOperatorUse);

        let suffix = parse_direct("(a)++", &canonical_operator_table());
        let suffix = only_child(&suffix, SyntaxKind::OperatorChain);
        assert_eq!(
            suffix.children().next()
                .expect("parenthesized operand")
                .kind(),
            SyntaxKind::ParenthesizedExpression
        );
        assert_eq!(suffix.children().nth(1).unwrap().kind(), SyntaxKind::SuffixOperatorUse);
    }

    #[test]
    fn operator_chain_ast_preserves_source_order_without_application_edges() {
        let chain = parse("+!a+!b++", &canonical_operator_table());
        assert_eq!(chain.range(), 0..8);
        assert!(matches!(
            chain.items(),
            [
                OperatorChainItem::PrefixUse(prefix),
                OperatorChainItem::PrefixUse(nested_prefix),
                OperatorChainItem::Primary(PrimaryExpression::Identifier(_)),
                OperatorChainItem::InfixUse(infix),
                OperatorChainItem::Primary(PrimaryExpression::Identifier(_)),
                OperatorChainItem::SuffixUse(suffix),
            ] if prefix.text() == "+" && nested_prefix.text() == "!" && infix.text() == "+!" && suffix.text() == "++"
        ));
    }

    #[test]
    fn direct_chain_emits_role_nodes_and_keeps_operator_trivia_outside_them() {
        let root = parse_direct("+!a +! b++", &canonical_operator_table());
        let chain = only_child(&root, SyntaxKind::OperatorChain);
        assert_eq!(chain.to_string(), "+!a +! b++");
        assert_eq!(
            chain.children_with_tokens().map(|child| child.kind()).collect::<Vec<_>>(),
            vec![
                SyntaxKind::PrefixOperatorUse,
                SyntaxKind::PrefixOperatorUse,
                SyntaxKind::IdentifierExpression,
                SyntaxKind::Whitespace,
                SyntaxKind::InfixOperatorUse,
                SyntaxKind::Whitespace,
                SyntaxKind::IdentifierExpression,
                SyntaxKind::SuffixOperatorUse,
            ]
        );
        for use_kind in [
            SyntaxKind::PrefixOperatorUse,
            SyntaxKind::InfixOperatorUse,
            SyntaxKind::SuffixOperatorUse,
        ] {
            for node in chain.children().filter(|node| node.kind() == use_kind) {
                assert_eq!(direct_token_kinds(&node), vec![SyntaxKind::Operator]);
            }
        }
    }

    #[test]
    fn colon_application_ast_and_cst_keep_inline_arguments_in_the_terminal_tail() {
        let chain = parse("f: x, y", &canonical_operator_table());
        assert!(matches!(
            chain.items(),
            [
                OperatorChainItem::Primary(PrimaryExpression::Identifier(target)),
                OperatorChainItem::TerminalOuter(TerminalOuterTail::ColonApplication(
                    ColonApplicationTail {
                        colon,
                        rhs: Recovered::Complete(ColonApplicationRhs::Inline { arguments }),
                        range,
                    }
                )),
            ] if target.text() == "f" && *colon == (1..2) && arguments.len() == 2 && *range == (1..7)
        ));

        let root = parse_direct("f: x, y", &canonical_operator_table());
        let chain = only_child(&root, SyntaxKind::OperatorChain);
        let tail = chain.children().nth(1).expect("terminal colon tail");
        assert_eq!(tail.kind(), SyntaxKind::ColonApplicationTail);
        assert_eq!(
            tail.children_with_tokens()
                .map(|child| child.kind())
                .collect::<Vec<_>>(),
            vec![
                SyntaxKind::Colon,
                SyntaxKind::Whitespace,
                SyntaxKind::OperatorChain,
                SyntaxKind::Comma,
                SyntaxKind::Whitespace,
                SyntaxKind::OperatorChain,
            ]
        );
    }

    #[test]
    fn colon_inline_newline_arguments_have_ast_direct_and_bp_parity() {
        let source = "f: a\nb";
        let chain = parse(source, &canonical_operator_table());
        assert!(matches!(
            chain.items(),
            [
                OperatorChainItem::Primary(PrimaryExpression::Identifier(_)),
                OperatorChainItem::TerminalOuter(TerminalOuterTail::ColonApplication(
                    ColonApplicationTail {
                        rhs: Recovered::Complete(ColonApplicationRhs::Inline { arguments }),
                        ..
                    }
                )),
            ] if arguments.len() == 2
        ));

        let root = parse_direct(source, &canonical_operator_table());
        let tail = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ColonApplicationTail)
            .expect("colon tail");
        assert_eq!(tail.to_string(), ": a\nb");
        assert_eq!(tail.children().filter(|node| node.kind() == SyntaxKind::OperatorChain).count(), 2);
        assert_eq!(root.to_string(), source);

        let low = colon_operator_table(BindingPower::scalar(1));
        let high = colon_operator_table(BindingPower::scalar(99));
        assert_eq!(parse(source, &low), parse(source, &high));
        assert_eq!(parse_direct(source, &low).green(), parse_direct(source, &high).green());
    }

    #[test]
    fn outer_parenthesized_sequence_owns_colon_newline_boundary() {
        let source = "(f: a\nb)";
        let chain = parse(source, &canonical_operator_table());
        let [OperatorChainItem::Primary(PrimaryExpression::Parenthesized { elements, .. })] = chain.items()
        else {
            panic!("expected parenthesized expression");
        };
        assert_eq!(elements.len(), 2);
        let [
            OperatorChainItem::Primary(_),
            OperatorChainItem::TerminalOuter(TerminalOuterTail::ColonApplication(
                ColonApplicationTail {
                    rhs: Recovered::Complete(ColonApplicationRhs::Inline { arguments }),
                    ..
                }
            )),
        ] = elements[0].items()
        else {
            panic!("expected colon tail in first outer element");
        };
        assert_eq!(arguments.len(), 1);

        let root = parse_direct(source, &canonical_operator_table());
        let outer = only_child(&root, SyntaxKind::OperatorChain);
        let group = only_child(&outer, SyntaxKind::ParenthesizedExpression);
        let elements = group
            .children()
            .filter(|node| node.kind() == SyntaxKind::OperatorChain)
            .collect::<Vec<_>>();
        assert_eq!(elements.len(), 2);
        let tail = elements[0]
            .children()
            .find(|node| node.kind() == SyntaxKind::ColonApplicationTail)
            .expect("first outer element owns the colon tail");
        assert!(!tail.children_with_tokens().any(|child| child.kind() == SyntaxKind::Newline));
        assert_eq!(group.to_string(), source);
    }

    #[test]
    fn parenthesized_outer_comma_limits_a_colon_tail_to_one_argument() {
        let root = parse_direct("(f: x, y)", &canonical_operator_table());
        let outer = only_child(&root, SyntaxKind::OperatorChain);
        let group = only_child(&outer, SyntaxKind::ParenthesizedExpression);
        let elements = group
            .children()
            .filter(|node| node.kind() == SyntaxKind::OperatorChain)
            .collect::<Vec<_>>();
        assert_eq!(elements.len(), 2);
        assert!(elements[0]
            .children()
            .any(|node| node.kind() == SyntaxKind::ColonApplicationTail));
        assert!(!elements[1]
            .children()
            .any(|node| node.kind() == SyntaxKind::ColonApplicationTail));
    }

    #[test]
    fn colon_application_recovery_keeps_commas_and_retries_valid_values() {
        let cases = [
            ("f:", vec![(RecoveryKind::Missing, 2..2)]),
            ("f: ,x", vec![(RecoveryKind::Missing, 3..3)]),
            ("f: x,", vec![(RecoveryKind::Missing, 5..5)]),
            ("f: @x", vec![(RecoveryKind::Error, 3..4)]),
        ];

        for (source, expected) in cases {
            let (root, recoveries) = parse_direct_recovered(source, &canonical_operator_table());
            assert_eq!(root.to_string(), source, "{source:?}");
            assert_eq!(
                recoveries
                    .iter()
                    .map(|recovery| (recovery.kind, recovery.site.range.clone()))
                    .collect::<Vec<_>>(),
                expected,
                "{source:?}"
            );
            assert!(recoveries.iter().all(|recovery| {
                matches!(
                    recovery.site.role,
                    GrammarRole::ColonApplication(ColonApplicationRole::Rhs)
                        | GrammarRole::ColonApplication(ColonApplicationRole::InlineArgument)
                )
            }));
        }
    }

    #[test]
    fn colon_application_parses_an_indented_statement_block() {
        let source = "my value = f:\n  x\n  y";
        let output = crate::grammar::declaration::parse_direct_root_candidate(
            source,
            &canonical_operator_table(),
            &[],
        );
        let root = SyntaxNode::new_root(output.green().clone());
        let block = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
            .expect("indented statement block");
        assert_eq!(block.to_string(), "\n  x\n  y");
        assert_eq!(
            block.children().map(|node| node.kind()).collect::<Vec<_>>(),
            vec![
                SyntaxKind::Statement,
                SyntaxKind::BlockStatementSeparator,
                SyntaxKind::Statement,
            ]
        );
        assert_eq!(root.to_string(), source);

        let chain = parse("f:\n  x\n  y", &canonical_operator_table());
        let [_, OperatorChainItem::TerminalOuter(TerminalOuterTail::ColonApplication(
            ColonApplicationTail {
                rhs: Recovered::Complete(ColonApplicationRhs::Indented { block }),
                ..
            }
        ))] = chain.items()
        else {
            panic!("expected an indented colon RHS");
        };
        assert_eq!(block.base_indent, 0);
        assert_eq!(block.block_indent, 2);
        assert_eq!(block.statements.len(), 2);
    }

    #[test]
    fn braced_statement_block_is_a_primary_with_all_separator_forms() {
        for (source, statements, separator_token) in [
            ("{}", 0, None),
            ("{ }", 0, None),
            ("{\n}", 0, None),
            ("{x}", 1, None),
            ("{x,y}", 2, Some(SyntaxKind::Comma)),
            ("{x;y}", 2, Some(SyntaxKind::Semicolon)),
            ("{x\ny}", 2, None),
            ("{x,}", 1, Some(SyntaxKind::Comma)),
            ("{x;}", 1, Some(SyntaxKind::Semicolon)),
            ("{x\n}", 1, None),
        ] {
            let root = parse_direct(source, &canonical_operator_table());
            let block = root
                .descendants()
                .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
                .expect("braced statement block");
            assert_eq!(root.to_string(), source, "{source:?}");
            assert_eq!(
                block.children().filter(|node| node.kind() == SyntaxKind::Statement).count(),
                statements,
                "{source:?}"
            );
            if statements > 1 || separator_token.is_some() && source != "{ }" {
                assert_eq!(
                    block.children().filter(|node| node.kind() == SyntaxKind::BlockStatementSeparator).count(),
                    if statements > 1 { 1 } else { 1 },
                    "{source:?}"
                );
            }
            if let Some(token_kind) = separator_token {
                assert!(block
                    .descendants_with_tokens()
                    .filter_map(|element| element.into_token())
                    .any(|token| token.kind() == token_kind));
            }
            assert!(!block.descendants().any(|node| node.kind() == SyntaxKind::Missing));
        }
    }

    #[test]
    fn braced_statement_block_ast_keeps_statement_count_close_and_range() {
        let chain = parse("{x,y}", &canonical_operator_table());
        let [OperatorChainItem::Primary(PrimaryExpression::BracedStatementBlock(block))] = chain.items()
        else {
            panic!("expected braced statement-block primary");
        };
        assert_eq!(block.open, 0..1);
        assert_eq!(block.statements.len(), 2);
        assert_eq!(block.close, Recovered::Complete(4..5));
        assert_eq!(block.range, 0..5);
    }

    #[test]
    fn braced_statement_block_is_binding_power_invariant_and_keeps_deeper_newlines_local() {
        let source = "{x +\n  y\nz}";
        let low = colon_operator_table(BindingPower::scalar(1));
        let high = colon_operator_table(BindingPower::scalar(99));
        assert_eq!(parse_direct(source, &low).green(), parse_direct(source, &high).green());
        assert_eq!(parse(source, &low), parse(source, &high));

        let root = parse_direct(source, &low);
        let block = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
            .unwrap();
        assert_eq!(block.children().filter(|node| node.kind() == SyntaxKind::Statement).count(), 2);
        assert_eq!(block.children().filter(|node| node.kind() == SyntaxKind::BlockStatementSeparator).count(), 1);
    }

    #[test]
    fn braced_statement_block_keeps_colon_arguments_and_outer_chain_flat() {
        let root = parse_direct("+{x: 1, y: 2}*z", &canonical_operator_table());
        let chain = only_child(&root, SyntaxKind::OperatorChain);
        assert_eq!(
            chain.children().map(|node| node.kind()).collect::<Vec<_>>(),
            vec![
                SyntaxKind::PrefixOperatorUse,
                SyntaxKind::BracedStatementBlockExpression,
                SyntaxKind::InfixOperatorUse,
                SyntaxKind::IdentifierExpression,
            ]
        );
        let block = chain
            .children()
            .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
            .unwrap();
        assert_eq!(block.descendants().filter(|node| node.kind() == SyntaxKind::ColonApplicationTail).count(), 2);
        assert_eq!(block.descendants().filter(|node| node.kind() == SyntaxKind::BlockStatementSeparator).count(), 1);
        assert_eq!(root.to_string(), "+{x: 1, y: 2}*z");
    }

    #[test]
    fn braced_statement_block_recovers_mandatory_slots_and_close() {
        let cases = [
            ("{", vec![(RecoveryKind::Missing, 1..1)]),
            ("{x", vec![(RecoveryKind::Missing, 2..2)]),
            ("{x,", vec![(RecoveryKind::Missing, 3..3)]),
            ("{x y}", vec![(RecoveryKind::Missing, 3..3)]),
            ("{x,,y}", vec![(RecoveryKind::Missing, 3..3)]),
            ("{x,@ y}", vec![(RecoveryKind::Error, 3..5)]),
            ("{x]}", vec![(RecoveryKind::Error, 2..3)]),
        ];
        for (source, expected) in cases {
            let (root, recoveries) = parse_direct_recovered(source, &canonical_operator_table());
            assert_eq!(root.to_string(), source, "{source:?}");
            assert_eq!(
                recoveries.iter().map(|record| (record.kind, record.site.range.clone())).collect::<Vec<_>>(),
                expected,
                "{source:?}"
            );
        }
    }


    #[test]
    fn indented_block_accepts_a_semicolon_separator() {
        let root = parse_direct("f:\n  x; y", &canonical_operator_table());
        let block = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
            .expect("indented block");
        assert!(block
            .descendants()
            .any(|node| node.kind() == SyntaxKind::BlockStatementSeparator));
        assert_eq!(root.to_string(), "f:\n  x; y");
    }

    #[test]
    fn equal_indent_after_colon_leaves_newline_with_the_outer_owner() {
        let source = "my value = f:\nx";
        let output = crate::grammar::declaration::parse_direct_root_candidate(
            source,
            &canonical_operator_table(),
            &[],
        );
        let root = SyntaxNode::new_root(output.green().clone());
        let tail = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ColonApplicationTail)
            .expect("colon tail");
        assert!(tail.children().any(|node| node.kind() == SyntaxKind::Missing));
        assert!(!tail
            .children_with_tokens()
            .any(|child| child.kind() == SyntaxKind::Newline));
        assert_eq!(tail.to_string(), ":");
        assert_eq!(root.to_string(), source);
    }

    #[test]
    fn dedent_ends_an_indented_block_without_consuming_the_boundary() {
        let source = "my value = f:\n  x\nz";
        let output = crate::grammar::declaration::parse_direct_root_candidate(
            source,
            &canonical_operator_table(),
            &[],
        );
        let root = SyntaxNode::new_root(output.green().clone());
        let block = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
            .expect("indented block");
        assert_eq!(block.to_string(), "\n  x");
        assert_eq!(root.to_string(), source);
    }

    #[test]
    fn indented_block_recovers_a_missing_or_malformed_statement_once() {
        let cases = [
            ("f:\n  ", vec![(RecoveryKind::Missing, 5..5)]),
            ("f:\n  @x", vec![(RecoveryKind::Error, 5..6)]),
        ];
        for (source, expected) in cases {
            let (root, recoveries) = parse_direct_recovered(source, &canonical_operator_table());
            assert_eq!(root.to_string(), source, "{source:?}");
            assert_eq!(
                recoveries
                    .iter()
                    .map(|record| (record.kind, record.site.range.clone()))
                    .collect::<Vec<_>>(),
                expected,
                "{source:?}"
            );
            assert!(recoveries.iter().all(|record| {
                record.site.role
                    == GrammarRole::ColonApplication(ColonApplicationRole::IndentedStatement)
            }));
        }
    }

    #[test]
    fn indented_block_restores_layout_and_parenthesized_scopes() {
        let source = "f:\n  (x)";
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        {
            let i = In::new(
                &mut source_input,
                &mut expectations,
                IsCut::new(&mut is_cut),
            )
            .set_local(&mut local);
            let mut committed = Probe::new(i).commit(FullCstOutput::new(source));
            committed.start_node(SyntaxKind::Root);
            parse_direct_expression_with_operators(
                &canonical_operator_table(),
                LeadingTrivia::None,
                &mut committed,
            )
            .expect("nested block expression");
            committed.finish_node();
            let root = SyntaxNode::new_root(committed.into_output().finish_complete());
            assert_eq!(root.to_string(), source);
        }
        assert_eq!(local.indentation_baseline(), None);
        assert!(!local.inline());
        assert!(!local.ml_arg());
        assert_eq!(local.stop_set(), None);
    }

    #[test]
    fn colon_block_surface_is_binding_power_independent() {
        let source = "f:\n  x\n  y";
        let low = colon_operator_table(BindingPower::scalar(1));
        let high = colon_operator_table(BindingPower::scalar(99));
        assert_eq!(parse_direct(source, &low).green(), parse_direct(source, &high).green());
        assert_eq!(parse(source, &low), parse(source, &high));
    }

    #[test]
    fn colon_tail_stays_flat_before_and_after_binding_power_changes() {
        let source = "a + b: x";
        let low = colon_operator_table(BindingPower::scalar(1));
        let high = colon_operator_table(BindingPower::scalar(99));

        let root = parse_direct(source, &low);
        let chain = only_child(&root, SyntaxKind::OperatorChain);
        assert_eq!(
            chain.children().map(|child| child.kind()).collect::<Vec<_>>(),
            vec![
                SyntaxKind::IdentifierExpression,
                SyntaxKind::InfixOperatorUse,
                SyntaxKind::IdentifierExpression,
                SyntaxKind::ColonApplicationTail,
            ]
        );
        assert_eq!(parse_direct(source, &low).green(), parse_direct(source, &high).green());
        assert_eq!(parse(source, &low), parse(source, &high));
    }

    #[test]
    fn binding_power_only_changes_do_not_change_surface_chain() {
        let source = "+!a+!b*c++";
        let low = canonical_operator_table();
        let high = OperatorTable::from_declarations([
            OperatorDeclaration::new("+!", OperatorFixities::new().with_infix(BindingPower::scalar(99), BindingPower::scalar(-99))),
            OperatorDeclaration::new("+", OperatorFixities::new().with_prefix(BindingPower::scalar(-90))),
            OperatorDeclaration::new("!", OperatorFixities::new().with_prefix(BindingPower::scalar(100)).with_nullfix()),
            OperatorDeclaration::new("++", OperatorFixities::new().with_suffix(BindingPower::scalar(-80))),
            OperatorDeclaration::new("*", OperatorFixities::new().with_infix(BindingPower::scalar(-70), BindingPower::scalar(70))),
        ]).expect("same recognition table");
        assert_eq!(parse_direct(source, &low).green(), parse_direct(source, &high).green());
        assert_eq!(parse(source, &low), parse(source, &high));
    }

    #[test]
    fn parenthesized_elements_are_operator_chains_and_outer_continues_flatly() {
        let chain = parse("(a+!b)*c", &canonical_operator_table());
        assert!(matches!(chain.items(), [
            OperatorChainItem::Primary(PrimaryExpression::Parenthesized { elements, .. }),
            OperatorChainItem::InfixUse(_),
            OperatorChainItem::Primary(PrimaryExpression::Identifier(_)),
        ] if matches!(elements.as_slice(), [OperatorChain { items, .. }] if matches!(items.as_slice(), [OperatorChainItem::Primary(_), OperatorChainItem::InfixUse(_), OperatorChainItem::Primary(_)]))));
        let root = parse_direct("(a+!b)*c", &canonical_operator_table());
        let chain = only_child(&root, SyntaxKind::OperatorChain);
        assert_eq!(chain.children().next().expect("primary").kind(), SyntaxKind::ParenthesizedExpression);
    }

    #[test]
    fn dangling_infix_preserves_the_use_and_emits_one_zero_width_missing_operand() {
        let (root, recoveries) = parse_direct_recovered("a+!", &canonical_operator_table());
        let chain = only_child(&root, SyntaxKind::OperatorChain);
        assert!(chain.children().any(|node| node.kind() == SyntaxKind::InfixOperatorUse));
        assert_eq!(
            recoveries.iter().map(|record| (record.kind, record.site.range.clone())).collect::<Vec<_>>(),
            vec![(RecoveryKind::Missing, 3..3)]
        );
    }

    #[test]
    fn dangling_prefix_preserves_the_use_and_emits_one_zero_width_missing_operand() {
        let (root, recoveries) = parse_direct_recovered("+", &canonical_operator_table());
        let chain = only_child(&root, SyntaxKind::OperatorChain);
        assert!(chain.children().any(|node| node.kind() == SyntaxKind::PrefixOperatorUse));
        assert_eq!(
            recoveries.iter().map(|record| (record.kind, record.site.range.clone())).collect::<Vec<_>>(),
            vec![(RecoveryKind::Missing, 1..1)]
        );
    }

    #[test]
    fn dangling_infix_stops_before_parenthesis_close() {
        let (root, recoveries) = parse_direct_recovered("(a+!)", &canonical_operator_table());
        assert_eq!(root.to_string(), "(a+!)");
        assert_eq!(
            recoveries.iter().map(|record| (record.kind, record.site.range.clone())).collect::<Vec<_>>(),
            vec![(RecoveryKind::Missing, 4..4)]
        );
    }

    #[test]
    fn direct_parenthesized_expression_recovers_mandatory_slots_without_duplicate_absences() {
        let cases = [
            ("()", Vec::new()),
            ("(value", vec![(RecoveryKind::Missing, 6..6)]),
            (
                "(a]",
                vec![(RecoveryKind::Error, 2..3), (RecoveryKind::Missing, 3..3)],
            ),
            ("(", vec![(RecoveryKind::Missing, 1..1)]),
            ("(@a)", vec![(RecoveryKind::Error, 1..2)]),
            (
                "(@",
                vec![(RecoveryKind::Error, 1..2), (RecoveryKind::Missing, 2..2)],
            ),
            ("(a,,b)", vec![(RecoveryKind::Missing, 3..3)]),
            (
                "(a,",
                vec![(RecoveryKind::Missing, 3..3), (RecoveryKind::Missing, 3..3)],
            ),
        ];

        for (source, expected) in cases {
            let (root, recoveries) = parse_direct_recovered(source, &canonical_operator_table());
            assert_eq!(root.to_string(), source, "{source:?}");
            assert_eq!(
                recoveries
                    .iter()
                    .map(|recovery| (recovery.kind, recovery.site.range.clone()))
                    .collect::<Vec<_>>(),
                expected,
                "{source:?}"
            );
        }

        let (_, empty) = parse_direct_recovered("()", &canonical_operator_table());
        assert!(empty.is_empty());

        let (_, missing_close) = parse_direct_recovered("(value", &canonical_operator_table());
        assert_eq!(missing_close[0].site.role, parenthesized_close_role());

        let (_, mismatched) = parse_direct_recovered("(a]", &canonical_operator_table());
        assert_eq!(mismatched[0].site.role, parenthesized_close_role());
        assert_eq!(
            mismatched[0].unexpected,
            Arc::from([UnexpectedSyntax::Token {
                range: 2..3,
                category: UnexpectedCategory::Punctuation(
                    crate::session::PunctuationEvidence::Close(Delimiter::Bracket),
                ),
            }])
        );

        let (_, collapsed) = parse_direct_recovered("(", &canonical_operator_table());
        assert_eq!(collapsed[0].site.role, parenthesized_close_role());
        assert_eq!(collapsed[0].expectations.len(), 1);

        let (_, invalid_at_eof) = parse_direct_recovered("(@", &canonical_operator_table());
        assert_eq!(invalid_at_eof[1].site.role, parenthesized_close_role());
        assert_eq!(invalid_at_eof[1].expectations.len(), 2);
    }

    #[test]
    fn parenthesized_probe_is_sink_free_and_committed_node_preserves_lossless_invariants() {
        let source = "(a+!b)*c";
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
        let calls = Rc::new(Cell::new(0));
        let mut committed = Probe::new(i).commit(CountingOutput {
            calls: Rc::clone(&calls),
        });

        assert!(committed.probe(|probe| direct_expression_nud_candidate(
            &canonical_operator_table(),
            LeadingTrivia::None,
            probe,
        )));
        assert_eq!(calls.get(), 0, "a NUD probe must not call the sink");

        let root = parse_direct(source, &canonical_operator_table());
        let tokens = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| token.text().to_string())
            .collect::<String>();
        assert_eq!(tokens, source);
        assert_eq!(root.to_string(), source);
        assert_eq!(root.kind(), SyntaxKind::Root);
    }

    #[test]
    fn if_expression_owns_arm_colons_without_colon_application_tails() {
        let root = parse_direct("if x: 1 else: 0", &canonical_operator_table());
        assert_eq!(root.to_string(), "if x: 1 else: 0");
        assert_eq!(root.descendants().filter(|node| node.kind() == SyntaxKind::IfExpression).count(), 1);
        assert_eq!(root.descendants().filter(|node| node.kind() == SyntaxKind::IfArm).count(), 1);
        assert_eq!(root.descendants().filter(|node| node.kind() == SyntaxKind::ElseArm).count(), 1);
        assert_eq!(root.descendants().filter(|node| node.kind() == SyntaxKind::ColonApplicationTail).count(), 0);
    }

    #[test]
    fn if_expression_keeps_elsif_arms_as_siblings() {
        let root = parse_direct(
            "if x: 1 elsif y: 2 elsif z: 3 else: 0",
            &canonical_operator_table(),
        );
        let if_expression = root.descendants().find(|node| node.kind() == SyntaxKind::IfExpression).unwrap();
        assert_eq!(
            if_expression.children().filter(|node| node.kind() == SyntaxKind::IfArm).count(),
            3,
        );
        assert_eq!(
            if_expression.descendants_with_tokens().filter_map(|element| element.into_token()).filter(|token| token.kind() == SyntaxKind::ElsifKw).count(),
            2,
        );
    }

    #[test]
    fn else_if_is_a_nested_if_primary_not_an_elsif_arm() {
        let root = parse_direct("if x: 1 else if y: 2", &canonical_operator_table());
        assert_eq!(root.descendants().filter(|node| node.kind() == SyntaxKind::IfExpression).count(), 2);
        assert_eq!(root.descendants().filter(|node| node.kind() == SyntaxKind::ElseArm).count(), 1);
        assert_eq!(root.descendants().filter(|node| node.kind() == SyntaxKind::ElsifKw).count(), 0);
    }

    #[test]
    fn indented_if_body_returns_dedent_else_to_its_owner() {
        let root = parse_direct("if x:\n  1\n  2\nelse: 0", &canonical_operator_table());
        let block = root.descendants().find(|node| node.kind() == SyntaxKind::IndentedStatementBlock).unwrap();
        assert_eq!(block.children().filter(|node| node.kind() == SyntaxKind::Statement).count(), 2);
        assert_eq!(root.descendants().filter(|node| node.kind() == SyntaxKind::ElseArm).count(), 1);
    }

    #[test]
    fn indented_block_companion_stop_precedes_a_same_indent_else_statement() {
        let root = parse_direct("if x:\n  1\n  else: 0", &canonical_operator_table());
        let block = root.descendants().find(|node| node.kind() == SyntaxKind::IndentedStatementBlock).unwrap();
        assert_eq!(block.children().filter(|node| node.kind() == SyntaxKind::Statement).count(), 1);
        assert_eq!(root.descendants().filter(|node| node.kind() == SyntaxKind::ElseArm).count(), 1);
    }

    #[test]
    fn if_expression_is_binding_power_invariant() {
        let source = "if x + y: a + b else: c + d";
        let low = colon_operator_table(BindingPower::scalar(1));
        let high = colon_operator_table(BindingPower::scalar(99));
        assert_eq!(parse_direct(source, &low).green(), parse_direct(source, &high).green());
        assert_eq!(parse(source, &low), parse(source, &high));
    }

    #[test]
    fn if_condition_keeps_nested_parenthesized_colon_application_local() {
        let root = parse_direct("if (f: x): 1", &canonical_operator_table());
        let condition = root.descendants().find(|node| node.kind() == SyntaxKind::Condition).unwrap();
        assert_eq!(condition.descendants().filter(|node| node.kind() == SyntaxKind::ColonApplicationTail).count(), 1);
        let arm = root.descendants().find(|node| node.kind() == SyntaxKind::IfArm).unwrap();
        assert_eq!(arm.children().filter(|node| node.kind() == SyntaxKind::ColonApplicationTail).count(), 0);
    }

    #[test]
    fn if_is_an_ordinary_parenthesized_primary() {
        let root = parse_direct("(if x: 1 else: 0)", &canonical_operator_table());
        let parenthesized = root.descendants().find(|node| node.kind() == SyntaxKind::ParenthesizedExpression).unwrap();
        assert_eq!(parenthesized.descendants().filter(|node| node.kind() == SyntaxKind::IfExpression).count(), 1);
    }

    #[test]
    fn if_recovery_preserves_committed_keywords_and_body_retry() {
        let cases = [
            ("if : 1", vec![(RecoveryKind::Missing, 3..3)]),
            ("if", vec![(RecoveryKind::Missing, 2..2)]),
            ("if x", vec![(RecoveryKind::Missing, 4..4)]),
            ("if x:", vec![(RecoveryKind::Missing, 5..5)]),
            ("if x: @ y", vec![(RecoveryKind::Error, 6..8)]),
            ("if x: 1 elsif : 2", vec![(RecoveryKind::Missing, 14..14)]),
            ("if x: 1 else", vec![(RecoveryKind::Missing, 12..12)]),
        ];
        for (source, expected) in cases {
            let (root, recoveries) = parse_direct_recovered(source, &canonical_operator_table());
            assert_eq!(root.to_string(), source, "{source:?}");
            assert_eq!(
                recoveries.iter().map(|record| (record.kind, record.site.range.clone())).collect::<Vec<_>>(),
                expected,
                "{source:?}",
            );
        }
    }

    fn canonical_operator_table() -> OperatorTable {
        OperatorTable::from_declarations([
            OperatorDeclaration::new(
                "+!",
                OperatorFixities::new()
                    .with_infix(BindingPower::scalar(50), BindingPower::new(50, [1])),
            ),
            OperatorDeclaration::new(
                "+",
                OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
            ),
            OperatorDeclaration::new(
                "!",
                OperatorFixities::new()
                    .with_prefix(BindingPower::scalar(80))
                    .with_nullfix(),
            ),
            OperatorDeclaration::new(
                "++",
                OperatorFixities::new().with_suffix(BindingPower::scalar(90)),
            ),
            OperatorDeclaration::new(
                "*",
                OperatorFixities::new()
                    .with_infix(BindingPower::scalar(60), BindingPower::scalar(60)),
            ),
        ])
        .expect("canonical operators should be valid")
    }

    fn range_operator_table() -> OperatorTable {
        OperatorTable::from_declarations([OperatorDeclaration::new(
            "..",
            OperatorFixities::new()
                .with_prefix(BindingPower::scalar(80))
                .with_suffix(BindingPower::scalar(80)),
        )])
        .expect("range operator fixture should be valid")
    }

    fn colon_operator_table(binding_power: BindingPower) -> OperatorTable {
        OperatorTable::from_declarations([OperatorDeclaration::new(
            "+",
            OperatorFixities::new().with_infix(binding_power.clone(), binding_power),
        )])
        .expect("colon table should be valid")
    }

    fn parse<'source>(source: &'source str, table: &OperatorTable) -> OperatorChain<'source> {
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

        let expression = i
            .run(from_fn(|i| parse_expression_with_operators(table, i)))
            .expect("expression should parse");
        assert_eq!(i.input.remainder(), "");
        expression
    }

    fn parse_direct(source: &str, table: &OperatorTable) -> SyntaxNode {
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
        let mut committed = Probe::new(i).commit(FullCstOutput::new(source));

        committed.start_node(SyntaxKind::Root);
        parse_direct_expression_with_operators(table, LeadingTrivia::None, &mut committed)
            .expect("expression should parse directly");
        assert_eq!(committed.probe(|probe| probe.input().input.remainder()), "");
        committed.finish_node();

        SyntaxNode::new_root(committed.into_output().finish_complete())
    }

    fn fixed_tail_after_identifier(source: &str) -> Option<FixedPostfixRecognition> {
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
        let mut i = i;
        i.run(scan_word).expect("leading identifier");
        i.run(recognize_fixed_postfix)
    }

    fn ml_after_identifier(source: &str) -> Option<TriviaRun> {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(&mut source_input, &mut expectations, IsCut::new(&mut is_cut)).set_local(&mut local);
        i.run(scan_word).expect("leading identifier");
        i.run(from_fn(|i| recognize_ml_argument(&canonical_operator_table(), i)))
    }

    fn parse_direct_recovered(
        source: &str,
        table: &OperatorTable,
    ) -> (SyntaxNode, Vec<CommittedRecoveryRecord>) {
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
        let mut committed = Probe::new(i).commit(FullCstOutput::new(source));

        committed.start_node(SyntaxKind::Root);
        parse_direct_expression_with_operators(table, LeadingTrivia::None, &mut committed)
            .expect("an accepted group remains a direct Pratt operand after recovery");
        assert_eq!(committed.probe(|probe| probe.input().input.remainder()), "");
        committed.finish_node();

        let output = committed.into_output();
        let recoveries = output.committed_recoveries().to_vec();
        (SyntaxNode::new_root(output.finish_complete()), recoveries)
    }

    struct CountingOutput {
        calls: Rc<Cell<usize>>,
    }

    impl CountingOutput {
        fn record(&self) {
            self.calls.set(self.calls.get() + 1);
        }
    }

    impl CommitOutput<'_> for CountingOutput {
        type Checkpoint = ();

        fn checkpoint(&mut self) -> Self::Checkpoint {
            self.record();
        }

        fn start_node(&mut self, _: SyntaxKind) {
            self.record();
        }

        fn start_node_at(&mut self, _: Self::Checkpoint, _: SyntaxKind) {
            self.record();
        }

        fn token(&mut self, _: SyntaxKind, _: Range<usize>) {
            self.record();
        }

        fn emit_trivia(&mut self, _: &TriviaRun) {
            self.record();
        }

        fn finish_node(&mut self) {
            self.record();
        }

        fn commit_recovery(&mut self, _: CommittedRecoveryRecord) {
            self.record();
        }

        fn emit_missing(&mut self, _: CommittedRecoveryRecord) {
            self.record();
        }

        fn emit_error(&mut self, _: CommittedRecoveryRecord) {
            self.record();
        }
    }

    fn only_child(node: &SyntaxNode, expected: SyntaxKind) -> SyntaxNode {
        let children = node.children().collect::<Vec<_>>();
        assert_eq!(
            children.len(),
            1,
            "expected exactly one child of {expected:?}"
        );
        assert_eq!(children[0].kind(), expected);
        children.into_iter().next().expect("one child")
    }

    #[test]
    fn case_and_catch_are_primary_expressions_with_family_owned_arm_shapes() {
        let case_source = "case x: 1 -> a, 2 -> b";
        let case_root = parse_direct(case_source, &canonical_operator_table());
        assert_eq!(case_root.to_string(), case_source);
        assert_eq!(case_root.descendants().filter(|node| node.kind() == SyntaxKind::CaseExpression).count(), 1);
        assert_eq!(case_root.descendants().filter(|node| node.kind() == SyntaxKind::CaseArm).count(), 2);
        assert_eq!(case_root.descendants().filter(|node| node.kind() == SyntaxKind::CaseArmSeparator).count(), 1);
        assert_eq!(case_root.descendants().filter(|node| node.kind() == SyntaxKind::ColonApplicationTail).count(), 0);

        let catch_source = "catch action { err, handler -> recover, _ -> fallback }";
        let catch_root = parse_direct(catch_source, &canonical_operator_table());
        assert_eq!(catch_root.to_string(), catch_source);
        assert_eq!(catch_root.descendants().filter(|node| node.kind() == SyntaxKind::CatchExpression).count(), 1);
        assert_eq!(catch_root.descendants().filter(|node| node.kind() == SyntaxKind::CatchBlock).count(), 1);
        assert_eq!(catch_root.descendants().filter(|node| node.kind() == SyntaxKind::CatchArm).count(), 2);
    }

    #[test]
    fn case_like_guards_and_indented_arms_keep_their_boundaries() {
        for source in [
            "case 'go 4: 0 if ok -> zero, n where ready -> n",
            "case x:\n  1 -> a\n  _ -> b",
            "catch action:\n  err -> recover\n  _ -> fallback",
        ] {
            let root = parse_direct(source, &canonical_operator_table());
            assert_eq!(root.to_string(), source, "{source:?}");
        }
        let root = parse_direct("case x: n if cond -> yes", &canonical_operator_table());
        assert_eq!(root.descendants().filter(|node| node.kind() == SyntaxKind::CaseGuard).count(), 1);
    }

    #[test]
    fn case_like_arrow_is_exact_and_never_splits_a_longer_operator() {
        let source = "case x: n ->> body";
        let root = parse_direct(source, &canonical_operator_table());
        assert_eq!(root.to_string(), source);
        assert_eq!(root.descendants_with_tokens().filter_map(|element| element.into_token()).filter(|token| token.kind() == SyntaxKind::Arrow).count(), 0);
    }

    #[test]
    fn case_and_catch_are_binding_power_invariant() {
        let source = "case x + y: n if ready + now -> yes + again, _ -> no + later";
        let low = colon_operator_table(BindingPower::scalar(1));
        let high = colon_operator_table(BindingPower::scalar(99));

        assert_eq!(parse_direct(source, &low).green(), parse_direct(source, &high).green());
        assert_eq!(parse(source, &low), parse(source, &high));
    }

    #[test]
    fn case_like_ast_and_direct_paths_agree_on_arm_count_and_layout() {
        let cases = [
            ("case x: 1 -> a, 2 -> b", 2, ColonArmLayout::Inline),
            (
                "case x:\n  1 -> a\n  _ -> b",
                2,
                ColonArmLayout::Indented {
                    base_indent: 0,
                    arm_indent: 2,
                },
            ),
        ];

        for (source, expected_arms, expected_layout) in cases {
            let chain = parse(source, &canonical_operator_table());
            let OperatorChainItem::Primary(PrimaryExpression::Case(case)) = &chain.items()[0] else {
                panic!("case source must produce a case primary");
            };
            let Recovered::Complete(block) = &case.block else {
                panic!("valid case source must complete its block");
            };
            let Recovered::Complete(arms) = &block.arms else {
                panic!("valid case source must complete its arm sequence");
            };
            assert_eq!(arms.arms.len(), expected_arms);
            assert_eq!(block.layout, expected_layout);

            let root = parse_direct(source, &canonical_operator_table());
            assert_eq!(root.to_string(), source);
            assert_eq!(root.descendants().filter(|node| node.kind() == SyntaxKind::CaseArm).count(), expected_arms);
            assert!(root.descendants().all(|node| node.kind() != SyntaxKind::Missing && node.kind() != SyntaxKind::Error));
        }

        let source = "catch action { err -> recover, _ -> fallback }";
        let chain = parse(source, &canonical_operator_table());
        let OperatorChainItem::Primary(PrimaryExpression::Catch(catch)) = &chain.items()[0] else {
            panic!("catch source must produce a catch primary");
        };
        let Recovered::Complete(CatchBlock::Braced { arms: Recovered::Complete(arms), .. }) = &catch.block else {
            panic!("valid catch source must complete a braced block");
        };
        assert_eq!(arms.arms.len(), 2);
        let root = parse_direct(source, &canonical_operator_table());
        assert_eq!(root.to_string(), source);
        assert_eq!(root.descendants().filter(|node| node.kind() == SyntaxKind::CatchArm).count(), 2);
        assert!(root.descendants().all(|node| node.kind() != SyntaxKind::Missing && node.kind() != SyntaxKind::Error));
    }

    #[test]
    fn nested_delimiters_keep_arm_boundaries_local() {
        let sources = [
            "case x: (a, b) -> (f, g), _ -> z",
            "case (f: x): (a, b) -> (g, h), _ -> z",
            "catch (action) { (err, handler) -> (recover, fallback), _ -> done }",
        ];

        for source in sources {
            let root = parse_direct(source, &canonical_operator_table());
            assert_eq!(root.to_string(), source, "{source:?}");
            assert_eq!(
                root.descendants_with_tokens()
                    .filter_map(|element| element.into_token())
                    .filter(|token| token.kind() == SyntaxKind::Arrow)
                    .count(),
                2,
                "{source:?}"
            );
        }
    }

    #[test]
    fn list_patterns_keep_case_and_catch_arm_commas_outside_brackets() {
        for source in [
            "case xs: [head, ..tail] -> head",
            "catch x: [a,b], handler -> body",
        ] {
            let root = parse_direct(source, &canonical_operator_table());
            assert_eq!(root.to_string(), source, "{source:?}");
            assert_eq!(root.descendants().filter(|node| node.kind() == SyntaxKind::ListPattern).count(), 1);
            assert!(root.descendants().all(|node| node.kind() != SyntaxKind::Missing && node.kind() != SyntaxKind::Error));
        }
    }

    #[test]
    fn missing_list_close_returns_the_case_arrow_to_its_arm_owner() {
        let source = "case xs: [a -> body";
        let (root, recoveries) = parse_direct_recovered(source, &canonical_operator_table());
        assert_eq!(root.to_string(), source);
        assert_eq!(root.descendants_with_tokens().filter_map(|element| element.into_token()).filter(|token| token.kind() == SyntaxKind::Arrow).count(), 1);
        assert!(recoveries.iter().any(|record| matches!(record.site.role, GrammarRole::ClosingDelimiter { owner: ConstructRole::ListPattern, .. })));
    }

    #[test]
    fn case_like_missing_arrow_retries_the_body_from_the_same_position() {
        let source = "case x: n yes";
        let (root, recoveries) = parse_direct_recovered(source, &canonical_operator_table());

        assert_eq!(root.to_string(), source);
        assert_eq!(
            recoveries
                .iter()
                .map(|record| (record.kind, record.site.role, record.site.range.clone()))
                .collect::<Vec<_>>(),
            vec![(RecoveryKind::Missing, GrammarRole::CaseLike(CaseLikeRole::Arrow), 10..10)],
        );
        assert!(root
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::CaseArm)
            .flat_map(|arm| arm.children())
            .any(|node| node.kind() == SyntaxKind::OperatorChain && node.to_string() == "yes"));

        let chain = parse(source, &canonical_operator_table());
        let [OperatorChainItem::Primary(PrimaryExpression::Case(case))] = chain.items() else {
            panic!("the AST path must recognize a case primary");
        };
        let Recovered::Complete(block) = &case.block else {
            panic!("the AST path must recognize the inline block");
        };
        let Recovered::Complete(arms) = &block.arms else {
            panic!("the AST path must retain its arm sequence");
        };
        let Recovered::Complete(arm) = &arms.arms[0] else {
            panic!("the AST path must retain the arm");
        };
        assert!(matches!(
            &arm.body,
            Recovered::Complete(ArmBody::Inline(body))
                if matches!(body.items(), [OperatorChainItem::Primary(PrimaryExpression::Identifier(identifier))] if identifier.text() == "yes")
        ));
    }

    #[test]
    fn case_like_recovery_marks_missing_mandatory_slots_once() {
        let cases = [
            ("case : 1 -> a", vec![(RecoveryKind::Missing, 5..5)]),
            ("case x", vec![(RecoveryKind::Missing, 6..6)]),
            ("case x: -> a", vec![(RecoveryKind::Missing, 8..8)]),
            ("catch action: err, -> recover", vec![(RecoveryKind::Missing, 19..19)]),
            ("case x: n if -> yes", vec![(RecoveryKind::Missing, 13..13)]),
            ("case x: n", vec![(RecoveryKind::Missing, 9..9)]),
            ("case x: n ->", vec![(RecoveryKind::Missing, 12..12)]),
            (
                "catch action { err -> recover",
                vec![(RecoveryKind::Missing, 29..29)],
            ),
        ];

        for (source, expected) in cases {
            let (root, recoveries) = parse_direct_recovered(source, &canonical_operator_table());
            assert_eq!(root.to_string(), source, "{source:?}");
            assert_eq!(
                recoveries
                    .iter()
                    .map(|record| (record.kind, record.site.range.clone()))
                    .collect::<Vec<_>>(),
                expected,
                "{source:?}"
            );
        }
    }

    #[test]
    fn case_like_invalid_arrow_run_recovers_to_the_next_comma_arm() {
        let source = "case x: n @, _ -> b";
        let (root, recoveries) = parse_direct_recovered(source, &canonical_operator_table());

        assert_eq!(root.to_string(), source);
        assert_eq!(
            recoveries
                .iter()
                .map(|record| (record.kind, record.site.range.clone()))
                .collect::<Vec<_>>(),
            vec![(RecoveryKind::Missing, 10..10), (RecoveryKind::Error, 10..11)],
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::CaseArm)
                .count(),
            2
        );
    }

    #[test]
    fn case_like_same_indent_boundaries_stay_with_the_outer_owner() {
        for (source, arm_missing) in [
            ("my value = case x:\nnext", false),
            ("my value = case x: n ->\nnext", true),
        ] {
            let output = crate::grammar::declaration::parse_direct_root_candidate(
                source,
                &canonical_operator_table(),
                &[],
            );
            let root = SyntaxNode::new_root(output.green().clone());
            assert_eq!(root.to_string(), source, "{source:?}");

            let owner = root
                .descendants()
                .find(|node| {
                    node.kind()
                        == if arm_missing {
                            SyntaxKind::CaseArm
                        } else {
                            SyntaxKind::CaseBlock
                        }
                })
                .expect("case-like owner");
            assert!(owner.children().any(|node| node.kind() == SyntaxKind::Missing));
            assert!(
                !owner
                    .children_with_tokens()
                    .any(|child| child.kind() == SyntaxKind::Newline),
                "the boundary newline belongs to the outer statement"
            );
        }
    }

    #[test]
    fn case_like_missing_arm_comma_retries_the_next_pattern() {
        let cases = [
            ("case x: 1 -> a 2 -> b", 15..15, SyntaxKind::CaseArm),
            ("case x:\n  1 -> a 2 -> b", 17..17, SyntaxKind::CaseArm),
            (
                "catch action:\n  err -> recover _ -> fallback",
                31..31,
                SyntaxKind::CatchArm,
            ),
            (
                "catch action { err -> recover _ -> fallback }",
                30..30,
                SyntaxKind::CatchArm,
            ),
        ];

        for (source, separator_at, arm_kind) in cases {
            let (root, recoveries) = parse_direct_recovered(source, &canonical_operator_table());
            assert_eq!(root.to_string(), source, "{source:?}");
            assert_eq!(
                recoveries
                    .iter()
                    .map(|record| (record.kind, record.site.role, record.site.range.clone()))
                    .collect::<Vec<_>>(),
                vec![(
                    RecoveryKind::Missing,
                    GrammarRole::CaseLike(CaseLikeRole::Separator),
                    separator_at,
                )],
                "{source:?}"
            );
            assert_eq!(
                root.descendants()
                    .filter(|node| node.kind() == arm_kind)
                    .count(),
                2,
                "{source:?}"
            );
        }

        for source in ["case x: 1 -> a 2 -> b", "case x:\n  1 -> a 2 -> b"] {
            let chain = parse(source, &canonical_operator_table());
            let [OperatorChainItem::Primary(PrimaryExpression::Case(case))] = chain.items() else {
                panic!("the AST path must recognize a case primary");
            };
            let Recovered::Complete(block) = &case.block else {
                panic!("the AST path must retain the block");
            };
            let Recovered::Complete(arms) = &block.arms else {
                panic!("the AST path must retain the arm sequence");
            };
            assert_eq!(arms.arms.len(), 2, "{source:?}");
        }
    }

    fn direct_token_kinds(node: &SyntaxNode) -> Vec<SyntaxKind> {
        node.children_with_tokens()
            .filter_map(|child| child.into_token())
            .map(|token| token.kind())
            .collect()
    }
}
