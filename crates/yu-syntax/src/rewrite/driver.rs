use std::{ops::Range, sync::Arc};

use chasa_recover::parser::{choice, item};
use chasa_recover::{In, ParserOnce, ParserOnceStrExt as _};
use reborrow_generic::Reborrow as _;
use unicode_ident::{is_xid_continue, is_xid_start};

use crate::{
    grammar::{
        declaration::Recovered,
        expression::{
            CallTail, FieldTail, FixedPostfixTail, OperatorChain, OperatorChainItem, OperatorRole,
            OperatorUse, PathSegment, PathTail, PrimaryExpression,
        },
    },
    scan::word::WordSpan,
    session::{
        CanonicalRecoveryContinuation, ConstructRole, Delimiter as SessionDelimiter,
        ExpectationSources, ExpectedSyntax, ExpressionRole, GrammarRole, PunctuationEvidence,
        RecoveryKind, RecoverySiteKey, SyntaxExpectation, UnexpectedCategory, UnexpectedSyntax,
    },
    syntax_kind::SyntaxKind,
};

use super::{
    item::{
        BinaryOperator, Boundary, Delimiter, Item, LayoutEvidence, Level, LogicalPosition,
        MalformedTailKind, NudKind, Payload, SourceSpan, StopKind, TailKind, Token, TokenKind,
    },
    state::{
        PilotFrame, PilotOutput, PilotRecoverState, RecoveryChainItem, RecoveryDraft,
        level_is_readable, syntax_kind_for_token,
    },
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum Either<L, R> {
    Left(L),
    Right(R),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct End<'source> {
    pub(super) item: Item<'source>,
}

pub(super) type TailExit<'source> = Result<(), Either<Item<'source>, End<'source>>>;

#[derive(Clone, Copy)]
pub(super) struct PilotContext<'source> {
    pub(super) root: &'source str,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum BorrowedArgsOwner {
    InlineReference,
    InlineApply,
}

impl BorrowedArgsOwner {
    fn node_kind(self) -> SyntaxKind {
        match self {
            Self::InlineReference => SyntaxKind::YmYulangArgs,
            Self::InlineApply => SyntaxKind::YmInlineApplyArgs,
        }
    }
}

#[derive(Clone, Debug)]
pub(super) struct BorrowedArgsResult<'source> {
    pub(super) expression: OperatorChain<'source>,
    pub(super) close_item: Item<'source>,
    pub(super) range: Range<usize>,
}

#[derive(Clone, Debug)]
pub(super) struct BorrowedArgsEnd<'source> {
    pub(super) expression: OperatorChain<'source>,
    pub(super) end: End<'source>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ExprMode {
    Normal,
    MlArgument { stop_before_tail: bool },
}

#[derive(Clone, Debug)]
struct ScannedNud<'source> {
    identity: super::item::ItemIdentity,
    leading_trivia: SourceSpan<'source>,
    token: Token<'source>,
    kind: NudKind,
}

#[derive(Clone, Copy, Debug, Default)]
struct TriviaScan {
    saw_newline: bool,
    indent: usize,
}

#[derive(Clone, Copy)]
struct ScanTriviaParser<'source> {
    context: PilotContext<'source>,
}

impl<'source, 'state> ParserOnce<&'source str, &'state mut PilotRecoverState, ()>
    for ScanTriviaParser<'source>
{
    type Output = TriviaScan;

    fn run_once(
        self,
        i: In<'_, &'source str, &'state mut PilotRecoverState, ()>,
    ) -> Option<Self::Output> {
        scan_trivia(i, self.context)
    }
}

#[derive(Clone, Copy)]
struct ScanNudParser<'source> {
    context: PilotContext<'source>,
}

impl<'source, 'state> ParserOnce<&'source str, &'state mut PilotRecoverState, ()>
    for ScanNudParser<'source>
{
    type Output = ScannedNud<'source>;

    fn run_once(
        self,
        i: In<'_, &'source str, &'state mut PilotRecoverState, ()>,
    ) -> Option<Self::Output> {
        scan_nud(i, self.context)
    }
}

#[derive(Clone, Copy)]
struct TailItemParser<'source> {
    context: PilotContext<'source>,
    frame: PilotFrame,
}

#[derive(Clone, Copy)]
enum DirectWordKind {
    Ordinary,
    PathSegment,
}

#[derive(Clone, Copy)]
struct DirectWordParser<'source> {
    context: PilotContext<'source>,
    kind: DirectWordKind,
}

impl<'source, 'state> ParserOnce<&'source str, &'state mut PilotRecoverState, ()>
    for DirectWordParser<'source>
{
    type Output = WordSpan<'source>;

    fn run_once(
        self,
        i: In<'_, &'source str, &'state mut PilotRecoverState, ()>,
    ) -> Option<Self::Output> {
        scan_direct_word(i, self.context, self.kind)
    }
}

#[derive(Clone, Copy)]
struct FixedInvalidRunParser<'source> {
    context: PilotContext<'source>,
    frame: PilotFrame,
}

impl<'source, 'state> ParserOnce<&'source str, &'state mut PilotRecoverState, ()>
    for FixedInvalidRunParser<'source>
{
    type Output = Range<usize>;

    fn run_once(
        self,
        i: In<'_, &'source str, &'state mut PilotRecoverState, ()>,
    ) -> Option<Self::Output> {
        consume_fixed_invalid_run(i, self.context, self.frame)
    }
}

impl<'source, 'state> ParserOnce<&'source str, &'state mut PilotRecoverState, ()>
    for TailItemParser<'source>
{
    type Output = Item<'source>;

    fn run_once(
        self,
        i: In<'_, &'source str, &'state mut PilotRecoverState, ()>,
    ) -> Option<Self::Output> {
        tail_item(i, self.context, self.frame)
    }
}

/// Isolated direct expression entry. It begins Rowan and the existing AST
/// product only after a NUD has matched, so entry `None` is effect-free.
pub(super) fn expr<'source>(
    i: In<'_, &'source str, &mut PilotRecoverState, &mut PilotOutput<'source>>,
    context: PilotContext<'source>,
    level: Level,
    frame: PilotFrame,
) -> Option<TailExit<'source>> {
    i.then(ScanNudParser { context }, move |nud, mut i| {
        i.state.start_node(SyntaxKind::Root);
        emit_trivia(i.state, &nud.leading_trivia);
        let mut nud = nud;
        nud.leading_trivia = SourceSpan::empty_at(context.root, nud.token.lexeme.range.start);
        i.state.start_node(SyntaxKind::OperatorChain);
        i.state.begin_chain(nud.token.lexeme.range.start);
        let exit = expr_from_scanned_nud(i.rb(), context, level, ExprMode::Normal, frame, nud);
        let chain = i.state.finish_chain();
        i.state.finish_node();
        i.state.set_root_chain(chain);
        exit
    })
}

pub(super) fn expr_body<'source>(
    i: In<'_, &'source str, &mut PilotRecoverState, &mut PilotOutput<'source>>,
    context: PilotContext<'source>,
    level: Level,
    mode: ExprMode,
    frame: PilotFrame,
) -> Option<TailExit<'source>> {
    i.then(ScanNudParser { context }, move |nud, i| {
        expr_from_scanned_nud(i, context, level, mode, frame, nud)
    })
}

pub(super) fn expr_chain<'source>(
    i: In<'_, &'source str, &mut PilotRecoverState, &mut PilotOutput<'source>>,
    context: PilotContext<'source>,
    level: Level,
    mode: ExprMode,
    frame: PilotFrame,
) -> Option<(TailExit<'source>, OperatorChain<'source>)> {
    i.then(ScanNudParser { context }, move |mut nud, i| {
        emit_trivia(i.state, &nud.leading_trivia);
        nud.leading_trivia = SourceSpan::empty_at(context.root, nud.token.lexeme.range.start);
        nested_expr_from_scanned(i, context, level, mode, frame, nud)
    })
}

/// Isolated E3 adapter for a caller that has already accepted an argument
/// opener and whose present closing parenthesis remains caller-owned.
pub(super) fn present_borrowed_args<'source>(
    mut i: In<'_, &'source str, &mut PilotRecoverState, &mut PilotOutput<'source>>,
    context: PilotContext<'source>,
    owner: BorrowedArgsOwner,
    open: Range<usize>,
    outer_frame: PilotFrame,
) -> Result<BorrowedArgsResult<'source>, BorrowedArgsEnd<'source>> {
    assert_eq!(
        byte_offset(context.root, i.index()),
        open.end,
        "the borrowed-args adapter starts immediately after its owned opener"
    );
    assert_eq!(&context.root[open.clone()], "(");
    i.state.start_node(owner.node_kind());
    i.state.token_range(SyntaxKind::LParen, open.clone());
    let inner_frame = PilotFrame {
        delimiter: Some(Delimiter::Parenthesis),
        ..outer_frame
    };
    let (exit, expression) =
        expr_chain(i.rb(), context, Level::OUTER, ExprMode::Normal, inner_frame)
            .expect("the present-close E3 witness has one expression");
    let Err(Either::Right(end)) = exit else {
        panic!("the present-close E3 witness must return its caller-owned close")
    };
    assert!(matches!(
        end.item.payload,
        Payload::Boundary(Boundary::Close(Delimiter::Parenthesis))
    ));
    if end.item.leading_trivia.text.is_empty() {
        i.state.finish_node();
        return Err(BorrowedArgsEnd { expression, end });
    }
    let close_item = borrow_close_for_owner(end.item, inner_frame);
    assert_eq!(
        byte_offset(context.root, i.index()),
        close_item.extent.end,
        "the adapter must claim the same close item returned by its child"
    );
    let close = emit_borrowed_close(i.state, &close_item);
    i.state.finish_node();
    Ok(BorrowedArgsResult {
        expression,
        close_item,
        range: open.start..close.end,
    })
}

fn nested_expr_from_scanned<'source>(
    mut i: In<'_, &'source str, &mut PilotRecoverState, &mut PilotOutput<'source>>,
    context: PilotContext<'source>,
    level: Level,
    mode: ExprMode,
    frame: PilotFrame,
    nud: ScannedNud<'source>,
) -> (TailExit<'source>, OperatorChain<'source>) {
    i.state.start_node(SyntaxKind::OperatorChain);
    i.state.begin_chain(nud.token.lexeme.range.start);
    let exit = expr_from_scanned_nud(i.rb(), context, level, mode, frame, nud);
    let chain = i.state.finish_chain();
    i.state.finish_node();
    (exit, chain)
}

fn expr_from_scanned_nud<'source>(
    mut i: In<'_, &'source str, &mut PilotRecoverState, &mut PilotOutput<'source>>,
    context: PilotContext<'source>,
    level: Level,
    mode: ExprMode,
    frame: PilotFrame,
    nud: ScannedNud<'source>,
) -> TailExit<'source> {
    match nud.kind {
        NudKind::Atom => {
            emit_core(i.state, context, &nud);
            scan_tail_after_accept(i, context, level, mode, frame)
        }
        NudKind::Prefix => prefix_after_accept(i, context, level, mode, frame, nud),
        NudKind::OpenParenthesis => {
            emit_group_open(i.state, &nud);
            let inner_frame = PilotFrame {
                delimiter: Some(Delimiter::Parenthesis),
                ..frame
            };
            let (elements, close, exit) = parse_group_contents(i.rb(), context, inner_frame);
            let end = close
                .as_ref()
                .map_or_else(|| boundary_start(&exit), |range| range.end);
            i.state.finish_node();
            i.state.push_chain_item(
                OperatorChainItem::Primary(PrimaryExpression::parenthesized(
                    elements,
                    nud.token.lexeme.range.start..end,
                )),
                nud.token.lexeme.range.start..end,
            );
            match exit {
                Ok(()) => scan_tail_after_accept(i, context, level, mode, frame),
                handoff => handoff,
            }
        }
    }
}

fn prefix_after_accept<'source>(
    mut i: In<'_, &'source str, &mut PilotRecoverState, &mut PilotOutput<'source>>,
    context: PilotContext<'source>,
    outer_level: Level,
    mode: ExprMode,
    frame: PilotFrame,
    prefix: ScannedNud<'source>,
) -> TailExit<'source> {
    emit_prefix(i.state, context, &prefix);
    let rhs = match expr_body(i.rb(), context, Level::PREFIX, mode, frame) {
        Some(rhs) => rhs,
        None => recover_required_operand(
            i.rb(),
            context,
            Level::PREFIX,
            mode,
            frame,
            GrammarRole::Expression(ExpressionRole::Nud),
        ),
    };
    continue_after_child(i, context, outer_level, mode, frame, rhs)
}

fn scan_tail_after_accept<'source>(
    i: In<'_, &'source str, &mut PilotRecoverState, &mut PilotOutput<'source>>,
    context: PilotContext<'source>,
    level: Level,
    mode: ExprMode,
    frame: PilotFrame,
) -> TailExit<'source> {
    if matches!(
        mode,
        ExprMode::MlArgument {
            stop_before_tail: true
        }
    ) && !adjacent_fixed_tail_starts(context.root, i.index())
    {
        return Ok(());
    }
    i.then(TailItemParser { context, frame }, move |item, i| {
        tail(i, context, level, mode, frame, item)
    })
    .expect("accepted tail-item completion is total")
}

fn adjacent_fixed_tail_starts(root: &str, index: *const u8) -> bool {
    let remainder = &root[byte_offset(root, index)..];
    if remainder.starts_with("::") || remainder.starts_with('(') {
        return true;
    }
    let Some(after_dot) = remainder.strip_prefix('.') else {
        return false;
    };
    !matches!(after_dot.chars().next(), Some('(' | '{' | '.'))
}

pub(super) fn tail<'source>(
    mut i: In<'_, &'source str, &mut PilotRecoverState, &mut PilotOutput<'source>>,
    context: PilotContext<'source>,
    level: Level,
    mode: ExprMode,
    frame: PilotFrame,
    item: Item<'source>,
) -> TailExit<'source> {
    let Some(kind) = item.tail_kind() else {
        return Err(Either::Right(End { item }));
    };
    if !tail_reads(level, kind) {
        return Err(Either::Left(item));
    }

    match kind {
        TailKind::Binary(operator) => {
            emit_binary(i.state, context, &item, operator);
            let rhs_level = operator.right_level();
            let rhs = match expr_body(i.rb(), context, rhs_level, mode, frame) {
                Some(rhs) => rhs,
                None => recover_required_operand(
                    i.rb(),
                    context,
                    rhs_level,
                    mode,
                    frame,
                    GrammarRole::Expression(ExpressionRole::Nud),
                ),
            };
            continue_after_child(i, context, level, mode, frame, rhs)
        }
        TailKind::MlNud(nud_kind) => {
            let (child, argument) =
                ml_child_after_accept(i.rb(), context, level, frame, &item, nud_kind);
            let range = argument.range();
            i.state.push_chain_item(
                OperatorChainItem::MlArgument {
                    argument: Box::new(argument),
                    range: range.clone(),
                },
                range,
            );
            continue_after_child(i, context, level, mode, frame, child)
        }
        TailKind::CallOpen => parse_call_after_open(i, context, level, mode, frame, item),
        TailKind::Field => field_after_accept(i, context, level, mode, frame, item),
        TailKind::Path => path_after_accept(i, context, level, mode, frame, item),
        TailKind::Deferred => unreachable!("a deferred fixed-tail item is never accepted"),
        TailKind::Malformed(kind) => {
            let role = match kind {
                MalformedTailKind::Adjacent => GrammarRole::Expression(ExpressionRole::Nud),
                MalformedTailKind::Spaced => GrammarRole::Expression(ExpressionRole::MlArgument),
            };
            if kind == MalformedTailKind::Spaced {
                emit_trivia(i.state, &item.leading_trivia);
                i.state.start_node(SyntaxKind::MlArgument);
                i.state.start_node(SyntaxKind::OperatorChain);
                let range = token_range(&item);
                i.state.begin_chain(range.start);
                recover_invalid_item_without_trivia(i.rb(), role, &item);
                let argument = i.state.finish_chain();
                i.state.finish_node();
                i.state.finish_node();
                let range = argument.range();
                i.state.push_chain_item(
                    OperatorChainItem::MlArgument {
                        argument: Box::new(argument),
                        range: range.clone(),
                    },
                    range,
                );
            } else {
                recover_invalid_item(i.rb(), role, &item);
            }
            scan_tail_after_accept(i, context, level, mode, frame)
        }
    }
}

pub(super) fn ml_child_after_accept<'source>(
    mut i: In<'_, &'source str, &mut PilotRecoverState, &mut PilotOutput<'source>>,
    context: PilotContext<'source>,
    level: Level,
    frame: PilotFrame,
    item: &Item<'source>,
    nud_kind: NudKind,
) -> (TailExit<'source>, OperatorChain<'source>) {
    let mut nud = nud_from_item(item, nud_kind);
    emit_trivia(i.state, &item.leading_trivia);
    nud.leading_trivia = SourceSpan::empty_at(context.root, nud.token.lexeme.range.start);
    i.state.start_node(SyntaxKind::MlArgument);
    let ml_mode = ExprMode::MlArgument {
        stop_before_tail: !item.leading_trivia.text.is_empty(),
    };
    let child = nested_expr_from_scanned(i.rb(), context, level, ml_mode, frame, nud);
    i.state.finish_node();
    child
}

fn field_after_accept<'source>(
    mut i: In<'_, &'source str, &mut PilotRecoverState, &mut PilotOutput<'source>>,
    context: PilotContext<'source>,
    level: Level,
    mode: ExprMode,
    frame: PilotFrame,
    item: Item<'source>,
) -> TailExit<'source> {
    let dot = token_range(&item);
    emit_trivia(i.state, &item.leading_trivia);
    i.state.start_node(SyntaxKind::FieldTail);
    i.state.token_range(SyntaxKind::Dot, dot.clone());
    let name = i
        .rb()
        .then(
            DirectWordParser {
                context,
                kind: DirectWordKind::Ordinary,
            },
            |word, i| {
                i.state.token_range(SyntaxKind::Identifier, word.range());
                word
            },
        )
        .map(Recovered::Complete)
        .unwrap_or_else(|| {
            recover_fixed_tail_slot(i.rb(), context, frame, ExpressionRole::FieldName);
            Recovered::Incomplete
        });
    let end = byte_offset(context.root, i.index());
    i.state.finish_node();
    let range = dot.start..end;
    i.state.push_chain_item(
        OperatorChainItem::FixedPostfix(FixedPostfixTail::Field(FieldTail::new(
            dot,
            name,
            range.clone(),
        ))),
        range,
    );
    scan_tail_after_accept(i, context, level, mode, frame)
}

fn path_after_accept<'source>(
    mut i: In<'_, &'source str, &mut PilotRecoverState, &mut PilotOutput<'source>>,
    context: PilotContext<'source>,
    level: Level,
    mode: ExprMode,
    frame: PilotFrame,
    item: Item<'source>,
) -> TailExit<'source> {
    let separator = token_range(&item);
    emit_trivia(i.state, &item.leading_trivia);
    i.state.start_node(SyntaxKind::PathTail);
    i.state
        .token_range(SyntaxKind::ColonColon, separator.clone());

    let trivia_start = byte_offset(context.root, i.index());
    let trivia_end = i
        .rb()
        .then(ScanTriviaParser { context }, |_, i| {
            byte_offset(context.root, i.index())
        })
        .expect("path trivia scanning is total");
    if trivia_start < trivia_end {
        emit_trivia(
            i.state,
            &SourceSpan::checked(context.root, &context.root[trivia_start..trivia_end]),
        );
    }

    let segment = i
        .rb()
        .then(
            DirectWordParser {
                context,
                kind: DirectWordKind::PathSegment,
            },
            |word, i| {
                let segment = PathSegment::from_word(word);
                let kind = match segment {
                    PathSegment::Identifier(_) => SyntaxKind::Identifier,
                    PathSegment::SigilIdentifier(_) => SyntaxKind::SigilIdentifier,
                };
                i.state.token_range(kind, word.range());
                segment
            },
        )
        .map(Recovered::Complete)
        .unwrap_or_else(|| {
            recover_fixed_tail_slot(i.rb(), context, frame, ExpressionRole::PathSegment);
            Recovered::Incomplete
        });
    let end = byte_offset(context.root, i.index());
    i.state.finish_node();
    let range = separator.start..end;
    i.state.push_chain_item(
        OperatorChainItem::FixedPostfix(FixedPostfixTail::Path(PathTail::new(
            separator,
            segment,
            range.clone(),
        ))),
        range,
    );
    scan_tail_after_accept(i, context, level, mode, frame)
}

fn recover_fixed_tail_slot<'source>(
    mut i: In<'_, &'source str, &mut PilotRecoverState, &mut PilotOutput<'source>>,
    context: PilotContext<'source>,
    frame: PilotFrame,
    role: ExpressionRole,
) {
    let invalid = i
        .rb()
        .then(FixedInvalidRunParser { context, frame }, |range, _| range);
    let (range, kind, continuation) = match invalid {
        Some(range) => (
            range,
            RecoveryKind::Error,
            CanonicalRecoveryContinuation::RetrySameSlot,
        ),
        None => {
            let at = byte_offset(context.root, i.index());
            (
                at..at,
                RecoveryKind::Missing,
                CanonicalRecoveryContinuation::StopAtBoundary,
            )
        }
    };
    publish_recovery(
        i,
        GrammarRole::Expression(role),
        ExpectedSyntax::Identifier,
        range,
        kind,
        continuation,
        RecoveryChainItem::None,
    );
}

fn parse_call_after_open<'source>(
    mut i: In<'_, &'source str, &mut PilotRecoverState, &mut PilotOutput<'source>>,
    context: PilotContext<'source>,
    level: Level,
    mode: ExprMode,
    frame: PilotFrame,
    open_item: Item<'source>,
) -> TailExit<'source> {
    let open = token_range(&open_item);
    emit_call_open(i.state, &open_item);
    let inner_frame = PilotFrame {
        delimiter: Some(Delimiter::Parenthesis),
        ..frame
    };
    let first = complete_tail_item(i.rb(), context, inner_frame);
    let mut arguments = Vec::new();
    let (close, exit) = match first.payload {
        Payload::Boundary(Boundary::Close(Delimiter::Parenthesis)) => {
            let close = emit_owned_close(i.state, first);
            (Recovered::Complete(close.clone()), Ok(()))
        }
        Payload::Boundary(_) => {
            let at = first.extent.start;
            recover_missing_close(i.rb(), ConstructRole::ArgumentList, at);
            (
                Recovered::Incomplete,
                Err(Either::Right(End { item: first })),
            )
        }
        Payload::Tail {
            kind: TailKind::MlNud(nud_kind),
            ..
        } => {
            let mut nud = nud_from_item(&first, nud_kind);
            emit_trivia(i.state, &first.leading_trivia);
            nud.leading_trivia = SourceSpan::empty_at(context.root, nud.token.lexeme.range.start);
            let (child, argument) = nested_expr_from_scanned(
                i.rb(),
                context,
                Level::OUTER,
                ExprMode::Normal,
                inner_frame,
                nud,
            );
            arguments.push(argument);
            finish_call_child(i.rb(), context, ConstructRole::ArgumentList, child)
        }
        _ => {
            emit_trivia(i.state, &first.leading_trivia);
            i.state.start_node(SyntaxKind::OperatorChain);
            i.state.begin_chain(first.extent.start);
            recover_invalid_item_without_trivia(
                i.rb(),
                GrammarRole::Expression(ExpressionRole::CallArgument),
                &first,
            );
            let argument = i.state.finish_chain();
            i.state.finish_node();
            arguments.push(argument);
            let next = complete_tail_item(i.rb(), context, inner_frame);
            finish_call_child(
                i.rb(),
                context,
                ConstructRole::ArgumentList,
                Err(Either::Right(End { item: next })),
            )
        }
    };

    let end = match &close {
        Recovered::Complete(close) => close.end,
        Recovered::Incomplete => boundary_start(&exit),
    };
    i.state.finish_node();
    let call = CallTail::new(open.clone(), arguments, close, open.start..end);
    i.state.push_chain_item(
        OperatorChainItem::FixedPostfix(FixedPostfixTail::Call(call)),
        open.start..end,
    );
    match exit {
        Ok(()) => scan_tail_after_accept(i, context, level, mode, frame),
        handoff => handoff,
    }
}

fn finish_call_child<'source>(
    mut i: In<'_, &'source str, &mut PilotRecoverState, &mut PilotOutput<'source>>,
    context: PilotContext<'source>,
    owner: ConstructRole,
    child: TailExit<'source>,
) -> (Recovered<std::ops::Range<usize>>, TailExit<'source>) {
    match child {
        Err(Either::Right(end))
            if matches!(
                end.item.payload,
                Payload::Boundary(Boundary::Close(Delimiter::Parenthesis))
            ) =>
        {
            let close = emit_owned_close(i.state, end.item);
            (Recovered::Complete(close), Ok(()))
        }
        Err(Either::Left(item)) => {
            recover_missing_close(i.rb(), owner, item.extent.start);
            (Recovered::Incomplete, Err(Either::Left(item)))
        }
        Err(Either::Right(end)) => {
            recover_missing_close(i.rb(), owner, end.item.extent.start);
            (Recovered::Incomplete, Err(Either::Right(end)))
        }
        Ok(()) => {
            let at = byte_offset(context.root, i.index());
            recover_missing_close(i, owner, at);
            (Recovered::Incomplete, Ok(()))
        }
    }
}

fn parse_group_contents<'source>(
    mut i: In<'_, &'source str, &mut PilotRecoverState, &mut PilotOutput<'source>>,
    context: PilotContext<'source>,
    frame: PilotFrame,
) -> (
    Vec<OperatorChain<'source>>,
    Option<std::ops::Range<usize>>,
    TailExit<'source>,
) {
    if let Some((child, element)) =
        expr_chain(i.rb(), context, Level::OUTER, ExprMode::Normal, frame)
    {
        let (close, exit) = finish_group_child(i, context, child);
        return (vec![element], close, exit);
    }

    let first = complete_tail_item(i.rb(), context, frame);
    if matches!(
        first.payload,
        Payload::Boundary(Boundary::Close(Delimiter::Parenthesis))
    ) {
        let close = emit_owned_close(i.state, first);
        return (Vec::new(), Some(close), Ok(()));
    }

    if matches!(first.payload, Payload::Boundary(_)) {
        recover_missing_close(i.rb(), ConstructRole::ExpressionGroup, first.extent.start);
        return (Vec::new(), None, Err(Either::Right(End { item: first })));
    }

    emit_trivia(i.state, &first.leading_trivia);
    i.state.start_node(SyntaxKind::OperatorChain);
    i.state.begin_chain(first.extent.start);
    recover_invalid_item_without_trivia(
        i.rb(),
        GrammarRole::Expression(ExpressionRole::Nud),
        &first,
    );
    let element = i.state.finish_chain();
    i.state.finish_node();
    let next = complete_tail_item(i.rb(), context, frame);
    let (close, exit) = finish_group_child(i, context, Err(Either::Right(End { item: next })));
    (vec![element], close, exit)
}

fn finish_group_child<'source>(
    mut i: In<'_, &'source str, &mut PilotRecoverState, &mut PilotOutput<'source>>,
    context: PilotContext<'source>,
    child: TailExit<'source>,
) -> (Option<std::ops::Range<usize>>, TailExit<'source>) {
    match child {
        Err(Either::Right(end))
            if matches!(
                end.item.payload,
                Payload::Boundary(Boundary::Close(Delimiter::Parenthesis))
            ) =>
        {
            let close = emit_owned_close(i.state, end.item);
            (Some(close), Ok(()))
        }
        Err(Either::Left(item)) => {
            recover_missing_close(i.rb(), ConstructRole::ExpressionGroup, item.extent.start);
            (None, Err(Either::Left(item)))
        }
        Err(Either::Right(end)) => {
            recover_missing_close(
                i.rb(),
                ConstructRole::ExpressionGroup,
                end.item.extent.start,
            );
            (None, Err(Either::Right(end)))
        }
        Ok(()) => {
            let at = byte_offset(context.root, i.index());
            recover_missing_close(i, ConstructRole::ExpressionGroup, at);
            (None, Ok(()))
        }
    }
}

fn recover_required_operand<'source>(
    mut i: In<'_, &'source str, &mut PilotRecoverState, &mut PilotOutput<'source>>,
    context: PilotContext<'source>,
    level: Level,
    mode: ExprMode,
    frame: PilotFrame,
    role: GrammarRole,
) -> TailExit<'source> {
    let item = complete_tail_item(i.rb(), context, frame);
    match item.payload {
        Payload::Boundary(_) => {
            recover_missing(i.rb(), role, item.extent.start, ExpectedSyntax::Expression);
            Err(Either::Right(End { item }))
        }
        _ => {
            recover_invalid_item(i.rb(), role, &item);
            scan_tail_after_accept(i, context, level, mode, frame)
        }
    }
}

fn continue_after_child<'source>(
    i: In<'_, &'source str, &mut PilotRecoverState, &mut PilotOutput<'source>>,
    context: PilotContext<'source>,
    level: Level,
    mode: ExprMode,
    frame: PilotFrame,
    child: TailExit<'source>,
) -> TailExit<'source> {
    match child {
        Ok(()) => scan_tail_after_accept(i, context, level, mode, frame),
        Err(Either::Left(item)) => tail(i, context, level, mode, frame, item),
        Err(Either::Right(end)) => Err(Either::Right(end)),
    }
}

fn tail_reads(level: Level, kind: TailKind) -> bool {
    match kind {
        TailKind::Binary(operator) => level_is_readable(level, operator.left_level()),
        TailKind::CallOpen
        | TailKind::Field
        | TailKind::Path
        | TailKind::MlNud(_)
        | TailKind::Malformed(_) => true,
        TailKind::Deferred => false,
    }
}

fn scan_nud<'source>(
    mut i: In<'_, &'source str, &mut PilotRecoverState, ()>,
    context: PilotContext<'source>,
) -> Option<ScannedNud<'source>> {
    let start = byte_offset(context.root, i.index());
    let ((trivia, (kind, character)), consumed) = i.check(
        (
            ScanTriviaParser { context },
            choice((scan_prefix_nud, scan_open_nud, scan_atom_nud)),
        )
            .with_str(),
    )?;
    let token_len = character.len_utf8();
    let trivia_len = consumed.len() - token_len;
    let _ = trivia;
    let leading_trivia = SourceSpan::checked(context.root, &consumed[..trivia_len]);
    let token_text = &consumed[trivia_len..];
    let identity = i.recovery().allocate_item_identity(start);
    i.recovery().record_scanned_item(identity);
    i.recovery().line.column += 1;
    i.recovery().line.at_line_start = false;
    Some(ScannedNud {
        identity,
        leading_trivia,
        token: Token {
            kind: match kind {
                NudKind::Atom if character.is_ascii_digit() => TokenKind::Integer,
                NudKind::Atom => TokenKind::Identifier,
                NudKind::Prefix => TokenKind::PrefixOperator,
                NudKind::OpenParenthesis => TokenKind::LeftParenthesis,
            },
            lexeme: SourceSpan::checked(context.root, token_text),
        },
        kind,
    })
}

fn scan_atom(mut i: In<'_, &str, &mut PilotRecoverState, ()>) -> Option<char> {
    i.check(choice((
        item('a'),
        item('b'),
        item('c'),
        item('f'),
        item('x'),
        item('y'),
        item('α'),
        item('あ'),
    )))
}

fn scan_prefix_nud(mut i: In<'_, &str, &mut PilotRecoverState, ()>) -> Option<(NudKind, char)> {
    i.check(item('-'))
        .map(|character| (NudKind::Prefix, character))
}

fn scan_open_nud(mut i: In<'_, &str, &mut PilotRecoverState, ()>) -> Option<(NudKind, char)> {
    i.check(item('('))
        .map(|character| (NudKind::OpenParenthesis, character))
}

fn scan_atom_nud(mut i: In<'_, &str, &mut PilotRecoverState, ()>) -> Option<(NudKind, char)> {
    i.check(scan_atom)
        .map(|character| (NudKind::Atom, character))
}

fn scan_direct_word<'source>(
    mut i: In<'_, &'source str, &mut PilotRecoverState, ()>,
    context: PilotContext<'source>,
    kind: DirectWordKind,
) -> Option<WordSpan<'source>> {
    let start = byte_offset(context.root, i.index());
    let remainder = &context.root[start..];
    let length = match kind {
        DirectWordKind::Ordinary => ordinary_word_length(remainder)?,
        DirectWordKind::PathSegment => {
            let Some(first) = remainder.chars().next() else {
                return None;
            };
            if matches!(first, '$' | '&' | '\'') {
                first.len_utf8() + ordinary_word_length(&remainder[first.len_utf8()..])?
            } else {
                ordinary_word_length(remainder)?
            }
        }
    };
    let end = start + length;
    let text = &context.root[start..end];
    for expected in text.chars() {
        assert_eq!(i.next(), Some(expected));
    }
    let line = i.recovery();
    line.line.column += text.chars().count();
    line.line.at_line_start = false;
    Some(WordSpan::from_root_range(context.root, start..end))
}

fn ordinary_word_length(source: &str) -> Option<usize> {
    let mut characters = source.char_indices();
    let (_, first) = characters.next()?;
    if first != '_' && !is_xid_start(first) {
        return None;
    }
    let mut end = first.len_utf8();
    for (offset, character) in characters {
        if is_xid_continue(character) {
            end = offset + character.len_utf8();
            continue;
        }
        if matches!(character, '?' | '!') {
            end = offset + character.len_utf8();
        }
        break;
    }
    Some(end)
}

fn consume_fixed_invalid_run<'source>(
    mut i: In<'_, &'source str, &mut PilotRecoverState, ()>,
    context: PilotContext<'source>,
    frame: PilotFrame,
) -> Option<Range<usize>> {
    let start = byte_offset(context.root, i.index());
    let remainder = &context.root[start..];
    let first = remainder.chars().next()?;
    if fixed_invalid_boundary(first, frame) || fixed_retry_head(first) && !first.is_numeric() {
        return None;
    }

    let mut end = first.len_utf8();
    if first.is_numeric() {
        for (offset, character) in remainder.char_indices().skip(1) {
            if !character.is_numeric() {
                break;
            }
            end = offset + character.len_utf8();
        }
    } else {
        for (offset, character) in remainder.char_indices().skip(1) {
            if fixed_invalid_boundary(character, frame) || fixed_retry_head(character) {
                break;
            }
            end = offset + character.len_utf8();
        }
    }

    let range = start..start + end;
    let text = &context.root[range.clone()];
    for expected in text.chars() {
        assert_eq!(i.next(), Some(expected));
    }
    let line = i.recovery();
    line.line.column += text.chars().count();
    line.line.at_line_start = false;
    Some(range)
}

fn fixed_invalid_boundary(character: char, frame: PilotFrame) -> bool {
    character.is_whitespace()
        || matches!(character, ')' | ']' | '}' | '.' | ':')
        || character == ',' && frame.stop == Some(StopKind::Comma)
        || character == ';' && frame.stop == Some(StopKind::Semicolon)
}

fn fixed_retry_head(character: char) -> bool {
    matches!(character, '+' | '*' | '(' | '-')
        || character == '_'
        || is_xid_start(character)
        || character.is_numeric()
}

pub(super) fn tail_item<'source>(
    mut i: In<'_, &'source str, &mut PilotRecoverState, ()>,
    context: PilotContext<'source>,
    frame: PilotFrame,
) -> Option<Item<'source>> {
    let item_start = byte_offset(context.root, i.index());
    let trivia = scan_trivia(i.rb(), context).expect("trivia scanning is total");
    let payload_start = byte_offset(context.root, i.index());
    let leading_trivia =
        SourceSpan::checked(context.root, &context.root[item_start..payload_start]);
    let identity = i.recovery().allocate_item_identity(item_start);
    let logical_position = LogicalPosition {
        line: i.recovery().line.line_number,
        column: i.recovery().line.column,
    };

    if trivia.saw_newline
        && (!frame.allow_same_level_newline || trivia.indent < frame.layout_baseline)
    {
        i.recovery().record_scanned_item(identity);
        return Some(Item {
            identity,
            leading_trivia,
            payload: Payload::Boundary(Boundary::Dedent(LayoutEvidence {
                baseline: frame.layout_baseline,
                observed_indent: trivia.indent,
            })),
            lexical_boundary_token: None,
            extent: item_start..payload_start,
            logical_position,
        });
    }

    let item = complete_item_payload(
        i.rb(),
        context,
        frame,
        Item {
            identity,
            leading_trivia,
            payload: Payload::Boundary(Boundary::EofAfterTrivia),
            lexical_boundary_token: None,
            extent: item_start..payload_start,
            logical_position,
        },
    );
    i.recovery().record_scanned_item(identity);
    Some(item)
}

fn complete_tail_item<'source>(
    i: In<'_, &'source str, &mut PilotRecoverState, &mut PilotOutput<'source>>,
    context: PilotContext<'source>,
    frame: PilotFrame,
) -> Item<'source> {
    i.then(TailItemParser { context, frame }, |item, _| item)
        .expect("accepted item completion is total")
}

fn complete_item_payload<'source>(
    mut i: In<'_, &'source str, &mut PilotRecoverState, ()>,
    context: PilotContext<'source>,
    frame: PilotFrame,
    mut pending: Item<'source>,
) -> Item<'source> {
    let Some(character) = i.next() else {
        return pending;
    };
    let payload_start = pending.leading_trivia.range.end;
    let mut payload_end = byte_offset(context.root, i.index());
    if character == ':' && context.root[payload_end..].starts_with(':') {
        let second = i.next().expect("the inspected second colon exists");
        assert_eq!(second, ':');
        payload_end = byte_offset(context.root, i.index());
    }
    i.recovery().line.column += 1;
    if character == ':' && payload_end - payload_start == 2 {
        i.recovery().line.column += 1;
    }
    i.recovery().line.at_line_start = false;
    let token = Token {
        kind: if character == ':' && payload_end - payload_start == 2 {
            TokenKind::ColonColon
        } else {
            token_kind(character)
        },
        lexeme: SourceSpan::checked(context.root, &context.root[payload_start..payload_end]),
    };
    let spaced = !pending.leading_trivia.text.is_empty();
    pending.extent.end = payload_end;
    let next_character = context.root[payload_end..].chars().next();
    let (payload, lexical_boundary_token) =
        classify_payload(frame, character, next_character, token, spaced);
    pending.payload = payload;
    pending.lexical_boundary_token = lexical_boundary_token;
    pending
}

/// The layout owner may release a trivia-caused boundary and complete that
/// same item under a new frame. Identity/trivia/position are not rebuilt.
pub(super) fn resume_trivia_boundary<'source>(
    i: In<'_, &'source str, &mut PilotRecoverState, ()>,
    context: PilotContext<'source>,
    frame: PilotFrame,
    mut item: Item<'source>,
) -> Item<'source> {
    let Payload::Boundary(Boundary::Dedent(evidence)) = item.payload else {
        panic!("only a retained dedent item can be resumed");
    };
    assert_eq!(
        byte_offset(context.root, i.index()),
        item.leading_trivia.range.end,
        "a retained boundary can only resume at its payload cursor"
    );
    if !frame.allow_same_level_newline || evidence.observed_indent < frame.layout_baseline {
        return item;
    }
    if item.leading_trivia.range.end == context.root.len() {
        item.payload = Payload::Boundary(Boundary::EofAfterTrivia);
        return item;
    }
    complete_item_payload(i, context, frame, item)
}

fn classify_payload<'source>(
    frame: PilotFrame,
    character: char,
    next_character: Option<char>,
    token: Token<'source>,
    spaced: bool,
) -> (Payload<'source>, Option<Token<'source>>) {
    let lexical = |boundary| (Payload::Boundary(boundary), Some(token.clone()));
    match character {
        ')' => lexical(Boundary::Close(Delimiter::Parenthesis)),
        ']' => lexical(Boundary::Close(Delimiter::Bracket)),
        '}' => lexical(Boundary::Close(Delimiter::Brace)),
        ',' if frame.stop == Some(StopKind::Comma) => lexical(Boundary::Stop(StopKind::Comma)),
        ';' if frame.stop == Some(StopKind::Semicolon) => {
            lexical(Boundary::Stop(StopKind::Semicolon))
        }
        ':' if token.lexeme.text == "::" => tail_payload(TailKind::Path, token),
        ':' if frame.stop == Some(StopKind::Colon) => lexical(Boundary::Stop(StopKind::Colon)),
        '.' if matches!(next_character, Some('(' | '{' | '.')) => {
            tail_payload(TailKind::Deferred, token)
        }
        '.' => tail_payload(TailKind::Field, token),
        '+' => tail_payload(TailKind::Binary(BinaryOperator::Add), token),
        '*' => tail_payload(TailKind::Binary(BinaryOperator::Multiply), token),
        '(' if !spaced => tail_payload(TailKind::CallOpen, token),
        '(' => tail_payload(TailKind::MlNud(NudKind::OpenParenthesis), token),
        '-' => tail_payload(TailKind::MlNud(NudKind::Prefix), token),
        character if character.is_alphanumeric() => {
            tail_payload(TailKind::MlNud(NudKind::Atom), token)
        }
        _ => tail_payload(
            TailKind::Malformed(if spaced {
                MalformedTailKind::Spaced
            } else {
                MalformedTailKind::Adjacent
            }),
            token,
        ),
    }
}

fn tail_payload<'source>(
    kind: TailKind,
    token: Token<'source>,
) -> (Payload<'source>, Option<Token<'source>>) {
    (Payload::Tail { kind, token }, None)
}

pub(super) fn borrow_close_for_owner(mut item: Item<'_>, frame: PilotFrame) -> Item<'_> {
    let Payload::Boundary(Boundary::Close(delimiter)) = item.payload else {
        panic!("only a lexical close can be transferred to its caller");
    };
    assert_eq!(
        frame.delimiter,
        Some(delimiter),
        "only the active delimiter owner can transfer its close"
    );
    let token = item
        .lexical_boundary_token
        .as_ref()
        .expect("a lexical close must retain its token evidence");
    assert_eq!(
        token.lexeme.text,
        delimiter_text(delimiter),
        "close classification must match its lexical token"
    );
    item.payload = Payload::Boundary(Boundary::BorrowedClose(delimiter));
    item
}

pub(super) fn claim_stop_for_owner(
    mut item: Item<'_>,
    frame: PilotFrame,
    stop: StopKind,
) -> Item<'_> {
    assert_eq!(
        frame.stop,
        Some(stop),
        "only the active stop owner can claim a stop"
    );
    let Payload::Tail { token, .. } = item.payload else {
        panic!("only a completed token item can become an owner stop");
    };
    assert_eq!(
        token.lexeme.text,
        stop_text(stop),
        "stop classification must match its lexical token"
    );
    item.lexical_boundary_token = Some(token);
    item.payload = Payload::Boundary(Boundary::Stop(stop));
    item
}

fn delimiter_text(delimiter: Delimiter) -> &'static str {
    match delimiter {
        Delimiter::Parenthesis => ")",
        Delimiter::Bracket => "]",
        Delimiter::Brace => "}",
    }
}

fn stop_text(stop: StopKind) -> &'static str {
    match stop {
        StopKind::Comma => ",",
        StopKind::Semicolon => ";",
        StopKind::Colon => ":",
    }
}

fn scan_trivia(
    mut i: In<'_, &str, &mut PilotRecoverState, ()>,
    context: PilotContext<'_>,
) -> Option<TriviaScan> {
    let mut trivia = TriviaScan::default();
    loop {
        if i.check(item(' ')).is_some() || i.check(item('\t')).is_some() {
            let line = i.recovery();
            line.line.column += 1;
            if trivia.saw_newline {
                trivia.indent += 1;
            }
            continue;
        }
        let newline_start = byte_offset(context.root, i.index());
        if i.check((item('\r'), item('\n'))).is_some() || i.check(item('\n')).is_some() {
            let newline_end = byte_offset(context.root, i.index());
            trivia.saw_newline = true;
            trivia.indent = 0;
            let line = i.recovery();
            line.line.last_newline = Some((newline_start, newline_end));
            line.line.line_start = newline_end;
            line.line.line_indent = 0;
            line.line.line_number += 1;
            line.line.column = 0;
            line.line.at_line_start = true;
            continue;
        }
        break;
    }
    if trivia.saw_newline {
        i.recovery().line.line_indent = trivia.indent;
    } else {
        trivia.indent = i.recovery().line.column;
    }
    Some(trivia)
}

fn recover_missing<'source>(
    mut i: In<'_, &'source str, &mut PilotRecoverState, &mut PilotOutput<'source>>,
    role: GrammarRole,
    at: usize,
    expected: ExpectedSyntax,
) {
    publish_recovery(
        i.rb(),
        role,
        expected,
        at..at,
        RecoveryKind::Missing,
        CanonicalRecoveryContinuation::StopAtBoundary,
        RecoveryChainItem::MissingOperand,
    );
}

fn recover_missing_close<'source>(
    i: In<'_, &'source str, &mut PilotRecoverState, &mut PilotOutput<'source>>,
    owner: ConstructRole,
    at: usize,
) {
    let role = GrammarRole::ClosingDelimiter {
        owner,
        delimiter: SessionDelimiter::Parenthesis,
    };
    publish_recovery(
        i,
        role,
        ExpectedSyntax::Punctuation(PunctuationEvidence::Close(SessionDelimiter::Parenthesis)),
        at..at,
        RecoveryKind::Missing,
        CanonicalRecoveryContinuation::StopAtBoundary,
        RecoveryChainItem::None,
    );
}

fn recover_invalid_item<'source>(
    i: In<'_, &'source str, &mut PilotRecoverState, &mut PilotOutput<'source>>,
    role: GrammarRole,
    item: &Item<'source>,
) {
    emit_trivia(i.state, &item.leading_trivia);
    recover_invalid_item_without_trivia(i, role, item);
}

fn recover_invalid_item_without_trivia<'source>(
    i: In<'_, &'source str, &mut PilotRecoverState, &mut PilotOutput<'source>>,
    role: GrammarRole,
    item: &Item<'source>,
) {
    publish_recovery(
        i,
        role,
        ExpectedSyntax::Expression,
        token_range(item),
        RecoveryKind::Error,
        CanonicalRecoveryContinuation::RetrySameSlot,
        RecoveryChainItem::Error,
    );
}

fn publish_recovery<'source>(
    i: In<'_, &'source str, &mut PilotRecoverState, &mut PilotOutput<'source>>,
    role: GrammarRole,
    expected: ExpectedSyntax,
    range: std::ops::Range<usize>,
    kind: RecoveryKind,
    continuation: CanonicalRecoveryContinuation,
    chain_item: RecoveryChainItem,
) {
    let expectation = SyntaxExpectation {
        role,
        expected,
        range: range.clone(),
        sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
    };
    let prepared = i.then(
        move |mut grammar: In<'_, &'source str, &mut PilotRecoverState, ()>| {
            let recovery = grammar.recovery();
            recovery.record_expectation(expectation.clone());
            let id = recovery.allocate_diagnostic_id();
            Some((
                id,
                RecoveryDraft {
                    site: RecoverySiteKey {
                        role,
                        range: range.clone(),
                    },
                    kind,
                    unexpected: match kind {
                        RecoveryKind::Missing => Arc::from([]),
                        RecoveryKind::Error => Arc::from([UnexpectedSyntax::Token {
                            range: range.clone(),
                            category: UnexpectedCategory::OtherCharacter,
                        }]),
                    },
                    expectations: Arc::from([expectation]),
                    primary_expectation: 0,
                    continuation,
                },
                range,
            ))
        },
        |(id, draft, range), committed| {
            committed
                .state
                .publish_recovery(id, draft, range, chain_item)
        },
    );
    assert!(prepared.is_some(), "accepted recovery preparation is total");
}

fn nud_from_item<'source>(item: &Item<'source>, kind: NudKind) -> ScannedNud<'source> {
    let Payload::Tail { token, .. } = &item.payload else {
        unreachable!("ML NUD comes from a tail token")
    };
    ScannedNud {
        identity: item.identity,
        leading_trivia: item.leading_trivia.clone(),
        token: token.clone(),
        kind,
    }
}

fn emit_core<'source>(
    output: &mut PilotOutput<'source>,
    context: PilotContext<'source>,
    nud: &ScannedNud<'_>,
) {
    emit_trivia(output, &nud.leading_trivia);
    output.start_node(SyntaxKind::IdentifierExpression);
    output.token_range(
        syntax_kind_for_token(nud.token.kind),
        nud.token.lexeme.range.clone(),
    );
    output.finish_node();
    let range = nud.token.lexeme.range.clone();
    let word = WordSpan::from_root_range(context.root, range.clone());
    output.push_chain_item(
        OperatorChainItem::Primary(PrimaryExpression::Identifier(word)),
        range,
    );
}

fn emit_prefix<'source>(
    output: &mut PilotOutput<'source>,
    context: PilotContext<'source>,
    prefix: &ScannedNud<'_>,
) {
    emit_trivia(output, &prefix.leading_trivia);
    output.start_node(SyntaxKind::PrefixOperatorUse);
    output.token_range(SyntaxKind::Operator, prefix.token.lexeme.range.clone());
    output.finish_node();
    let range = prefix.token.lexeme.range.clone();
    output.push_chain_item(
        OperatorChainItem::PrefixUse(OperatorUse::from_root_range(
            context.root,
            range.clone(),
            OperatorRole::Prefix,
        )),
        range,
    );
}

fn emit_binary<'source>(
    output: &mut PilotOutput<'source>,
    context: PilotContext<'source>,
    item: &Item<'_>,
    _: BinaryOperator,
) {
    let range = token_range(item);
    emit_trivia(output, &item.leading_trivia);
    output.start_node(SyntaxKind::InfixOperatorUse);
    output.token_range(SyntaxKind::Operator, range.clone());
    output.finish_node();
    output.push_chain_item(
        OperatorChainItem::InfixUse(OperatorUse::from_root_range(
            context.root,
            range.clone(),
            OperatorRole::Infix,
        )),
        range,
    );
}

fn emit_call_open(output: &mut PilotOutput<'_>, item: &Item<'_>) {
    emit_trivia(output, &item.leading_trivia);
    output.start_node(SyntaxKind::CallTail);
    output.token_range(SyntaxKind::LParen, token_range(item));
}

fn emit_group_open(output: &mut PilotOutput<'_>, nud: &ScannedNud<'_>) {
    emit_trivia(output, &nud.leading_trivia);
    output.start_node(SyntaxKind::ParenthesizedExpression);
    output.token_range(SyntaxKind::LParen, nud.token.lexeme.range.clone());
}

fn emit_owned_close(output: &mut PilotOutput<'_>, item: Item<'_>) -> std::ops::Range<usize> {
    emit_trivia(output, &item.leading_trivia);
    let token = item
        .lexical_boundary_token
        .expect("a lexical close owns its token");
    let range = token.lexeme.range;
    output.token_range(SyntaxKind::RParen, range.clone());
    range
}

fn emit_borrowed_close(output: &mut PilotOutput<'_>, item: &Item<'_>) -> std::ops::Range<usize> {
    assert!(matches!(
        item.payload,
        Payload::Boundary(Boundary::BorrowedClose(Delimiter::Parenthesis))
    ));
    emit_trivia(output, &item.leading_trivia);
    let token = item
        .lexical_boundary_token
        .as_ref()
        .expect("a borrowed close retains lexical token evidence");
    assert_eq!(token.kind, TokenKind::RightParenthesis);
    assert_eq!(token.lexeme.text, ")");
    let range = token.lexeme.range.clone();
    output.token_range(SyntaxKind::RParen, range.clone());
    range
}

pub(super) fn emit_end(output: &mut PilotOutput<'_>, end: &End<'_>) {
    emit_trivia(output, &end.item.leading_trivia);
    if let Some(token) = &end.item.lexical_boundary_token {
        output.token_range(
            syntax_kind_for_token(token.kind),
            token.lexeme.range.clone(),
        );
    }
}

fn emit_trivia(output: &mut PilotOutput<'_>, trivia: &SourceSpan<'_>) {
    let mut offset = trivia.range.start;
    let bytes = trivia.text.as_bytes();
    let mut index = 0;
    while index < bytes.len() {
        let start = index;
        let newline = if bytes[index] == b'\r' && bytes.get(index + 1) == Some(&b'\n') {
            index += 2;
            true
        } else if bytes[index] == b'\n' {
            index += 1;
            true
        } else {
            while index < bytes.len() && bytes[index] != b'\r' && bytes[index] != b'\n' {
                index += 1;
            }
            false
        };
        let end = offset + (index - start);
        output.token_range(
            if newline {
                SyntaxKind::Newline
            } else {
                SyntaxKind::Whitespace
            },
            offset..end,
        );
        offset = end;
    }
}

fn token_kind(character: char) -> TokenKind {
    match character {
        '0'..='9' => TokenKind::Integer,
        '+' => TokenKind::InfixOperator(BinaryOperator::Add),
        '*' => TokenKind::InfixOperator(BinaryOperator::Multiply),
        '-' => TokenKind::PrefixOperator,
        '(' => TokenKind::LeftParenthesis,
        ')' => TokenKind::RightParenthesis,
        '.' => TokenKind::Dot,
        character if character.is_alphabetic() => TokenKind::Identifier,
        _ => TokenKind::Unknown,
    }
}

fn token_range(item: &Item<'_>) -> std::ops::Range<usize> {
    match &item.payload {
        Payload::Tail { token, .. } => token.lexeme.range.clone(),
        Payload::Boundary(_) => item
            .lexical_boundary_token
            .as_ref()
            .expect("a token boundary has lexical evidence")
            .lexeme
            .range
            .clone(),
    }
}

fn boundary_start(exit: &TailExit<'_>) -> usize {
    match exit {
        Err(Either::Left(item)) => item.extent.start,
        Err(Either::Right(end)) => end.item.extent.start,
        Ok(()) => 0,
    }
}

fn byte_offset(root: &str, index: *const u8) -> usize {
    let root_start = root.as_ptr() as usize;
    let index = index as usize;
    assert!(index >= root_start && index <= root_start + root.len());
    index - root_start
}
