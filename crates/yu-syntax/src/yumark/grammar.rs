//! Gate 3/4 isolated inline, block, command, and embedded-Yulang grammar.
//!
//! This is the one iterative grammar required by the doc-comment addendum
//! §§4–6.1 and 7–11. Document envelopes belong to later gates.

use std::ops::Range;

use unicode_ident::{is_xid_continue, is_xid_start};

use crate::{
    SyntaxKind,
    ambient_claim::AmbientClaimView,
    cursor::{Recover, SyntaxIn, SyntaxOutput, SyntaxOutputCheckpoint},
    handoff::{Either, MlMode, NormalizedExit},
    lexical::{
        current_item::LineEntry,
        expression_item::expression_item,
        item::TokenKind,
        item::{BorrowedTarget, Boundary, StopKind},
        operator_scan::OperatorSite,
        stops::{STOP_LINE_BREAK, STOP_SEMICOLON, stops_for},
        yumark::{
            FenceBoundary, FenceLineDecision, FenceOpener, FencePrefixPolicy, is_yulang_fence_info,
            judge_fence_line,
        },
    },
    operator_table::OperatorTable,
    statement::StatementLineHandoff,
};

use super::frame::{EnvelopeStop, FrameOwner, InlineClose, YumarkFrame, YumarkFrameStack};
use super::judge::{
    ActiveClose as JudgeActiveClose, ChunkContext, ChunkKind, InlineClose as JudgeInlineClose,
    judge_chunk,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum RecoveryOwner {
    DocComment,
    Section,
    List,
    ListItem,
    Quote,
    CodeFence,
    InlineGroup,
    InlineLink,
    InlineImage,
    InlineApply,
    InlineReference,
    Emphasis,
    Strong,
    Command,
    My,
    Use,
    DocArgument,
    DoCapture,
    IfChain,
    IfBranch,
    ElsifBranch,
    ElseBranch,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum RecoverySlot {
    Starter,
    Name,
    Arguments,
    Body,
    Destination,
    ClosingDelimiter,
    SectionClose,
    QuoteForm,
    Head,
    Condition,
    BodyIntroducer,
    ExpressionBody,
    Route,
    Terminator,
    BranchPredecessor,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Recovery {
    /// The generic Gate-1 recovery node kind (`Missing` or `Error`).
    pub(crate) kind: SyntaxKind,
    pub(crate) owner: RecoveryOwner,
    pub(crate) slot: RecoverySlot,
}

/// Minimal callback target for the neutral Gate-3 decision driver.
///
/// A checkpoint is an opaque output position. `replace_enter` changes only the
/// `Enter` emitted at that exact checkpoint, preserving all following events.
/// This is the streaming equivalent of Rowan's `start_node_at` and is needed
/// when a completed group is reclassified as a link or apply.
pub(crate) trait Sink {
    type Checkpoint: Clone;

    fn checkpoint(&mut self) -> Self::Checkpoint;
    fn enter(&mut self, kind: SyntaxKind);
    fn token(&mut self, kind: SyntaxKind, range: Range<usize>);
    fn exit(&mut self);
    fn recovery(&mut self, recovery: Recovery, range: Range<usize>);
    /// Publishes a recovery whose nonempty range may already have streamed.
    /// The checkpoint is an output-control handle, not an additional event.
    fn recovery_at(
        &mut self,
        checkpoint: &Self::Checkpoint,
        recovery: Recovery,
        range: Range<usize>,
    ) {
        let _ = checkpoint;
        self.recovery(recovery, range);
    }
    fn replace_enter(&mut self, checkpoint: &Self::Checkpoint, kind: SyntaxKind);
    /// Opens a node at an earlier output checkpoint, matching Rowan's
    /// `start_node_at`.  Gate 4 uses this once after the first ordinary
    /// command argument has been parsed and the written form is known.
    fn start_enter_at(&mut self, checkpoint: &Self::Checkpoint, kind: SyntaxKind);
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct Gate3State {
    pub(crate) consumed: usize,
    pub(crate) line: usize,
    pub(crate) column: usize,
    pub(crate) at_line_start: bool,
    pub(crate) frame_depth: usize,
    /// Counts committed source bytes. A byte is charged only when ownership
    /// advances, never by a rejected structural probe.
    pub(crate) byte_visits: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Mode {
    Block,
    /// A block document whose strict `---` close belongs to its envelope.
    /// The marker and its suffix are returned unconsumed to the Gate-5 driver.
    BlockDocument,
    Line,
}

#[derive(Clone, Debug)]
struct InlineFrame<C> {
    close: InlineClose,
    owner: RecoveryOwner,
    checkpoint: C,
    node: SyntaxKind,
}

pub(crate) fn parse<S: Sink>(
    source: &str,
    mode: Mode,
    operators: &OperatorTable,
    sink: &mut S,
) -> Gate3State
where
    S::Checkpoint: 'static,
{
    parse_at_document_base(source, mode, 0, operators, sink)
}

pub(crate) fn parse_at_document_base<S: Sink>(
    source: &str,
    mode: Mode,
    document_base_col: usize,
    operators: &OperatorTable,
    sink: &mut S,
) -> Gate3State
where
    S::Checkpoint: 'static,
{
    let mut parser = Parser {
        source,
        position: 0,
        line: 0,
        column: 0,
        at_line_start: true,
        byte_visits: 0,
        stop_at_document_close: mode == Mode::BlockDocument,
        document_base_col,
        operators,
        sink,
        frames: YumarkFrameStack::new(),
    };
    parser.frames.push(YumarkFrame::Document {
        base: 0,
        envelope_stop: match mode {
            Mode::Block | Mode::BlockDocument => EnvelopeStop::BlockDocument,
            Mode::Line => EnvelopeStop::LineDocument,
        },
    });
    parser.sink.enter(SyntaxKind::YmDoc);
    match mode {
        Mode::Block => parser.parse_block_iterative(false),
        Mode::BlockDocument => parser.parse_block_iterative(true),
        Mode::Line => {
            let end = physical_line(&source[parser.position..], parser.position).content_end;
            parser.parse_inline_until(end);
        }
    }
    parser.sink.exit();
    parser.frames.pop();
    Gate3State {
        consumed: parser.position,
        line: parser.line,
        column: parser.column,
        at_line_start: parser.at_line_start,
        frame_depth: parser.frames.len(),
        byte_visits: parser.byte_visits,
    }
}

struct Parser<'source, 'sink, 'operators, S> {
    source: &'source str,
    position: usize,
    line: usize,
    column: usize,
    at_line_start: bool,
    byte_visits: usize,
    stop_at_document_close: bool,
    document_base_col: usize,
    operators: &'operators OperatorTable,
    sink: &'sink mut S,
    frames: YumarkFrameStack,
}

/// Streams canonical parser output directly into the neutral Yumark sink.
/// `position` is advanced only by canonical token emission, so no CST walk,
/// event replay, or source slice reparse is involved.
struct EmbeddedOutput<'sink, S> {
    sink: &'sink mut S,
    position: usize,
}

impl<S: Sink> SyntaxOutput for EmbeddedOutput<'_, S>
where
    S::Checkpoint: 'static,
{
    fn start_node(&mut self, kind: rowan::SyntaxKind) {
        self.sink
            .enter(<crate::YulangLanguage as rowan::Language>::kind_from_raw(
                kind,
            ));
    }

    fn token(&mut self, kind: rowan::SyntaxKind, text: &str) {
        let start = self.position;
        self.position += text.len();
        self.sink.token(
            <crate::YulangLanguage as rowan::Language>::kind_from_raw(kind),
            start..self.position,
        );
    }

    fn finish_node(&mut self) {
        self.sink.exit();
    }

    fn checkpoint(&mut self) -> SyntaxOutputCheckpoint {
        SyntaxOutputCheckpoint::new(self.sink.checkpoint())
    }

    fn start_node_at(&mut self, checkpoint: &SyntaxOutputCheckpoint, kind: rowan::SyntaxKind) {
        let checkpoint = checkpoint
            .downcast_ref::<S::Checkpoint>()
            .expect("an embedded output receives its own sink checkpoint");
        self.sink.start_enter_at(
            checkpoint,
            <crate::YulangLanguage as rowan::Language>::kind_from_raw(kind),
        );
    }
}

#[derive(Clone, Copy, Debug)]
struct PhysicalLine {
    start: usize,
    content_end: usize,
    end: usize,
    indent_end: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum OpenBlock {
    Section {
        level: usize,
        explicit_body_indent: Option<usize>,
    },
    List {
        indent: usize,
    },
    ListItem {
        indent: usize,
        content: usize,
    },
    PrefixQuote {
        depth: usize,
    },
    ExplicitQuote {
        depth: usize,
    },
    CommandBody {
        parent_indent: usize,
        body_indent: usize,
        capture: bool,
        command_start: usize,
    },
    DoCapture {
        indent: usize,
    },
}

fn physical_line(source: &str, origin: usize) -> PhysicalLine {
    let (content_len, end_len) = match source.find('\n') {
        Some(lf) if lf > 0 && source.as_bytes()[lf - 1] == b'\r' => (lf - 1, lf + 1),
        Some(lf) => (lf, lf + 1),
        None => (source.len(), source.len()),
    };
    let indent = source[..content_len]
        .bytes()
        .take_while(|byte| matches!(byte, b' ' | b'\t'))
        .count();
    PhysicalLine {
        start: origin,
        content_end: origin + content_len,
        end: origin + end_len,
        indent_end: origin + indent,
    }
}

impl<S: Sink> Parser<'_, '_, '_, S>
where
    S::Checkpoint: 'static,
{
    fn advance_to(&mut self, end: usize) {
        debug_assert!(end >= self.position && end <= self.source.len());
        let consumed = &self.source[self.position..end];
        self.byte_visits += consumed.len();
        for byte in consumed.bytes() {
            if byte == b'\n' {
                self.line += 1;
                self.column = 0;
                self.at_line_start = true;
            } else {
                self.column += 1;
                self.at_line_start = false;
            }
        }
        self.position = end;
    }

    fn emit_token(&mut self, kind: SyntaxKind, range: Range<usize>) {
        self.sink.token(kind, range.clone());
        self.advance_to(range.end);
    }

    /// Settles bytes already consumed by one canonical embedded parse.  The
    /// canonical lexer is their only scanner; this updates only the shared
    /// Yumark position/line ledger and charges each settled byte once.
    fn settle_embedded_to(&mut self, end: usize) {
        self.advance_to(end);
    }

    fn parse_embedded_expression(&mut self, stops: u16, limit: usize) -> bool {
        let start = self.position;
        let mut remaining = &self.source[start..limit];
        let mut recover = Recover::new(self.operators);
        let (parsed, end) = {
            let mut output = EmbeddedOutput {
                sink: &mut *self.sink,
                position: start,
            };
            let exit = crate::expression::expr_normalized(
                SyntaxIn::new(&mut remaining, &mut recover, &mut output),
                None,
                0,
                stops,
                MlMode::All,
                StatementLineHandoff::OrdinaryLayout,
                start,
                LineEntry::InLine,
                None,
                Some(AmbientClaimView::root_statement(0)).into(),
                None,
            );
            let parsed = exit.is_some();
            if let Some(exit) = exit {
                let pending = match exit {
                    NormalizedExit::Complete(Err(Either::Left(item)), _)
                    | NormalizedExit::Deferred(item, _) => Some(item),
                    NormalizedExit::Complete(Err(Either::Right(end)), _) => Some(end.item),
                    NormalizedExit::Complete(Ok(()), _) => None,
                };
                if let Some(mut item) = pending {
                    item.emit_all_remaining_leading(&mut output);
                }
            }
            (parsed, output.position)
        };
        self.settle_embedded_to(end);
        parsed
    }

    /// Required-expression counterpart used by `if`/`elsif`.  In particular,
    /// an immediate outer `)` is handed to the existing required operand
    /// parser, which emits its canonical missing-expression record while the
    /// Yumark wrapper retains the closer.
    fn parse_required_embedded_expression(&mut self, stops: u16, limit: usize) {
        let start = self.position;
        let mut remaining = &self.source[start..limit];
        let mut recover = Recover::new(self.operators);
        let end = {
            let mut output = EmbeddedOutput {
                sink: &mut *self.sink,
                position: start,
            };
            let mut input = SyntaxIn::new(&mut remaining, &mut recover, &mut output);
            let (item, origin, line_entry) = expression_item(
                input.rb(),
                OperatorSite::Nud,
                start,
                LineEntry::InLine,
                None,
                0,
                stops,
            );
            input.state.start_node(SyntaxKind::OperatorChain.into());
            let exit = crate::expression::required_expr_item_normalized(
                input.rb(),
                item,
                None,
                0,
                stops,
                MlMode::All,
                StatementLineHandoff::OrdinaryLayout,
                origin,
                line_entry,
                None,
                Some(AmbientClaimView::root_statement(0)).into(),
                None,
            );
            input.state.finish_node();
            let mut pending = match exit {
                NormalizedExit::Complete(Err(Either::Left(item)), _)
                | NormalizedExit::Deferred(item, _) => Some(item),
                NormalizedExit::Complete(Err(Either::Right(end)), _) => Some(end.item),
                NormalizedExit::Complete(Ok(()), _) => None,
            };
            if let Some(item) = pending.as_mut() {
                item.emit_all_remaining_leading(input.state);
            }
            output.position
        };
        self.settle_embedded_to(end);
    }

    /// Shared §6.1 paired-delimiter bridge for call arguments. Yumark owns
    /// `(`/`)`; canonical expressions own every interior token and node.
    fn parse_yulang_arguments(&mut self, home: SyntaxKind, owner: RecoveryOwner, limit: usize) {
        self.sink.enter(home);
        self.parse_parenthesized_yulang(owner, limit);
        self.sink.exit();
    }

    /// Parses a Yumark-owned parenthesized payload directly below an adapter
    /// that is already open (notably `YmIfCondition`/`YmElsifCondition`).
    fn parse_parenthesized_yulang(&mut self, owner: RecoveryOwner, limit: usize) {
        let open = self.position;
        self.emit_token(SyntaxKind::LParen, open..open + 1);
        self.frames.push(YumarkFrame::EmbeddedYulang {
            owner: match owner {
                RecoveryOwner::InlineReference => FrameOwner::InlineReference,
                RecoveryOwner::InlineApply => FrameOwner::InlineApply,
                RecoveryOwner::Command => FrameOwner::Command,
                RecoveryOwner::IfBranch => FrameOwner::IfBranch,
                RecoveryOwner::ElsifBranch => FrameOwner::ElsifBranch,
                RecoveryOwner::ElseBranch => FrameOwner::ElseBranch,
                _ => FrameOwner::Command,
            },
            outer_kind: super::frame::EmbeddedOuterKind::Parenthesis,
            delimiter_floor: super::frame::DelimiterFloor(self.frames.len()),
        });

        let stops = stops_for(TokenKind::RParen) | STOP_LINE_BREAK;
        loop {
            if self.position >= limit || self.position >= self.source.len() {
                self.missing(owner, RecoverySlot::ClosingDelimiter, self.position);
                break;
            }
            match self.source.as_bytes()[self.position] {
                b')' => {
                    let close = self.position;
                    self.emit_token(SyntaxKind::RParen, close..close + 1);
                    break;
                }
                b',' => {
                    let comma = self.position;
                    self.emit_token(SyntaxKind::Comma, comma..comma + 1);
                }
                b'\n' | b'\r' => {
                    self.missing(owner, RecoverySlot::ClosingDelimiter, self.position);
                    break;
                }
                _ => {
                    let before = self.position;
                    if !self.parse_embedded_expression(stops, limit) {
                        self.missing(owner, RecoverySlot::Arguments, self.position);
                        break;
                    }
                    if self.position == before {
                        self.missing(owner, RecoverySlot::Arguments, self.position);
                        break;
                    }
                }
            }
        }
        self.frames.pop();
    }

    fn parse_parenthesized_condition(&mut self, owner: RecoveryOwner, limit: usize) {
        let open = self.position;
        self.emit_token(SyntaxKind::LParen, open..open + 1);
        self.frames.push(YumarkFrame::EmbeddedYulang {
            owner: match owner {
                RecoveryOwner::IfBranch => FrameOwner::IfBranch,
                RecoveryOwner::ElsifBranch => FrameOwner::ElsifBranch,
                _ => FrameOwner::ElseBranch,
            },
            outer_kind: super::frame::EmbeddedOuterKind::Parenthesis,
            delimiter_floor: super::frame::DelimiterFloor(self.frames.len()),
        });
        self.parse_required_embedded_expression(
            stops_for(TokenKind::RParen) | STOP_LINE_BREAK,
            limit,
        );
        if self.position < limit && self.source.as_bytes()[self.position] == b')' {
            self.emit_token(SyntaxKind::RParen, self.position..self.position + 1);
        } else {
            self.missing(owner, RecoverySlot::ClosingDelimiter, self.position);
        }
        self.frames.pop();
    }

    /// The production Gate-3 block path. All structural nesting is represented
    /// by `open`; it never calls a Yumark block parser through Rust recursion.
    fn parse_block_iterative(&mut self, stop_at_document_close: bool) {
        let mut open = Vec::new();
        while self.position < self.source.len() {
            let line = physical_line(&self.source[self.position..], self.position);
            if stop_at_document_close
                && matches!(
                    judge_chunk(
                        &self.source[line.indent_end..],
                        line.indent_end,
                        ChunkContext {
                            at_line_start: true,
                            indent_col: line.indent_end - line.start,
                            base_col: self.document_base_col,
                            active_close: Some(JudgeActiveClose::BlockDocument {
                                after_opening_line: true,
                            }),
                        },
                    )
                    .kind,
                    ChunkKind::Terminator(super::judge::TerminatorKind::BlockDocument)
                )
            {
                break;
            }
            let content = &self.source[line.indent_end..line.content_end];

            if line.indent_end < line.content_end {
                let indent = line.indent_end - line.start;
                if let Some(explicit) = open.iter().rposition(|entry| {
                    matches!(entry, OpenBlock::Section { explicit_body_indent: Some(body), .. } if indent < *body)
                }) {
                    while open.len() > explicit {
                        self.close_open_block(&mut open, false);
                    }
                }
                if let Some(command) = open.iter().rposition(|entry| match entry {
                    OpenBlock::CommandBody { body_indent, .. } => indent < *body_indent,
                    OpenBlock::DoCapture { indent: owner } => indent < *owner,
                    _ => false,
                }) {
                    while open.len() > command {
                        let before = open.len();
                        self.close_open_block(&mut open, false);
                        if open.len() == before
                            && matches!(open.last(), Some(OpenBlock::DoCapture { .. }))
                        {
                            break;
                        }
                    }
                }
            }

            if line.indent_end == line.content_end {
                while matches!(open.last(), Some(OpenBlock::PrefixQuote { .. })) {
                    self.close_open_block(&mut open, false);
                }
                self.sink.enter(SyntaxKind::YmBlankLine);
                if line.indent_end > line.start {
                    self.emit_token(SyntaxKind::Whitespace, line.start..line.indent_end);
                }
                if line.end > line.content_end {
                    self.emit_token(SyntaxKind::Newline, line.content_end..line.end);
                }
                self.sink.exit();
                continue;
            }

            let quote = quote_facts(content, line.indent_end);
            if quote.is_none() && self.position < line.indent_end {
                self.emit_token(SyntaxKind::Whitespace, line.start..line.indent_end);
            }

            if let Some((level, marker_end, is_close)) = heading_facts(content, line.indent_end) {
                self.close_open_non_sections(&mut open);
                while matches!(open.last(), Some(OpenBlock::Section { level: active, .. }) if *active > level || !is_close && *active == level)
                {
                    self.close_open_block(&mut open, false);
                }
                if is_close {
                    if matches!(open.last(), Some(OpenBlock::Section { level: active, .. }) if *active == level)
                    {
                        self.sink.enter(SyntaxKind::YmSectionClose);
                        self.emit_token(SyntaxKind::YmHeadingMarker, line.indent_end..marker_end);
                        self.sink.exit();
                        self.finish_line(line);
                        self.close_open_block(&mut open, false);
                    } else {
                        let recovery_checkpoint = self.sink.checkpoint();
                        self.sink.enter(SyntaxKind::YmSectionClose);
                        self.emit_token(SyntaxKind::YmHeadingMarker, line.indent_end..marker_end);
                        self.sink.exit();
                        self.sink.recovery_at(
                            &recovery_checkpoint,
                            Recovery {
                                kind: SyntaxKind::Error,
                                owner: RecoveryOwner::Section,
                                slot: RecoverySlot::SectionClose,
                            },
                            line.indent_end..marker_end,
                        );
                        self.finish_line(line);
                    }
                } else {
                    self.open_section_iterative(&mut open, line, level, marker_end);
                }
                continue;
            }

            if !content.starts_with('>') {
                while matches!(open.last(), Some(OpenBlock::PrefixQuote { .. })) {
                    self.close_open_block(&mut open, false);
                }
            }

            if let Some(marker_end) = list_marker_end(content, line.indent_end) {
                self.open_list_line_iterative(&mut open, line, marker_end);
                continue;
            }

            if content.starts_with('\\')
                && content[1..].chars().next().is_some_and(identifier_start)
            {
                self.settle_list_continuation(&mut open, line.indent_end - line.start);
                self.parse_command_line(&mut open, line);
                continue;
            }

            if raw_fence_opener(&self.source[line.indent_end..], line.indent_end) {
                self.close_open_lists(&mut open);
                self.parse_fence(line);
                continue;
            }

            if let Some((depth, marker_end, explicit)) = quote {
                self.close_open_lists(&mut open);
                self.open_quote_line_iterative(&mut open, line, depth, marker_end, explicit);
                continue;
            }

            if self.settle_list_continuation(&mut open, line.indent_end - line.start) {
                continue;
            }
            self.parse_paragraph(line);
        }
        while !open.is_empty() {
            self.close_open_block(&mut open, false);
        }
    }

    fn open_section_iterative(
        &mut self,
        open: &mut Vec<OpenBlock>,
        line: PhysicalLine,
        level: usize,
        marker_end: usize,
    ) {
        let title_start = marker_end + 1;
        let (title_end, explicit) = terminal_colon(self.source, title_start, line.content_end);
        self.sink.enter(SyntaxKind::YmSection);
        self.sink.enter(if explicit {
            SyntaxKind::YmExplicitSection
        } else {
            SyntaxKind::YmImplicitSection
        });
        self.frames.push(if explicit {
            YumarkFrame::ExplicitSection {
                level,
                parent_indent: line.indent_end - line.start,
                body_indent: usize::MAX,
            }
        } else {
            YumarkFrame::ImplicitSection { level }
        });
        self.sink.enter(SyntaxKind::YmHeading);
        self.emit_token(SyntaxKind::YmHeadingMarker, line.indent_end..marker_end);
        self.emit_token(SyntaxKind::Whitespace, marker_end..title_start);
        self.parse_inline_until(title_end);
        if explicit {
            self.emit_token(SyntaxKind::Colon, title_end..title_end + 1);
            if self.position < line.content_end {
                self.emit_token(SyntaxKind::Whitespace, self.position..line.content_end);
            }
        }
        self.sink.exit();
        if line.end > line.content_end {
            self.emit_token(SyntaxKind::Newline, line.content_end..line.end);
        }
        self.sink.enter(SyntaxKind::YmDoc);
        let explicit_body_indent = if explicit && self.position < self.source.len() {
            let body = physical_line(&self.source[self.position..], self.position);
            (body.indent_end > body.start + (line.indent_end - line.start)
                && body.indent_end < body.content_end)
                .then_some(body.indent_end - body.start)
        } else {
            None
        };
        open.push(OpenBlock::Section {
            level,
            explicit_body_indent,
        });

        if explicit {
            if self.position == self.source.len() {
                self.missing(RecoveryOwner::Section, RecoverySlot::Body, self.position);
            } else {
                if explicit_body_indent.is_none() {
                    self.missing(RecoveryOwner::Section, RecoverySlot::Body, self.position);
                    self.close_open_block(open, false);
                }
            }
        }
    }

    fn open_list_line_iterative(
        &mut self,
        open: &mut Vec<OpenBlock>,
        line: PhysicalLine,
        marker_end: usize,
    ) {
        let indent = line.indent_end - line.start;
        let content_column = marker_end + 1 - line.start;
        loop {
            let item = open.iter().rev().find_map(|entry| match entry {
                OpenBlock::ListItem { indent, content } => Some((*indent, *content)),
                _ => None,
            });
            match item {
                Some((active, _)) if active == indent => {
                    if matches!(open.last(), Some(OpenBlock::ListItem { .. })) {
                        self.close_open_block(open, false);
                    }
                    break;
                }
                Some((_, content)) if indent >= content => break,
                Some(_) => {
                    self.close_lists_deeper_than(open, indent);
                    continue;
                }
                None => break,
            }
        }
        if !matches!(open.last(), Some(OpenBlock::List { indent: active }) if *active == indent) {
            self.sink.enter(SyntaxKind::YmList);
            self.frames.push(YumarkFrame::List { indent });
            open.push(OpenBlock::List { indent });
        }
        self.sink.enter(SyntaxKind::YmListItem);
        self.frames.push(YumarkFrame::ListItem {
            marker: line.indent_end..marker_end + 1,
            indent,
            content_column,
        });
        self.emit_token(SyntaxKind::YmListMarker, line.indent_end..marker_end + 1);
        self.sink.enter(SyntaxKind::YmListItemBody);
        self.sink.enter(SyntaxKind::YmDoc);
        open.push(OpenBlock::ListItem {
            indent,
            content: content_column,
        });
        if self.source[self.position..line.content_end].starts_with('\\') {
            self.parse_command_line(open, line);
        } else {
            self.parse_paragraph(line);
        }
    }

    fn open_quote_line_iterative(
        &mut self,
        open: &mut Vec<OpenBlock>,
        line: PhysicalLine,
        depth: usize,
        marker_end: usize,
        explicit: bool,
    ) {
        if explicit
            && matches!(open.last(), Some(OpenBlock::ExplicitQuote { depth: active }) if *active == depth)
        {
            if self.position < line.indent_end {
                self.emit_token(SyntaxKind::Whitespace, line.start..line.indent_end);
            }
            self.sink.exit();
            self.emit_token(SyntaxKind::YmQuoteFenceMarker, line.indent_end..marker_end);
            self.sink.exit();
            open.pop();
            self.frames.pop();
            if self.position < line.content_end {
                self.emit_token(SyntaxKind::Whitespace, self.position..line.content_end);
            }
            if line.end > line.content_end {
                self.emit_token(SyntaxKind::Newline, line.content_end..line.end);
            }
            return;
        }
        if explicit && matches!(open.last(), Some(OpenBlock::PrefixQuote { .. })) {
            if self.position < line.indent_end {
                self.emit_token(SyntaxKind::Whitespace, line.start..line.indent_end);
            }
            self.sink.recovery(
                Recovery {
                    kind: SyntaxKind::Error,
                    owner: RecoveryOwner::Quote,
                    slot: RecoverySlot::QuoteForm,
                },
                line.indent_end..marker_end,
            );
            self.emit_token(SyntaxKind::YmQuoteFenceMarker, line.indent_end..marker_end);
            self.finish_line(line);
            return;
        }
        if explicit {
            if self.position < line.indent_end {
                self.emit_token(SyntaxKind::Whitespace, line.start..line.indent_end);
            }
            self.sink.enter(SyntaxKind::YmQuoteBlock);
            self.frames.push(YumarkFrame::ExplicitQuote {
                depth,
                marker: line.indent_end..marker_end,
            });
            self.emit_token(SyntaxKind::YmQuoteFenceMarker, line.indent_end..marker_end);
            self.sink.enter(SyntaxKind::YmDoc);
            open.push(OpenBlock::ExplicitQuote { depth });
            self.finish_line(line);
            return;
        }
        if matches!(open.last(), Some(OpenBlock::ExplicitQuote { .. })) {
            self.sink.recovery(
                Recovery {
                    kind: SyntaxKind::Error,
                    owner: RecoveryOwner::Quote,
                    slot: RecoverySlot::QuoteForm,
                },
                line.indent_end..marker_end,
            );
            self.emit_token(SyntaxKind::YmQuotePrefix, line.start..marker_end);
            self.parse_paragraph(PhysicalLine {
                start: self.position,
                indent_end: self.position,
                content_end: line.content_end,
                end: line.end,
            });
            return;
        }
        while matches!(open.last(), Some(OpenBlock::PrefixQuote { depth: active }) if *active > depth)
        {
            self.close_open_block(open, false);
        }
        if !matches!(open.last(), Some(OpenBlock::PrefixQuote { depth: active }) if *active == depth)
        {
            self.sink.enter(SyntaxKind::YmQuoteBlock);
            self.frames.push(YumarkFrame::PrefixQuote { depth });
            self.sink.enter(SyntaxKind::YmDoc);
            open.push(OpenBlock::PrefixQuote { depth });
        }
        self.emit_token(SyntaxKind::YmQuotePrefix, line.start..marker_end);
        let logical = PhysicalLine {
            start: self.position,
            indent_end: self.position,
            content_end: line.content_end,
            end: line.end,
        };
        if raw_fence_opener(&self.source[self.position..], self.position) {
            self.parse_prefixed_fence(logical, depth);
        } else if let Some(marker_end) =
            list_marker_end(&self.source[self.position..line.content_end], self.position)
        {
            self.open_list_line_iterative(open, logical, marker_end);
        } else if self.source[self.position..line.content_end].starts_with('\\') {
            self.parse_command_line(open, logical);
        } else {
            self.parse_paragraph(logical);
        }
    }

    fn close_open_non_sections(&mut self, open: &mut Vec<OpenBlock>) {
        while !matches!(open.last(), None | Some(OpenBlock::Section { .. })) {
            self.close_open_block(open, false);
        }
    }

    fn close_open_lists(&mut self, open: &mut Vec<OpenBlock>) {
        while matches!(
            open.last(),
            Some(OpenBlock::List { .. } | OpenBlock::ListItem { .. })
        ) {
            self.close_open_block(open, false);
        }
    }

    fn close_lists_deeper_than(&mut self, open: &mut Vec<OpenBlock>, indent: usize) {
        while matches!(
            open.last(),
            Some(OpenBlock::ListItem { indent: active, .. } | OpenBlock::List { indent: active })
                if *active > indent
        ) {
            self.close_open_block(open, false);
        }
    }

    fn settle_list_continuation(&mut self, open: &mut Vec<OpenBlock>, line_indent: usize) -> bool {
        let mut returned = false;
        loop {
            let Some((item_indent, content)) = open.iter().rev().find_map(|entry| match entry {
                OpenBlock::ListItem { indent, content } => Some((*indent, *content)),
                _ => None,
            }) else {
                return returned;
            };
            if line_indent >= content {
                return returned;
            }
            // Both strict dedent and the approved middle-indentation row close
            // this item. No byte of the returning line is consumed.
            returned = true;
            while !matches!(open.last(), Some(OpenBlock::ListItem { indent, .. }) if *indent == item_indent)
            {
                self.close_open_block(open, false);
            }
            self.close_open_block(open, false);
            if matches!(open.last(), Some(OpenBlock::List { indent }) if *indent > line_indent) {
                self.close_open_block(open, false);
            }
        }
    }

    fn close_open_block(&mut self, open: &mut Vec<OpenBlock>, explicit_closed: bool) {
        let Some(block) = open.pop() else {
            return;
        };
        match block {
            OpenBlock::Section { .. } => {
                self.sink.exit();
                self.sink.exit();
                self.sink.exit();
                self.frames.pop();
            }
            OpenBlock::List { .. } => {
                self.sink.exit();
                self.frames.pop();
            }
            OpenBlock::ListItem { .. } => {
                self.sink.exit();
                self.sink.exit();
                self.sink.exit();
                self.frames.pop();
            }
            OpenBlock::PrefixQuote { .. } => {
                self.sink.exit();
                self.sink.exit();
                self.frames.pop();
            }
            OpenBlock::ExplicitQuote { .. } => {
                if !explicit_closed {
                    self.missing(
                        RecoveryOwner::Quote,
                        RecoverySlot::ClosingDelimiter,
                        self.position,
                    );
                }
                self.sink.exit();
                self.sink.exit();
                self.frames.pop();
            }
            OpenBlock::CommandBody {
                parent_indent,
                capture,
                command_start,
                ..
            } => {
                self.sink.exit();
                self.sink.exit();
                self.frames.pop();
                if capture {
                    self.sink.enter(SyntaxKind::YmDoCapture);
                    self.sink.enter(SyntaxKind::YmDoc);
                    self.frames.push(YumarkFrame::DoCapture {
                        command_start,
                        indent: parent_indent,
                    });
                    open.push(OpenBlock::DoCapture {
                        indent: parent_indent,
                    });
                } else {
                    self.sink.exit();
                }
            }
            OpenBlock::DoCapture { .. } => {
                self.sink.exit();
                self.sink.exit();
                self.sink.exit();
                self.frames.pop();
            }
        }
    }

    fn emit_horizontal_to(&mut self, end: usize) {
        if self.position < end {
            self.emit_token(SyntaxKind::Whitespace, self.position..end);
        }
    }

    fn horizontal_end(&self, limit: usize) -> usize {
        let mut end = self.position;
        while end < limit && matches!(self.source.as_bytes()[end], b' ' | b'\t') {
            end += 1;
        }
        end
    }

    fn strict_colon_body(&self, line: PhysicalLine) -> bool {
        if self.position >= line.content_end || self.source.as_bytes()[self.position] != b':' {
            return false;
        }
        self.source[self.position + 1..line.content_end]
            .bytes()
            .all(|byte| matches!(byte, b' ' | b'\t'))
            && line.end > line.content_end
    }

    fn parse_doc_argument(&mut self, limit: usize) {
        self.sink.enter(SyntaxKind::YmDocArg);
        self.frames.push(YumarkFrame::Inline {
            owner: FrameOwner::DocArgument,
            close: InlineClose::RightBracket,
        });
        let open = self.position;
        self.emit_token(SyntaxKind::LBracket, open..open + 1);
        self.sink.enter(SyntaxKind::YmDoc);
        self.parse_inline_owned_until(limit, Some(b']'));
        self.sink.exit();
        if self.position < limit && self.source.as_bytes()[self.position] == b']' {
            let close = self.position;
            self.emit_token(SyntaxKind::RBracket, close..close + 1);
        } else {
            self.missing(
                RecoveryOwner::DocArgument,
                RecoverySlot::ClosingDelimiter,
                self.position,
            );
        }
        self.frames.pop();
        self.sink.exit();
    }

    fn parse_do_candidate(&mut self, limit: usize) -> Option<bool> {
        if !self.source[self.position..limit].starts_with("(do") {
            return None;
        }
        let after_word = self.position + 3;
        if after_word < limit
            && self.source[after_word..]
                .chars()
                .next()
                .is_some_and(|character| character == '_' || is_xid_continue(character))
        {
            return None;
        }
        self.emit_token(SyntaxKind::LParen, self.position..self.position + 1);
        self.emit_token(SyntaxKind::Identifier, self.position..after_word);
        if after_word < limit && self.source.as_bytes()[after_word] == b')' {
            self.emit_token(SyntaxKind::RParen, after_word..after_word + 1);
            return Some(true);
        }
        let error_start = self.position;
        while self.position < limit
            && !matches!(self.source.as_bytes()[self.position], b')' | b'\r' | b'\n')
        {
            self.advance_to(self.position + 1);
        }
        if self.position > error_start {
            self.sink.recovery(
                Recovery {
                    kind: SyntaxKind::Error,
                    owner: RecoveryOwner::DoCapture,
                    slot: RecoverySlot::Arguments,
                },
                error_start..self.position,
            );
        }
        if self.position < limit && self.source.as_bytes()[self.position] == b')' {
            self.emit_token(SyntaxKind::RParen, self.position..self.position + 1);
        } else {
            self.missing(
                RecoveryOwner::DoCapture,
                RecoverySlot::ClosingDelimiter,
                self.position,
            );
        }
        Some(false)
    }

    fn parse_command_line(&mut self, open: &mut Vec<OpenBlock>, line: PhysicalLine) {
        let command_start = self.position;
        let checkpoint = self.sink.checkpoint();
        self.emit_token(SyntaxKind::YmBackslash, self.position..self.position + 1);
        let name_start = self.position;
        let name_end = identifier_end(self.source, name_start, line.content_end);
        self.emit_token(SyntaxKind::Identifier, name_start..name_end);
        let name = &self.source[name_start..name_end];

        match name {
            "my" => {
                self.sink.start_enter_at(&checkpoint, SyntaxKind::YmMy);
                self.parse_my_tail(open, line, command_start);
                return;
            }
            "use" => {
                self.sink.start_enter_at(&checkpoint, SyntaxKind::YmUse);
                self.parse_use_tail(line);
                self.sink.exit();
                self.finish_line(line);
                return;
            }
            "if" | "elsif" | "else" => {
                self.sink.start_enter_at(&checkpoint, SyntaxKind::YmIfChain);
                self.parse_if_chain_line(name, line, &checkpoint);
                self.sink.exit();
                return;
            }
            _ => {}
        }

        // §6 permits one speculative ordinary argument and no search through
        // an arbitrary argument run.  Its already-emitted events are wrapped
        // at `argument_checkpoint` only if the immediately following surface
        // proves block-command form.
        let argument_checkpoint = self.sink.checkpoint();
        let mut promoted = false;
        let mut capture = false;
        let mut arguments_open = false;
        let mut command_open = false;

        if self.position < line.content_end {
            match self.source.as_bytes()[self.position] {
                b'[' => {
                    promoted = true;
                    self.sink.start_enter_at(&checkpoint, SyntaxKind::YmCommand);
                    command_open = true;
                    self.sink.enter(SyntaxKind::YmCommandArgs);
                    arguments_open = true;
                    self.parse_doc_argument(line.content_end);
                }
                b'(' => {
                    if let Some(enabled) = self.parse_do_candidate(line.content_end) {
                        promoted = true;
                        capture = enabled;
                        self.sink.start_enter_at(&checkpoint, SyntaxKind::YmCommand);
                        command_open = true;
                        self.sink
                            .start_enter_at(&argument_checkpoint, SyntaxKind::YmCommandArgs);
                        arguments_open = true;
                    } else {
                        self.parse_yulang_arguments(
                            SyntaxKind::YmYulangArgs,
                            RecoveryOwner::Command,
                            line.content_end,
                        );
                        let followed_by_doc = self.position < line.content_end
                            && self.source.as_bytes()[self.position] == b'[';
                        let followed_by_brace = self.position < line.content_end
                            && self.source.as_bytes()[self.position] == b'{';
                        if followed_by_doc || followed_by_brace || self.strict_colon_body(line) {
                            promoted = true;
                            self.sink.start_enter_at(&checkpoint, SyntaxKind::YmCommand);
                            command_open = true;
                            self.sink
                                .start_enter_at(&argument_checkpoint, SyntaxKind::YmCommandArgs);
                            arguments_open = true;
                        }
                    }
                }
                b'{' => {
                    promoted = true;
                    self.sink.start_enter_at(&checkpoint, SyntaxKind::YmCommand);
                    command_open = true;
                }
                b':' if self.strict_colon_body(line) => {
                    promoted = true;
                    self.sink.start_enter_at(&checkpoint, SyntaxKind::YmCommand);
                    command_open = true;
                }
                _ => {}
            }
        }

        if promoted && !capture {
            // After block evidence commits the form, later command arguments
            // are no longer probes and are consumed once in source order.
            while self.position < line.content_end {
                match self.source.as_bytes()[self.position] {
                    b'[' => {
                        if !arguments_open {
                            self.sink.enter(SyntaxKind::YmCommandArgs);
                            arguments_open = true;
                        }
                        self.parse_doc_argument(line.content_end);
                    }
                    b'(' => {
                        if !arguments_open {
                            self.sink.enter(SyntaxKind::YmCommandArgs);
                            arguments_open = true;
                        }
                        self.parse_yulang_arguments(
                            SyntaxKind::YmYulangArgs,
                            RecoveryOwner::Command,
                            line.content_end,
                        );
                    }
                    _ => break,
                }
            }
        } else if promoted && capture {
            // `do` is the sole command argument.  A later argument is retained
            // as one maximal local error and disables sibling capture.
            let unexpected = self.position;
            let recovery_checkpoint = self.sink.checkpoint();
            while self.position < line.content_end
                && matches!(self.source.as_bytes()[self.position], b'(' | b'[')
            {
                if self.source.as_bytes()[self.position] == b'(' {
                    self.parse_yulang_arguments(
                        SyntaxKind::YmYulangArgs,
                        RecoveryOwner::Command,
                        line.content_end,
                    );
                } else {
                    self.parse_doc_argument(line.content_end);
                }
            }
            if self.position > unexpected {
                self.sink.recovery_at(
                    &recovery_checkpoint,
                    Recovery {
                        kind: SyntaxKind::Error,
                        owner: RecoveryOwner::DoCapture,
                        slot: RecoverySlot::Arguments,
                    },
                    unexpected..self.position,
                );
                capture = false;
            }
        }

        if arguments_open {
            self.sink.exit();
        }

        if !promoted {
            if self.position < line.content_end && self.source.as_bytes()[self.position] == b';' {
                self.emit_token(SyntaxKind::Semicolon, self.position..self.position + 1);
            }
            self.sink
                .start_enter_at(&checkpoint, SyntaxKind::YmInlineRef);
            self.sink.exit();
            self.sink
                .start_enter_at(&checkpoint, SyntaxKind::YmParagraph);
            let last = self.paragraph_last_line(line);
            self.parse_inline_until(last.content_end);
            self.sink.exit();
            if last.end > last.content_end {
                self.emit_token(SyntaxKind::Newline, last.content_end..last.end);
            }
            return;
        }

        debug_assert!(command_open, "every promoted command opens its owner");

        let braced =
            self.position < line.content_end && self.source.as_bytes()[self.position] == b'{';
        let indented = self.strict_colon_body(line);

        if braced {
            let closed = self.parse_braced_command_body(
                self.source.len(),
                FrameOwner::Command,
                RecoveryOwner::Command,
            );
            if closed {
                self.finish_after_braced(line);
            }
            if capture {
                self.sink.enter(SyntaxKind::YmDoCapture);
                self.sink.enter(SyntaxKind::YmDoc);
                self.frames.push(YumarkFrame::DoCapture {
                    command_start,
                    indent: line.indent_end - line.start,
                });
                open.push(OpenBlock::DoCapture {
                    indent: line.indent_end - line.start,
                });
            } else {
                self.sink.exit();
            }
            return;
        } else if indented {
            let colon = self.position;
            self.emit_token(SyntaxKind::Colon, colon..colon + 1);
            self.emit_horizontal_to(line.content_end);
            if line.end > line.content_end {
                self.emit_token(SyntaxKind::Newline, line.content_end..line.end);
            }
            let parent_indent = line.indent_end - line.start;
            let body_indent = if self.position < self.source.len() {
                let body = physical_line(&self.source[self.position..], self.position);
                body.indent_end - body.start
            } else {
                parent_indent
            };
            self.sink.enter(SyntaxKind::YmCommandBody);
            self.sink.enter(SyntaxKind::YmDoc);
            self.frames.push(YumarkFrame::IndentedBody {
                owner: FrameOwner::Command,
                parent_indent,
                body_indent,
            });
            if body_indent <= parent_indent {
                self.missing(RecoveryOwner::Command, RecoverySlot::Body, self.position);
                self.sink.exit();
                self.sink.exit();
                self.frames.pop();
                if capture {
                    self.sink.enter(SyntaxKind::YmDoCapture);
                    self.sink.enter(SyntaxKind::YmDoc);
                    self.frames.push(YumarkFrame::DoCapture {
                        command_start,
                        indent: parent_indent,
                    });
                    open.push(OpenBlock::DoCapture {
                        indent: parent_indent,
                    });
                } else {
                    self.sink.exit();
                }
                return;
            }
            open.push(OpenBlock::CommandBody {
                parent_indent,
                body_indent,
                capture,
                command_start,
            });
            return;
        }

        if self.position < line.content_end {
            self.emit_token(SyntaxKind::YmText, self.position..line.content_end);
        }
        if line.end > line.content_end {
            self.emit_token(SyntaxKind::Newline, line.content_end..line.end);
        }
        if promoted && capture {
            self.sink.enter(SyntaxKind::YmDoCapture);
            self.sink.enter(SyntaxKind::YmDoc);
            self.frames.push(YumarkFrame::DoCapture {
                command_start,
                indent: line.indent_end - line.start,
            });
            open.push(OpenBlock::DoCapture {
                indent: line.indent_end - line.start,
            });
        } else {
            self.sink.exit();
        }
    }

    fn parse_braced_command_body(
        &mut self,
        limit: usize,
        frame_owner: FrameOwner,
        recovery_owner: RecoveryOwner,
    ) -> bool {
        let parent_quote_depth = self.frames.nearest_prefix_quote_depth();
        let parent_layout_floor = self.frames.nearest_layout_floor();
        self.sink.enter(SyntaxKind::YmCommandBody);
        self.frames
            .push(YumarkFrame::BracedBody { owner: frame_owner });
        self.emit_token(SyntaxKind::LBrace, self.position..self.position + 1);
        self.sink.enter(SyntaxKind::YmDoc);
        let mut owners = vec![recovery_owner];
        while self.position < limit && !owners.is_empty() {
            match self.source.as_bytes()[self.position] {
                b'}' => {
                    self.sink.exit();
                    self.emit_token(SyntaxKind::RBrace, self.position..self.position + 1);
                    self.sink.exit();
                    self.frames.pop();
                    owners.pop();
                    if !owners.is_empty() {
                        self.sink.exit();
                    }
                }
                b'\\'
                    if self.source[self.position + 1..limit]
                        .chars()
                        .next()
                        .is_some_and(identifier_start) =>
                {
                    self.sink.enter(SyntaxKind::YmCommand);
                    self.emit_token(SyntaxKind::YmBackslash, self.position..self.position + 1);
                    let name_end = identifier_end(self.source, self.position, limit);
                    self.emit_token(SyntaxKind::Identifier, self.position..name_end);
                    while self.position < limit && self.source.as_bytes()[self.position] == b'(' {
                        self.parse_yulang_arguments(
                            SyntaxKind::YmYulangArgs,
                            RecoveryOwner::Command,
                            limit,
                        );
                    }
                    if self.position < limit && self.source.as_bytes()[self.position] == b'{' {
                        self.sink.enter(SyntaxKind::YmCommandBody);
                        self.frames.push(YumarkFrame::BracedBody {
                            owner: FrameOwner::Command,
                        });
                        self.emit_token(SyntaxKind::LBrace, self.position..self.position + 1);
                        self.sink.enter(SyntaxKind::YmDoc);
                        owners.push(RecoveryOwner::Command);
                    } else {
                        self.sink.exit();
                    }
                }
                b'\r' if self.source[self.position..limit].starts_with("\r\n") => {
                    self.emit_token(SyntaxKind::Newline, self.position..self.position + 2);
                    if self.braced_parent_boundary(limit, parent_quote_depth, parent_layout_floor) {
                        break;
                    }
                }
                b'\n' => {
                    self.emit_token(SyntaxKind::Newline, self.position..self.position + 1);
                    if self.braced_parent_boundary(limit, parent_quote_depth, parent_layout_floor) {
                        break;
                    }
                }
                _ => {
                    let start = self.position;
                    while self.position < limit
                        && !matches!(
                            self.source.as_bytes()[self.position],
                            b'\\' | b'}' | b'\r' | b'\n'
                        )
                    {
                        self.advance_to(self.position + 1);
                    }
                    self.sink.enter(SyntaxKind::YmParagraph);
                    self.sink.token(SyntaxKind::YmText, start..self.position);
                    self.sink.exit();
                }
            }
        }
        if !owners.is_empty() {
            for owner in owners.into_iter().rev() {
                self.missing(owner, RecoverySlot::ClosingDelimiter, self.position);
                self.sink.exit();
                self.sink.exit();
                self.frames.pop();
            }
            false
        } else {
            true
        }
    }

    fn braced_parent_boundary(
        &self,
        limit: usize,
        parent_quote_depth: Option<usize>,
        parent_layout_floor: Option<usize>,
    ) -> bool {
        if self.position >= limit {
            return false;
        }
        let line = physical_line(&self.source[self.position..limit], self.position);
        if line.indent_end == line.content_end {
            return false;
        }
        if self.stop_at_document_close
            && line.indent_end - line.start == self.document_base_col
            && matches!(
                judge_chunk(
                    &self.source[line.indent_end..],
                    line.indent_end,
                    ChunkContext {
                        at_line_start: true,
                        indent_col: self.document_base_col,
                        base_col: self.document_base_col,
                        active_close: Some(JudgeActiveClose::BlockDocument {
                            after_opening_line: true,
                        }),
                    },
                )
                .kind,
                ChunkKind::Terminator(super::judge::TerminatorKind::BlockDocument)
            )
        {
            return true;
        }
        let mut logical_start = line.indent_end;
        if let Some(required_depth) = parent_quote_depth {
            let Some((depth, marker_end, explicit)) = quote_facts(
                &self.source[line.indent_end..line.content_end],
                line.indent_end,
            ) else {
                return true;
            };
            if explicit || depth < required_depth {
                return true;
            }
            logical_start = marker_end;
        }
        if let Some(floor) = parent_layout_floor {
            let logical_indent = self.source[logical_start..line.content_end]
                .bytes()
                .take_while(|byte| matches!(byte, b' ' | b'\t'))
                .count();
            if logical_indent < floor {
                return true;
            }
        }
        false
    }

    fn finish_after_braced(&mut self, opener: PhysicalLine) {
        let line = if self.position <= opener.content_end {
            opener
        } else if self.position < self.source.len() {
            physical_line(&self.source[self.position..], self.position)
        } else {
            return;
        };
        if self.position < line.content_end {
            let range = self.position..line.content_end;
            let kind = if self.source[range.clone()]
                .bytes()
                .all(|byte| matches!(byte, b' ' | b'\t'))
            {
                SyntaxKind::Whitespace
            } else {
                SyntaxKind::YmText
            };
            self.emit_token(kind, range);
        }
        if line.end > line.content_end {
            self.emit_token(SyntaxKind::Newline, line.content_end..line.end);
        }
    }

    fn parse_embedded_pattern(
        &mut self,
        stops: crate::pattern::PatternStops,
        limit: usize,
    ) -> bool {
        let start = self.position;
        let mut remaining = &self.source[start..limit];
        let mut recover = Recover::new(self.operators);
        let (parsed, end) = {
            let mut output = EmbeddedOutput {
                sink: &mut *self.sink,
                position: start,
            };
            let exit = crate::pattern::pattern_normalized(
                SyntaxIn::new(&mut remaining, &mut recover, &mut output),
                start,
                LineEntry::InLine,
                None,
                stops,
                Some(AmbientClaimView::root_statement(0)).into(),
            );
            let mut pending = match exit {
                NormalizedExit::Complete(Err(Either::Left(item)), _)
                | NormalizedExit::Deferred(item, _) => Some(item),
                NormalizedExit::Complete(Err(Either::Right(end)), _) => Some(end.item),
                NormalizedExit::Complete(Ok(()), _) => None,
            };
            if let Some(item) = pending.as_mut() {
                item.emit_all_remaining_leading(&mut output);
            }
            (output.position > start, output.position)
        };
        self.settle_embedded_to(end);
        parsed
    }

    fn parse_embedded_use_tree(
        &mut self,
        stops: u16,
        outer_close: Option<char>,
        limit: usize,
    ) -> bool {
        let start = self.position;
        let mut remaining = &self.source[start..limit];
        let mut recover = Recover::new(self.operators);
        let (parsed, end) = {
            let mut output = EmbeddedOutput {
                sink: &mut *self.sink,
                position: start,
            };
            let exit = crate::declaration::use_decl::yumark_use_tree_normalized(
                SyntaxIn::new(&mut remaining, &mut recover, &mut output),
                0,
                stops,
                start,
                LineEntry::InLine,
                outer_close,
            );
            let parsed = exit.is_some();
            if let Some(exit) = exit {
                let mut pending = match exit {
                    NormalizedExit::Complete(Err(Either::Left(item)), _)
                    | NormalizedExit::Deferred(item, _) => Some(item),
                    NormalizedExit::Complete(Err(Either::Right(end)), _) => Some(end.item),
                    NormalizedExit::Complete(Ok(()), _) => None,
                };
                if let Some(item) = pending.as_mut() {
                    item.emit_all_remaining_leading(&mut output);
                }
            }
            (parsed, output.position)
        };
        self.settle_embedded_to(end);
        parsed
    }

    fn parse_my_tail(
        &mut self,
        open: &mut Vec<OpenBlock>,
        line: PhysicalLine,
        command_start: usize,
    ) {
        self.sink.enter(SyntaxKind::YmMyBindingHead);
        let gap = self.horizontal_end(line.content_end);
        self.emit_horizontal_to(gap);
        let mut parenthesized = false;
        if self.position < line.content_end && self.source.as_bytes()[self.position] == b'(' {
            parenthesized = true;
            self.emit_token(SyntaxKind::LParen, self.position..self.position + 1);
        }
        self.frames.push(YumarkFrame::EmbeddedYulang {
            owner: FrameOwner::My,
            outer_kind: if parenthesized {
                super::frame::EmbeddedOuterKind::Parenthesis
            } else {
                super::frame::EmbeddedOuterKind::MyHeadBoundary
            },
            delimiter_floor: super::frame::DelimiterFloor(self.frames.len()),
        });
        let pattern_stops = crate::pattern::PATTERN_STOP_EQUALS
            | crate::pattern::PATTERN_STOP_COLON
            | crate::pattern::PATTERN_STOP_LBRACE
            | if parenthesized {
                crate::pattern::PATTERN_STOP_RPAREN | crate::pattern::PATTERN_STOP_COMMA
            } else {
                0
            };
        let mut any_head = false;
        loop {
            let gap = self.horizontal_end(line.content_end);
            self.emit_horizontal_to(gap);
            if self.position >= line.content_end {
                break;
            }
            let byte = self.source.as_bytes()[self.position];
            if matches!(byte, b'=' | b':' | b'{') || parenthesized && byte == b')' {
                break;
            }
            if parenthesized && byte == b',' {
                self.emit_token(SyntaxKind::Comma, self.position..self.position + 1);
                continue;
            }
            let before = self.position;
            if !self.parse_embedded_pattern(pattern_stops, line.content_end)
                || self.position == before
            {
                break;
            }
            any_head = true;
        }
        if !any_head {
            self.missing(RecoveryOwner::My, RecoverySlot::Head, self.position);
        }
        if parenthesized {
            if self.position < line.content_end && self.source.as_bytes()[self.position] == b')' {
                self.emit_token(SyntaxKind::RParen, self.position..self.position + 1);
            } else {
                self.missing(
                    RecoveryOwner::My,
                    RecoverySlot::ClosingDelimiter,
                    self.position,
                );
            }
        }
        self.sink.exit();
        self.frames.pop();
        let gap = self.horizontal_end(line.content_end);
        self.emit_horizontal_to(gap);

        if self.position < line.content_end && self.source.as_bytes()[self.position] == b'=' {
            self.sink.enter(SyntaxKind::YmMyExpressionBody);
            self.emit_token(SyntaxKind::Equals, self.position..self.position + 1);
            let gap = self.horizontal_end(line.content_end);
            self.emit_horizontal_to(gap);
            if self.position >= line.content_end {
                if line.end > line.content_end {
                    self.emit_token(SyntaxKind::Newline, line.content_end..line.end);
                }
                if self.position < self.source.len() {
                    let body = physical_line(&self.source[self.position..], self.position);
                    if body.indent_end > body.start + (line.indent_end - line.start) {
                        self.parse_embedded_expression(
                            STOP_LINE_BREAK | STOP_SEMICOLON,
                            body.content_end,
                        );
                        self.finish_line(body);
                    } else {
                        self.missing(
                            RecoveryOwner::My,
                            RecoverySlot::ExpressionBody,
                            self.position,
                        );
                    }
                } else {
                    self.missing(
                        RecoveryOwner::My,
                        RecoverySlot::ExpressionBody,
                        self.position,
                    );
                }
            } else {
                self.frames.push(YumarkFrame::EmbeddedYulang {
                    owner: FrameOwner::My,
                    outer_kind: super::frame::EmbeddedOuterKind::RequiredSemicolon,
                    delimiter_floor: super::frame::DelimiterFloor(self.frames.len()),
                });
                let before = self.position;
                if !self
                    .parse_embedded_expression(STOP_LINE_BREAK | STOP_SEMICOLON, line.content_end)
                    || self.position == before
                {
                    self.missing(
                        RecoveryOwner::My,
                        RecoverySlot::ExpressionBody,
                        self.position,
                    );
                }
                if self.position < line.content_end && self.source.as_bytes()[self.position] == b';'
                {
                    self.emit_token(SyntaxKind::Semicolon, self.position..self.position + 1);
                } else {
                    self.missing(RecoveryOwner::My, RecoverySlot::Terminator, self.position);
                }
                self.emit_horizontal_to(line.content_end);
                if line.end > line.content_end {
                    self.emit_token(SyntaxKind::Newline, line.content_end..line.end);
                }
                self.frames.pop();
            }
            self.sink.exit();
            self.sink.exit();
            return;
        }
        if self.position < line.content_end && self.source.as_bytes()[self.position] == b'{' {
            let closed = self.parse_braced_command_body(
                self.source.len(),
                FrameOwner::My,
                RecoveryOwner::My,
            );
            if closed {
                self.finish_after_braced(line);
            }
            self.sink.exit();
            return;
        }
        if self.strict_colon_body(line) {
            self.emit_token(SyntaxKind::Colon, self.position..self.position + 1);
            self.emit_horizontal_to(line.content_end);
            if line.end > line.content_end {
                self.emit_token(SyntaxKind::Newline, line.content_end..line.end);
            }
            let parent_indent = line.indent_end - line.start;
            let body_indent = if self.position < self.source.len() {
                let body = physical_line(&self.source[self.position..], self.position);
                body.indent_end - body.start
            } else {
                parent_indent
            };
            self.sink.enter(SyntaxKind::YmCommandBody);
            self.sink.enter(SyntaxKind::YmDoc);
            self.frames.push(YumarkFrame::IndentedBody {
                owner: FrameOwner::My,
                parent_indent,
                body_indent,
            });
            if body_indent <= parent_indent {
                self.missing(RecoveryOwner::My, RecoverySlot::Body, self.position);
                self.sink.exit();
                self.sink.exit();
                self.frames.pop();
                self.sink.exit();
                return;
            }
            open.push(OpenBlock::CommandBody {
                parent_indent,
                body_indent,
                capture: false,
                command_start,
            });
            return;
        }
        self.missing(
            RecoveryOwner::My,
            RecoverySlot::BodyIntroducer,
            self.position,
        );
        self.emit_horizontal_to(line.content_end);
        if line.end > line.content_end {
            self.emit_token(SyntaxKind::Newline, line.content_end..line.end);
        }
        self.sink.exit();
    }

    fn parse_use_tail(&mut self, line: PhysicalLine) {
        let gap = self.horizontal_end(line.content_end);
        let had_gap = gap > self.position;
        self.emit_horizontal_to(gap);
        if self.position < line.content_end && self.source.as_bytes()[self.position] == b'(' {
            self.frames.push(YumarkFrame::EmbeddedYulang {
                owner: FrameOwner::Use,
                outer_kind: super::frame::EmbeddedOuterKind::Parenthesis,
                delimiter_floor: super::frame::DelimiterFloor(self.frames.len()),
            });
            self.emit_token(SyntaxKind::LParen, self.position..self.position + 1);
            let parsed = self.parse_embedded_use_tree(
                stops_for(TokenKind::RParen) | STOP_LINE_BREAK,
                Some(')'),
                line.content_end,
            );
            if !parsed {
                self.missing(RecoveryOwner::Use, RecoverySlot::Route, self.position);
            }
            if self.position < line.content_end && self.source.as_bytes()[self.position] == b')' {
                self.emit_token(SyntaxKind::RParen, self.position..self.position + 1);
            } else {
                self.missing(
                    RecoveryOwner::Use,
                    RecoverySlot::ClosingDelimiter,
                    self.position,
                );
            }
            self.frames.pop();
        } else if had_gap {
            self.frames.push(YumarkFrame::EmbeddedYulang {
                owner: FrameOwner::Use,
                outer_kind: super::frame::EmbeddedOuterKind::RequiredSemicolon,
                delimiter_floor: super::frame::DelimiterFloor(self.frames.len()),
            });
            let parsed = self.parse_embedded_use_tree(
                STOP_SEMICOLON | STOP_LINE_BREAK,
                None,
                line.content_end,
            );
            if !parsed {
                self.missing(RecoveryOwner::Use, RecoverySlot::Route, self.position);
            }
            if self.position < line.content_end && self.source.as_bytes()[self.position] == b';' {
                self.emit_token(SyntaxKind::Semicolon, self.position..self.position + 1);
            } else if parsed {
                self.missing(RecoveryOwner::Use, RecoverySlot::Terminator, self.position);
            }
            self.frames.pop();
        } else {
            self.missing(RecoveryOwner::Use, RecoverySlot::Route, self.position);
        }
        self.emit_horizontal_to(line.content_end);
    }

    fn parse_if_chain_line(
        &mut self,
        first: &str,
        mut line: PhysicalLine,
        chain_checkpoint: &S::Checkpoint,
    ) {
        let chain_indent = line.indent_end - line.start;
        self.frames.push(YumarkFrame::IfChain {
            indent: chain_indent,
            seen_else: first == "else",
        });
        let mut branch = first;
        let mut first_branch = true;
        loop {
            let owner = match branch {
                "if" => RecoveryOwner::IfBranch,
                "elsif" => RecoveryOwner::ElsifBranch,
                _ => RecoveryOwner::ElseBranch,
            };
            if first_branch && branch != "if" {
                self.sink.recovery_at(
                    chain_checkpoint,
                    Recovery {
                        kind: SyntaxKind::Error,
                        owner: RecoveryOwner::IfChain,
                        slot: RecoverySlot::BranchPredecessor,
                    },
                    line.indent_end..self.position,
                );
            }
            self.sink.enter(match branch {
                "if" => SyntaxKind::YmIf,
                "elsif" => SyntaxKind::YmElsif,
                _ => SyntaxKind::YmElse,
            });
            if branch == "else" {
                self.frames.replace_last(YumarkFrame::IfChain {
                    indent: chain_indent,
                    seen_else: true,
                });
            }
            let gap = self.horizontal_end(line.content_end);
            self.emit_horizontal_to(gap);
            if branch != "else" {
                self.sink.enter(if branch == "if" {
                    SyntaxKind::YmIfCondition
                } else {
                    SyntaxKind::YmElsifCondition
                });
                if self.position < line.content_end && self.source.as_bytes()[self.position] == b'('
                {
                    self.parse_parenthesized_condition(owner, line.content_end);
                } else {
                    self.missing(owner, RecoverySlot::Condition, self.position);
                }
                self.sink.exit();
            } else if self.position < line.content_end
                && self.source.as_bytes()[self.position] == b'('
            {
                let start = self.position;
                let recovery_checkpoint = self.sink.checkpoint();
                self.parse_parenthesized_yulang(RecoveryOwner::ElseBranch, line.content_end);
                self.sink.recovery_at(
                    &recovery_checkpoint,
                    Recovery {
                        kind: SyntaxKind::Error,
                        owner: RecoveryOwner::ElseBranch,
                        slot: RecoverySlot::Condition,
                    },
                    start..self.position,
                );
            }
            let gap = self.horizontal_end(line.content_end);
            self.emit_horizontal_to(gap);
            if self.position < line.content_end && self.source.as_bytes()[self.position] == b'{' {
                let closed = self.parse_braced_command_body(
                    self.source.len(),
                    match owner {
                        RecoveryOwner::IfBranch => FrameOwner::IfBranch,
                        RecoveryOwner::ElsifBranch => FrameOwner::ElsifBranch,
                        _ => FrameOwner::ElseBranch,
                    },
                    owner,
                );
                if closed {
                    self.finish_after_braced(line);
                }
            } else if self.strict_colon_body(line) {
                self.emit_token(SyntaxKind::Colon, self.position..self.position + 1);
                self.emit_horizontal_to(line.content_end);
                if line.end > line.content_end {
                    self.emit_token(SyntaxKind::Newline, line.content_end..line.end);
                }
                self.sink.enter(SyntaxKind::YmCommandBody);
                self.sink.enter(SyntaxKind::YmDoc);
                let mut saw_body = false;
                while self.position < self.source.len() {
                    let body = physical_line(&self.source[self.position..], self.position);
                    if body.indent_end == body.content_end {
                        break;
                    }
                    if body.indent_end - body.start <= chain_indent {
                        break;
                    }
                    if body.indent_end > body.start {
                        self.emit_token(SyntaxKind::Whitespace, body.start..body.indent_end);
                    }
                    saw_body = true;
                    self.parse_paragraph(PhysicalLine {
                        start: self.position,
                        indent_end: self.position,
                        content_end: body.content_end,
                        end: body.end,
                    });
                }
                if !saw_body {
                    self.missing(owner, RecoverySlot::Body, self.position);
                }
                self.sink.exit();
                self.sink.exit();
            } else {
                self.missing(owner, RecoverySlot::BodyIntroducer, self.position);
                if self.position < line.content_end {
                    let start = self.position;
                    self.advance_to(line.content_end);
                    self.sink.recovery(
                        Recovery {
                            kind: SyntaxKind::Error,
                            owner,
                            slot: RecoverySlot::BodyIntroducer,
                        },
                        start..self.position,
                    );
                }
                self.finish_line(line);
            }
            self.sink.exit();

            while self.position < self.source.len() {
                let blank = physical_line(&self.source[self.position..], self.position);
                if blank.indent_end != blank.content_end {
                    break;
                }
                self.sink.enter(SyntaxKind::YmBlankLine);
                self.finish_line(blank);
                self.sink.exit();
            }
            if self.position >= self.source.len() {
                break;
            }
            let next = physical_line(&self.source[self.position..], self.position);
            if next.indent_end - next.start != chain_indent {
                break;
            }
            let content = &self.source[next.indent_end..next.content_end];
            let next_branch = if content.starts_with("\\elsif")
                && content[6..]
                    .chars()
                    .next()
                    .is_none_or(|character| !is_xid_continue(character))
            {
                "elsif"
            } else if content.starts_with("\\else")
                && content[5..]
                    .chars()
                    .next()
                    .is_none_or(|character| !is_xid_continue(character))
            {
                "else"
            } else {
                break;
            };
            if branch == "else" {
                break;
            }
            if self.position < next.indent_end {
                self.emit_token(SyntaxKind::Whitespace, next.start..next.indent_end);
            }
            self.emit_token(SyntaxKind::YmBackslash, self.position..self.position + 1);
            let end = self.position + next_branch.len();
            self.emit_token(SyntaxKind::Identifier, self.position..end);
            line = next;
            branch = next_branch;
            first_branch = false;
        }
        self.frames.pop();
    }

    fn parse_fence(&mut self, opener: PhysicalLine) {
        let marker = opener.indent_end..opener.indent_end + 3;
        let boundary = FenceBoundary {
            opener: FenceOpener {
                line: opener.start,
                marker: marker.clone(),
                marker_width: 3,
            },
            prefix_policy: FencePrefixPolicy::None,
            close_column: opener.indent_end - opener.start,
        };
        self.sink.enter(SyntaxKind::YmCodeFence);
        self.frames.push(YumarkFrame::RawFence {
            marker: marker.clone(),
            indent: opener.indent_end - opener.start,
        });
        self.emit_token(SyntaxKind::YmFenceMarker, marker);
        let info = opener.indent_end + 3..opener.content_end;
        self.sink.enter(SyntaxKind::YmCodeFenceInfo);
        if !info.is_empty() {
            self.emit_token(SyntaxKind::YmText, info.clone());
        }
        self.sink.exit();
        if opener.end > opener.content_end {
            self.emit_token(SyntaxKind::Newline, opener.content_end..opener.end);
        }

        let selected_yulang = is_yulang_fence_info(&self.source[info]);
        let body_start = self.position;
        let mut close = None;
        while self.position < self.source.len() {
            match judge_fence_line(&self.source[self.position..], self.position, &boundary) {
                FenceLineDecision::Body { .. } => {
                    let line = physical_line(&self.source[self.position..], self.position);
                    self.advance_to(line.end);
                }
                FenceLineDecision::Boundary(pending) => match pending.kind() {
                    Boundary::BorrowedClose(BorrowedTarget::YumarkFence(facts)) => {
                        close = Some((**facts).clone());
                        break;
                    }
                    Boundary::EofAfterTrivia => break,
                    _ => unreachable!("unquoted fence judge has no quote transition"),
                },
            }
        }
        let body_end = self.position;
        if !selected_yulang && body_end > body_start {
            self.sink
                .token(SyntaxKind::YmCodeFenceText, body_start..body_end);
        }
        if let Some(close) = close {
            if self.position < close.marker.start {
                self.emit_token(SyntaxKind::Whitespace, self.position..close.marker.start);
            }
            self.emit_token(SyntaxKind::YmFenceMarker, close.marker);
            self.sink.exit();
            self.frames.pop();
            if self.position < close.horizontal_suffix.end {
                self.emit_token(
                    SyntaxKind::Whitespace,
                    self.position..close.horizontal_suffix.end,
                );
            }
            if let Some(newline) = close.newline {
                self.emit_token(SyntaxKind::Newline, newline);
            }
            return;
        } else {
            self.missing(
                RecoveryOwner::CodeFence,
                RecoverySlot::ClosingDelimiter,
                self.position,
            );
        }
        self.sink.exit();
        self.frames.pop();
    }

    fn parse_prefixed_fence(&mut self, opener: PhysicalLine, quote_depth: usize) {
        let marker = opener.indent_end..opener.indent_end + 3;
        let boundary = FenceBoundary {
            opener: FenceOpener {
                line: opener.start,
                marker: marker.clone(),
                marker_width: 3,
            },
            prefix_policy: FencePrefixPolicy::ActivePrefixQuote {
                depth: quote_depth,
                base: 0,
            },
            close_column: opener.indent_end - opener.start,
        };
        self.sink.enter(SyntaxKind::YmCodeFence);
        self.frames.push(YumarkFrame::RawFence {
            marker: marker.clone(),
            indent: boundary.close_column,
        });
        self.emit_token(SyntaxKind::YmFenceMarker, marker);
        let info = opener.indent_end + 3..opener.content_end;
        self.sink.enter(SyntaxKind::YmCodeFenceInfo);
        if !info.is_empty() {
            self.emit_token(SyntaxKind::YmText, info.clone());
        }
        self.sink.exit();
        if opener.end > opener.content_end {
            self.emit_token(SyntaxKind::Newline, opener.content_end..opener.end);
        }

        let selected = is_yulang_fence_info(&self.source[info]);
        let body_start = self.position;
        let mut close = None;
        let mut transition = false;
        while self.position < self.source.len() {
            match judge_fence_line(&self.source[self.position..], self.position, &boundary) {
                FenceLineDecision::Body { .. } => {
                    let line = physical_line(&self.source[self.position..], self.position);
                    self.advance_to(line.end);
                }
                FenceLineDecision::Boundary(pending) => match pending.kind() {
                    Boundary::BorrowedClose(BorrowedTarget::YumarkFence(facts)) => {
                        close = Some((**facts).clone());
                        break;
                    }
                    Boundary::Stop(StopKind::YumarkFence(_)) => {
                        transition = true;
                        break;
                    }
                    Boundary::EofAfterTrivia => break,
                    Boundary::Close(_)
                    | Boundary::BorrowedClose(BorrowedTarget::Delimiter(_))
                    | Boundary::Dedent(_)
                    | Boundary::Stop(
                        StopKind::Newline | StopKind::RightParenthesis | StopKind::RightBrace,
                    ) => unreachable!("fence judge returns only fence boundaries"),
                },
            }
        }
        if !selected && self.position > body_start {
            self.sink
                .token(SyntaxKind::YmCodeFenceText, body_start..self.position);
        }
        if let Some(close) = close {
            if let Some(prefix) = close.prefix {
                self.emit_token(SyntaxKind::YmQuotePrefix, prefix.extent);
            }
            if self.position < close.marker.start {
                self.emit_token(SyntaxKind::Whitespace, self.position..close.marker.start);
            }
            self.emit_token(SyntaxKind::YmFenceMarker, close.marker);
            self.sink.exit();
            self.frames.pop();
            if self.position < close.horizontal_suffix.end {
                self.emit_token(
                    SyntaxKind::Whitespace,
                    self.position..close.horizontal_suffix.end,
                );
            }
            if let Some(newline) = close.newline {
                self.emit_token(SyntaxKind::Newline, newline);
            }
        } else {
            let at = self.position;
            self.missing(RecoveryOwner::CodeFence, RecoverySlot::ClosingDelimiter, at);
            self.sink.exit();
            self.frames.pop();
            if transition {
                // The transition line is deliberately untouched for the quote
                // owner to settle on the next block-loop iteration.
            }
        }
    }

    fn paragraph_last_line(&self, first: PhysicalLine) -> PhysicalLine {
        let mut line = first;
        let list_content_column = match self.frames.last() {
            Some(YumarkFrame::ListItem { content_column, .. }) => Some(*content_column),
            _ => None,
        };
        let indented_body_column = match self.frames.last() {
            Some(YumarkFrame::IndentedBody { body_indent, .. }) => Some(*body_indent),
            _ => None,
        };
        let prefixed = matches!(self.frames.last(), Some(YumarkFrame::PrefixQuote { .. }));
        loop {
            if line.end == line.content_end {
                break;
            }
            let next_position = line.end;
            let next = (next_position < self.source.len())
                .then(|| physical_line(&self.source[next_position..], next_position));
            let continues = next.is_some_and(|next| {
                if self.stop_at_document_close
                    && next.indent_end - next.start == self.document_base_col
                    && matches!(
                        judge_chunk(
                            &self.source[next.indent_end..],
                            next.indent_end,
                            ChunkContext {
                                at_line_start: true,
                                indent_col: self.document_base_col,
                                base_col: self.document_base_col,
                                active_close: Some(JudgeActiveClose::BlockDocument {
                                    after_opening_line: true,
                                }),
                            },
                        )
                        .kind,
                        ChunkKind::Terminator(super::judge::TerminatorKind::BlockDocument)
                    )
                {
                    return false;
                }
                if next.indent_end == next.content_end {
                    return false;
                }
                if prefixed
                    || list_content_column
                        .is_some_and(|column| next.indent_end - next.start < column)
                    || indented_body_column
                        .is_some_and(|column| next.indent_end - next.start < column)
                {
                    return false;
                }
                let content = &self.source[next.indent_end..next.content_end];
                heading_facts(content, next.indent_end).is_none()
                    && list_marker_end(content, next.indent_end).is_none()
                    && !raw_fence_opener(&self.source[next.indent_end..], next.indent_end)
                    && quote_facts(content, next.indent_end).is_none()
                    && !content.starts_with('\\')
            });
            if !continues {
                break;
            }
            line = next.expect("paragraph continuation was checked");
        }
        line
    }

    fn parse_paragraph(&mut self, first: PhysicalLine) {
        self.sink.enter(SyntaxKind::YmParagraph);
        let line = self.paragraph_last_line(first);
        // One inline driver owns the complete paragraph range, so groups may
        // cross an owned physical newline without closing/reopening or rescans.
        self.parse_inline_until(line.content_end);
        self.sink.exit();
        if line.end > line.content_end {
            self.emit_token(SyntaxKind::Newline, line.content_end..line.end);
        }
    }

    fn parse_inline_until(&mut self, limit: usize) {
        self.parse_inline_owned_until(limit, None);
    }

    fn parse_inline_owned_until(&mut self, limit: usize, outer_close: Option<u8>) {
        let mut inline: Vec<InlineFrame<S::Checkpoint>> = Vec::new();
        while self.position < limit {
            if inline.is_empty()
                && outer_close.is_some_and(|close| self.source.as_bytes()[self.position] == close)
            {
                break;
            }
            let rest = &self.source[self.position..limit];
            let active_close = inline
                .last()
                .map(|frame| {
                    JudgeActiveClose::Inline(match frame.close {
                        InlineClose::RightBracket => JudgeInlineClose::RightBracket,
                        InlineClose::Emphasis => JudgeInlineClose::Emphasis,
                        InlineClose::Strong => JudgeInlineClose::Strong,
                    })
                })
                .or_else(|| {
                    outer_close.map(|_| JudgeActiveClose::Inline(JudgeInlineClose::RightBracket))
                });
            let chunk = judge_chunk(
                rest,
                self.position,
                ChunkContext {
                    // Inline documents never enable block NUDs, including
                    // after an owned group newline or in LineDocMode.
                    at_line_start: false,
                    indent_col: self.column,
                    base_col: 0,
                    active_close,
                },
            );
            if chunk.kind == ChunkKind::Newline && rest.starts_with("\r\n") {
                let start = self.position;
                self.emit_token(SyntaxKind::Newline, start..start + 2);
                continue;
            }
            if chunk.kind == ChunkKind::Newline && rest.starts_with('\n') {
                let start = self.position;
                self.emit_token(SyntaxKind::Newline, start..start + 1);
                continue;
            }
            if let Some(frame) = inline.last()
                && close_spelling(frame.close).is_some_and(|close| rest.starts_with(close))
            {
                let frame = inline.pop().expect("active inline frame");
                self.sink.exit();
                let length = close_spelling(frame.close).expect("framed close").len();
                let close_start = self.position;
                self.emit_token(close_token(frame.close), close_start..close_start + length);
                if frame.close == InlineClose::RightBracket {
                    self.finish_group_tail(&frame, limit);
                } else {
                    self.sink.exit();
                }
                self.frames.pop();
                continue;
            }
            if chunk.kind == ChunkKind::Image {
                let checkpoint = self.sink.checkpoint();
                self.sink.enter(SyntaxKind::YmInlineImage);
                self.emit_token(SyntaxKind::YmBangLBracket, self.position..self.position + 2);
                self.sink.enter(SyntaxKind::YmDoc);
                self.frames.push(YumarkFrame::Inline {
                    owner: FrameOwner::InlineImage,
                    close: InlineClose::RightBracket,
                });
                inline.push(InlineFrame {
                    close: InlineClose::RightBracket,
                    owner: RecoveryOwner::InlineImage,
                    checkpoint,
                    node: SyntaxKind::YmInlineImage,
                });
                continue;
            }
            if chunk.kind == ChunkKind::Strong {
                self.open_inline(
                    &mut inline,
                    SyntaxKind::YmStrong,
                    SyntaxKind::YmStrongMarker,
                    InlineClose::Strong,
                    RecoveryOwner::Strong,
                    2,
                    FrameOwner::Strong,
                );
                continue;
            }
            if chunk.kind == ChunkKind::InlineGroup {
                let checkpoint = self.sink.checkpoint();
                self.emit_token(SyntaxKind::LBracket, self.position..self.position + 1);
                self.sink.enter(SyntaxKind::YmDoc);
                self.frames.push(YumarkFrame::Inline {
                    owner: FrameOwner::InlineGroup,
                    close: InlineClose::RightBracket,
                });
                inline.push(InlineFrame {
                    close: InlineClose::RightBracket,
                    owner: RecoveryOwner::InlineGroup,
                    checkpoint,
                    node: SyntaxKind::YmInlineGroup,
                });
                continue;
            }
            if chunk.kind == ChunkKind::Emphasis {
                self.open_inline(
                    &mut inline,
                    SyntaxKind::YmEmphasis,
                    SyntaxKind::YmEmphasisMarker,
                    InlineClose::Emphasis,
                    RecoveryOwner::Emphasis,
                    1,
                    FrameOwner::Emphasis,
                );
                continue;
            }
            if chunk.kind == ChunkKind::Backslash {
                self.parse_inline_reference(limit);
                continue;
            }
            debug_assert_eq!(chunk.kind, ChunkKind::RawText);
            let end = chunk.range.end;
            self.emit_token(SyntaxKind::YmText, self.position..end);
        }
        while let Some(frame) = inline.pop() {
            self.missing(frame.owner, RecoverySlot::ClosingDelimiter, self.position);
            self.sink.exit();
            if frame.node == SyntaxKind::YmInlineGroup {
                self.sink
                    .start_enter_at(&frame.checkpoint, SyntaxKind::YmInlineGroup);
            }
            self.sink.exit();
            self.frames.pop();
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn open_inline(
        &mut self,
        inline: &mut Vec<InlineFrame<S::Checkpoint>>,
        node: SyntaxKind,
        marker: SyntaxKind,
        close: InlineClose,
        owner: RecoveryOwner,
        length: usize,
        frame_owner: FrameOwner,
    ) {
        let checkpoint = self.sink.checkpoint();
        self.sink.enter(node);
        self.emit_token(marker, self.position..self.position + length);
        self.sink.enter(SyntaxKind::YmDoc);
        self.frames.push(YumarkFrame::Inline {
            owner: frame_owner,
            close,
        });
        inline.push(InlineFrame {
            close,
            owner,
            checkpoint,
            node,
        });
    }

    fn finish_group_tail(&mut self, frame: &InlineFrame<S::Checkpoint>, limit: usize) {
        if self.position < limit && self.source.as_bytes()[self.position] == b'(' {
            let owner = if frame.node == SyntaxKind::YmInlineImage {
                RecoveryOwner::InlineImage
            } else {
                self.sink
                    .start_enter_at(&frame.checkpoint, SyntaxKind::YmInlineLink);
                RecoveryOwner::InlineLink
            };
            self.parse_raw_destination(owner, limit);
            self.sink.exit();
        } else if frame.node == SyntaxKind::YmInlineImage {
            self.missing(
                RecoveryOwner::InlineImage,
                RecoverySlot::Destination,
                self.position,
            );
            self.sink.exit();
        } else if self.position < limit && self.source.as_bytes()[self.position] == b':' {
            self.sink
                .start_enter_at(&frame.checkpoint, SyntaxKind::YmInlineApply);
            let colon = self.position;
            self.emit_token(SyntaxKind::Colon, colon..colon + 1);
            self.sink.enter(SyntaxKind::YmInlineApplyHead);
            let name_start = self.position;
            let name_end = identifier_end(self.source, name_start, limit);
            if name_end == name_start {
                self.missing(RecoveryOwner::InlineApply, RecoverySlot::Name, name_start);
            } else {
                self.emit_token(SyntaxKind::Identifier, name_start..name_end);
            }
            self.sink.exit();
            if self.position < limit && self.source.as_bytes()[self.position] == b'(' {
                self.parse_yulang_arguments(
                    SyntaxKind::YmInlineApplyArgs,
                    RecoveryOwner::InlineApply,
                    limit,
                );
            }
            self.sink.exit();
        } else {
            self.sink
                .start_enter_at(&frame.checkpoint, SyntaxKind::YmInlineGroup);
            self.sink.exit();
        }
    }

    fn parse_raw_destination(&mut self, owner: RecoveryOwner, limit: usize) {
        let open = self.position;
        self.emit_token(SyntaxKind::LParen, open..open + 1);
        let rest = &self.source[self.position..limit];
        if let Some(offset) = rest.find(')') {
            let end = self.position + offset;
            if end > self.position {
                self.emit_token(SyntaxKind::YmText, self.position..end);
            }
            self.emit_token(SyntaxKind::RParen, end..end + 1);
        } else {
            if self.position < limit {
                self.emit_token(SyntaxKind::YmText, self.position..limit);
            }
            self.missing(owner, RecoverySlot::ClosingDelimiter, self.position);
        }
    }

    fn parse_inline_reference(&mut self, limit: usize) {
        self.sink.enter(SyntaxKind::YmInlineRef);
        let slash = self.position;
        self.emit_token(SyntaxKind::YmBackslash, slash..slash + 1);
        let name_start = self.position;
        let name_end = identifier_end(self.source, name_start, limit);
        self.emit_token(SyntaxKind::Identifier, name_start..name_end);
        if self.position < limit && self.source.as_bytes()[self.position] == b'(' {
            self.parse_yulang_arguments(
                SyntaxKind::YmYulangArgs,
                RecoveryOwner::InlineReference,
                limit,
            );
        }
        if self.position < limit && self.source.as_bytes()[self.position] == b';' {
            let semi = self.position;
            self.emit_token(SyntaxKind::Semicolon, semi..semi + 1);
        }
        self.sink.exit();
    }

    fn finish_line(&mut self, line: PhysicalLine) {
        if self.position < line.content_end {
            self.advance_to(line.content_end);
        }
        if line.end > line.content_end {
            self.emit_token(SyntaxKind::Newline, line.content_end..line.end);
        }
    }

    fn missing(&mut self, owner: RecoveryOwner, slot: RecoverySlot, position: usize) {
        self.sink.recovery(
            Recovery {
                kind: SyntaxKind::Missing,
                owner,
                slot,
            },
            position..position,
        );
    }
}

fn heading_facts(source: &str, origin: usize) -> Option<(usize, usize, bool)> {
    let chunk = judge_chunk(
        source,
        origin,
        ChunkContext {
            at_line_start: true,
            indent_col: origin,
            base_col: origin,
            active_close: None,
        },
    );
    match chunk.kind {
        ChunkKind::Heading { level } => Some((level, chunk.range.end, false)),
        ChunkKind::SectionClose { level } => Some((level, chunk.range.end, true)),
        _ => None,
    }
}

fn terminal_colon(source: &str, start: usize, end: usize) -> (usize, bool) {
    let trimmed = source[start..end].trim_end_matches([' ', '\t']);
    if trimmed.ends_with(':') {
        (start + trimmed.len() - 1, true)
    } else {
        (end, false)
    }
}

fn list_marker_end(source: &str, origin: usize) -> Option<usize> {
    let chunk = judge_chunk(
        source,
        origin,
        ChunkContext {
            at_line_start: true,
            indent_col: origin,
            base_col: origin,
            active_close: None,
        },
    );
    matches!(
        chunk.kind,
        ChunkKind::OrderedList | ChunkKind::UnorderedList
    )
    .then_some(chunk.range.end - 1)
}

fn quote_facts(source: &str, origin: usize) -> Option<(usize, usize, bool)> {
    let chunk = judge_chunk(
        source,
        origin,
        ChunkContext {
            at_line_start: true,
            indent_col: origin,
            base_col: origin,
            active_close: None,
        },
    );
    match chunk.kind {
        ChunkKind::ExplicitQuote { depth } => Some((depth, chunk.range.end, true)),
        ChunkKind::PrefixQuote { depth } => Some((depth, chunk.range.end, false)),
        _ => None,
    }
}

fn raw_fence_opener(source: &str, origin: usize) -> bool {
    judge_chunk(
        source,
        origin,
        ChunkContext {
            at_line_start: true,
            indent_col: origin,
            base_col: origin,
            active_close: None,
        },
    )
    .kind
        == ChunkKind::RawFence
}

fn close_spelling(close: InlineClose) -> Option<&'static str> {
    Some(match close {
        InlineClose::RightBracket => "]",
        InlineClose::Emphasis => "*",
        InlineClose::Strong => "**",
    })
}

fn close_token(close: InlineClose) -> SyntaxKind {
    match close {
        InlineClose::RightBracket => SyntaxKind::RBracket,
        InlineClose::Emphasis => SyntaxKind::YmEmphasisMarker,
        InlineClose::Strong => SyntaxKind::YmStrongMarker,
    }
}

fn identifier_start(character: char) -> bool {
    character == '_' || is_xid_start(character)
}

fn identifier_end(source: &str, start: usize, limit: usize) -> usize {
    let mut end = start;
    for (offset, character) in source[start..limit].char_indices() {
        if offset == 0 {
            if !identifier_start(character) {
                break;
            }
        } else if character != '_' && !is_xid_continue(character) {
            break;
        }
        end = start + offset + character.len_utf8();
    }
    end
}

mod tests {
    use super::*;

    #[derive(Clone, Debug, Eq, PartialEq)]
    enum Event {
        Enter(SyntaxKind),
        Token(SyntaxKind, Range<usize>),
        Exit,
        Recovery(Recovery, Range<usize>),
    }

    #[derive(Default)]
    struct RecordingSink {
        events: Vec<Event>,
    }

    impl Sink for RecordingSink {
        type Checkpoint = usize;

        fn checkpoint(&mut self) -> Self::Checkpoint {
            self.events.len()
        }
        fn enter(&mut self, kind: SyntaxKind) {
            self.events.push(Event::Enter(kind));
        }
        fn token(&mut self, kind: SyntaxKind, range: Range<usize>) {
            self.events.push(Event::Token(kind, range));
        }
        fn exit(&mut self) {
            self.events.push(Event::Exit);
        }
        fn recovery(&mut self, recovery: Recovery, range: Range<usize>) {
            self.events.push(Event::Recovery(recovery, range));
        }
        fn replace_enter(&mut self, checkpoint: &Self::Checkpoint, kind: SyntaxKind) {
            assert!(matches!(self.events[*checkpoint], Event::Enter(_)));
            self.events[*checkpoint] = Event::Enter(kind);
        }
        fn start_enter_at(&mut self, checkpoint: &Self::Checkpoint, kind: SyntaxKind) {
            self.events.insert(*checkpoint, Event::Enter(kind));
        }
    }

    fn recorded(source: &str, mode: Mode) -> (Vec<Event>, Gate3State) {
        let mut sink = RecordingSink::default();
        let operators = OperatorTable::empty();
        let state = parse(source, mode, &operators, &mut sink);
        let mut depth = 0usize;
        for event in &sink.events {
            match event {
                Event::Enter(_) => depth += 1,
                Event::Exit => depth = depth.checked_sub(1).expect("unmatched Gate-3 Exit"),
                Event::Token(_, _) | Event::Recovery(_, _) => {}
            }
        }
        assert_eq!(depth, 0, "unclosed Gate-3 event node for {source:?}");
        (sink.events, state)
    }

    fn assert_exact_final_state(source: &str, state: Gate3State) {
        let line = source.bytes().filter(|byte| *byte == b'\n').count();
        let column = source
            .rfind('\n')
            .map_or(source.len(), |newline| source.len() - newline - 1);
        assert_eq!(
            state,
            Gate3State {
                consumed: source.len(),
                line,
                column,
                at_line_start: source.is_empty() || source.ends_with('\n'),
                frame_depth: 0,
                byte_visits: source.len(),
            },
            "{source:?}",
        );
    }

    fn kinds(events: &[Event]) -> Vec<SyntaxKind> {
        events
            .iter()
            .filter_map(|event| match event {
                Event::Enter(kind) | Event::Token(kind, _) => Some(*kind),
                Event::Exit | Event::Recovery(_, _) => None,
            })
            .collect()
    }

    fn recoveries(events: &[Event]) -> Vec<(Recovery, Range<usize>)> {
        events
            .iter()
            .filter_map(|event| match event {
                Event::Recovery(recovery, range) => Some((*recovery, range.clone())),
                _ => None,
            })
            .collect()
    }

    fn tokens(events: &[Event]) -> Vec<(SyntaxKind, Range<usize>)> {
        events
            .iter()
            .filter_map(|event| match event {
                Event::Token(kind, range) => Some((*kind, range.clone())),
                _ => None,
            })
            .collect()
    }

    #[test]
    fn inline_surface_table_has_exact_ranges_recovery_and_state() {
        for (source, expected_kinds, expected_recovery) in [
            (
                "*e*",
                vec![
                    SyntaxKind::YmDoc,
                    SyntaxKind::YmEmphasis,
                    SyntaxKind::YmEmphasisMarker,
                    SyntaxKind::YmDoc,
                    SyntaxKind::YmText,
                    SyntaxKind::YmEmphasisMarker,
                ],
                vec![],
            ),
            (
                "**s**",
                vec![
                    SyntaxKind::YmDoc,
                    SyntaxKind::YmStrong,
                    SyntaxKind::YmStrongMarker,
                    SyntaxKind::YmDoc,
                    SyntaxKind::YmText,
                    SyntaxKind::YmStrongMarker,
                ],
                vec![],
            ),
            (
                "[g]",
                vec![
                    SyntaxKind::YmDoc,
                    SyntaxKind::YmInlineGroup,
                    SyntaxKind::LBracket,
                    SyntaxKind::YmDoc,
                    SyntaxKind::YmText,
                    SyntaxKind::RBracket,
                ],
                vec![],
            ),
            (
                "[l](raw dest)",
                vec![
                    SyntaxKind::YmDoc,
                    SyntaxKind::YmInlineLink,
                    SyntaxKind::LBracket,
                    SyntaxKind::YmDoc,
                    SyntaxKind::YmText,
                    SyntaxKind::RBracket,
                    SyntaxKind::LParen,
                    SyntaxKind::YmText,
                    SyntaxKind::RParen,
                ],
                vec![],
            ),
            (
                "![a](img.png)",
                vec![
                    SyntaxKind::YmDoc,
                    SyntaxKind::YmInlineImage,
                    SyntaxKind::YmBangLBracket,
                    SyntaxKind::YmDoc,
                    SyntaxKind::YmText,
                    SyntaxKind::RBracket,
                    SyntaxKind::LParen,
                    SyntaxKind::YmText,
                    SyntaxKind::RParen,
                ],
                vec![],
            ),
            (
                "![a]tail",
                vec![
                    SyntaxKind::YmDoc,
                    SyntaxKind::YmInlineImage,
                    SyntaxKind::YmBangLBracket,
                    SyntaxKind::YmDoc,
                    SyntaxKind::YmText,
                    SyntaxKind::RBracket,
                    SyntaxKind::YmText,
                ],
                vec![(
                    Recovery {
                        kind: SyntaxKind::Missing,
                        owner: RecoveryOwner::InlineImage,
                        slot: RecoverySlot::Destination,
                    },
                    4..4,
                )],
            ),
            (
                "[a]:bold",
                vec![
                    SyntaxKind::YmDoc,
                    SyntaxKind::YmInlineApply,
                    SyntaxKind::LBracket,
                    SyntaxKind::YmDoc,
                    SyntaxKind::YmText,
                    SyntaxKind::RBracket,
                    SyntaxKind::Colon,
                    SyntaxKind::YmInlineApplyHead,
                    SyntaxKind::Identifier,
                ],
                vec![],
            ),
            (
                "\\name;",
                vec![
                    SyntaxKind::YmDoc,
                    SyntaxKind::YmInlineRef,
                    SyntaxKind::YmBackslash,
                    SyntaxKind::Identifier,
                    SyntaxKind::Semicolon,
                ],
                vec![],
            ),
            ("_", vec![SyntaxKind::YmDoc, SyntaxKind::YmText], vec![]),
        ] {
            let (events, state) = recorded(source, Mode::Line);
            assert_eq!(kinds(&events), expected_kinds, "{source:?}");
            assert_eq!(recoveries(&events), expected_recovery, "{source:?}");
            assert_eq!(state.consumed, source.len(), "{source:?}");
            assert_eq!(state.byte_visits, source.len(), "{source:?}");
            assert_eq!(state.frame_depth, 0, "{source:?}");
        }
    }

    #[test]
    fn line_mode_disables_block_nuds_and_leaves_the_physical_newline() {
        for source in ["# heading\nouter", "- item\r\nouter", "> quote\nouter"] {
            let (events, state) = recorded(source, Mode::Line);
            assert_eq!(
                kinds(&events),
                vec![SyntaxKind::YmDoc, SyntaxKind::YmText],
                "{source:?}"
            );
            let newline = source.find(['\r', '\n']).expect("fixture newline");
            assert_eq!(state.consumed, newline, "{source:?}");
            assert_eq!(state.byte_visits, newline, "{source:?}");
            assert_eq!(state.frame_depth, 0, "{source:?}");
        }
    }

    #[test]
    fn block_surface_table_covers_heading_list_quote_paragraph_and_raw_fence() {
        for (source, required) in [
            (
                "# \ntext",
                vec![
                    SyntaxKind::YmSection,
                    SyntaxKind::YmImplicitSection,
                    SyntaxKind::YmHeading,
                    SyntaxKind::YmParagraph,
                ],
            ),
            (
                "# title:\n  body",
                vec![
                    SyntaxKind::YmSection,
                    SyntaxKind::YmExplicitSection,
                    SyntaxKind::YmHeading,
                    SyntaxKind::YmParagraph,
                ],
            ),
            (
                "- one\n- two",
                vec![
                    SyntaxKind::YmList,
                    SyntaxKind::YmListItem,
                    SyntaxKind::YmListItemBody,
                ],
            ),
            (
                "> one\n> two",
                vec![SyntaxKind::YmQuoteBlock, SyntaxKind::YmQuotePrefix],
            ),
            (
                ">>>\nquoted\n>>>\n",
                vec![SyntaxKind::YmQuoteBlock, SyntaxKind::YmQuoteFenceMarker],
            ),
            (
                "one\ntwo\n\nthree",
                vec![SyntaxKind::YmParagraph, SyntaxKind::YmBlankLine],
            ),
            (
                "```rust\nfn main() {}\n```\n",
                vec![
                    SyntaxKind::YmCodeFence,
                    SyntaxKind::YmCodeFenceInfo,
                    SyntaxKind::YmCodeFenceText,
                ],
            ),
        ] {
            let (events, state) = recorded(source, Mode::Block);
            let actual = kinds(&events);
            for kind in required {
                assert!(actual.contains(&kind), "{source:?}: missing {kind:?}");
            }
            assert_eq!(state.consumed, source.len(), "{source:?}");
            assert_eq!(state.byte_visits, source.len(), "{source:?}");
            assert_eq!(state.frame_depth, 0, "{source:?}");
        }
    }

    #[test]
    fn selected_yulang_fence_has_no_gate3_body_event() {
        let source = "```  yulang doctest\nour x\n```\n";
        let (events, state) = recorded(source, Mode::Block);
        assert!(kinds(&events).contains(&SyntaxKind::YmCodeFence));
        assert!(!kinds(&events).contains(&SyntaxKind::YmCodeFenceText));
        assert!(!kinds(&events).contains(&SyntaxKind::YmYulangCodeCell));
        assert_eq!(state.consumed, source.len());
        assert_eq!(state.byte_visits, source.len());
    }

    #[test]
    fn prefix_quote_fences_reuse_the_shared_boundary_and_keep_close_ranges() {
        for (source, expects_body) in [
            ("> ```rust\n> body\n> ``` \t\r\n", true),
            ("> ```yulang\n> our x\n> ```\n", false),
        ] {
            let (events, state) = recorded(source, Mode::Block);
            assert_eq!(
                kinds(&events).contains(&SyntaxKind::YmCodeFenceText),
                expects_body,
                "{source:?}"
            );
            assert_eq!(
                events
                    .iter()
                    .filter(|event| matches!(event, Event::Token(SyntaxKind::YmFenceMarker, _)))
                    .count(),
                2,
                "{source:?}"
            );
            assert!(recoveries(&events).is_empty(), "{source:?}");
            assert_eq!(state.consumed, source.len(), "{source:?}");
            assert_eq!(state.byte_visits, source.len(), "{source:?}");
        }
    }

    #[test]
    fn missing_inline_and_fence_closes_use_typed_gate3_recovery() {
        let (inline, _) = recorded("*[x", Mode::Line);
        assert_eq!(
            recoveries(&inline),
            vec![
                (
                    Recovery {
                        kind: SyntaxKind::Missing,
                        owner: RecoveryOwner::InlineGroup,
                        slot: RecoverySlot::ClosingDelimiter
                    },
                    3..3
                ),
                (
                    Recovery {
                        kind: SyntaxKind::Missing,
                        owner: RecoveryOwner::Emphasis,
                        slot: RecoverySlot::ClosingDelimiter
                    },
                    3..3
                ),
            ]
        );
        let (fence, _) = recorded("```txt\nbody", Mode::Block);
        assert_eq!(
            recoveries(&fence),
            vec![(
                Recovery {
                    kind: SyntaxKind::Missing,
                    owner: RecoveryOwner::CodeFence,
                    slot: RecoverySlot::ClosingDelimiter
                },
                11..11
            )]
        );
    }

    #[test]
    fn completion_rows_have_exact_consumption_ranges_recovery_and_state() {
        struct Row {
            source: &'static str,
            tokens: Vec<(SyntaxKind, Range<usize>)>,
            recovery: Vec<(Recovery, Range<usize>)>,
        }
        for row in [
            Row {
                source: "# \n",
                tokens: vec![
                    (SyntaxKind::YmHeadingMarker, 0..1),
                    (SyntaxKind::Whitespace, 1..2),
                    (SyntaxKind::Newline, 2..3),
                ],
                recovery: vec![],
            },
            Row {
                source: "- item\n next\nparent",
                tokens: vec![
                    (SyntaxKind::YmListMarker, 0..2),
                    (SyntaxKind::YmText, 2..6),
                    (SyntaxKind::Newline, 6..7),
                    (SyntaxKind::Whitespace, 7..8),
                    (SyntaxKind::YmText, 8..12),
                    (SyntaxKind::Newline, 12..13),
                    (SyntaxKind::YmText, 13..19),
                ],
                recovery: vec![],
            },
            Row {
                source: "![alt] tail",
                tokens: vec![
                    (SyntaxKind::YmBangLBracket, 0..2),
                    (SyntaxKind::YmText, 2..5),
                    (SyntaxKind::RBracket, 5..6),
                    (SyntaxKind::YmText, 6..11),
                ],
                recovery: vec![(
                    Recovery {
                        kind: SyntaxKind::Missing,
                        owner: RecoveryOwner::InlineImage,
                        slot: RecoverySlot::Destination,
                    },
                    6..6,
                )],
            },
            Row {
                source: "one\n\ntwo",
                tokens: vec![
                    (SyntaxKind::YmText, 0..3),
                    (SyntaxKind::Newline, 3..4),
                    (SyntaxKind::Newline, 4..5),
                    (SyntaxKind::YmText, 5..8),
                ],
                recovery: vec![],
            },
        ] {
            let (events, state) = recorded(row.source, Mode::Block);
            assert_eq!(tokens(&events), row.tokens, "{:?}", row.source);
            assert_eq!(recoveries(&events), row.recovery, "{:?}", row.source);
            assert_eq!(state.consumed, row.source.len(), "{:?}", row.source);
            assert_eq!(state.byte_visits, row.source.len(), "{:?}", row.source);
            assert_eq!(state.frame_depth, 0, "{:?}", row.source);
        }
    }

    #[test]
    fn multiline_groups_continue_but_blank_lines_end_with_one_missing() {
        let (continued, state) = recorded("[a\r\nb]", Mode::Block);
        assert!(recoveries(&continued).is_empty());
        assert_eq!(state.consumed, 6);
        assert_eq!(
            tokens(&continued),
            vec![
                (SyntaxKind::LBracket, 0..1),
                (SyntaxKind::YmText, 1..2),
                (SyntaxKind::Newline, 2..4),
                (SyntaxKind::YmText, 4..5),
                (SyntaxKind::RBracket, 5..6),
            ]
        );

        let (blank, _) = recorded("[a\n\nnext", Mode::Block);
        assert_eq!(
            recoveries(&blank),
            vec![(
                Recovery {
                    kind: SyntaxKind::Missing,
                    owner: RecoveryOwner::InlineGroup,
                    slot: RecoverySlot::ClosingDelimiter,
                },
                2..2,
            )]
        );
    }

    #[test]
    fn explicit_and_prefix_quote_mixing_is_one_local_error_without_conversion() {
        for source in [">>>\n> mixed\n>>>\n", "> prefix\n>>>\n> after"] {
            let (events, state) = recorded(source, Mode::Block);
            assert_eq!(
                recoveries(&events)
                    .iter()
                    .filter(|(recovery, _)| recovery.slot == RecoverySlot::QuoteForm)
                    .count(),
                1,
                "{source:?}"
            );
            assert_eq!(state.consumed, source.len(), "{source:?}");
            assert_eq!(state.frame_depth, 0, "{source:?}");
        }
    }

    #[test]
    fn section_and_list_parent_returns_leave_the_first_unowned_line_for_parent() {
        for source in [
            "# outer:\n  ## inner\n  body\nparent",
            "- parent\n  - child\n  child body\n- sibling",
            "  - item\n next\nparent",
        ] {
            let (events, state) = recorded(source, Mode::Block);
            assert!(recoveries(&events).is_empty(), "{source:?}");
            assert_eq!(state.consumed, source.len(), "{source:?}");
            assert_eq!(state.byte_visits, source.len(), "{source:?}");
            assert_eq!(state.frame_depth, 0, "{source:?}");
            assert!(
                tokens(&events)
                    .iter()
                    .any(|(kind, range)| *kind == SyntaxKind::YmText
                        && &source[range.clone()] == "parent"),
                "{source:?}"
            );
        }
    }

    #[test]
    fn fence_and_explicit_quote_close_only_at_the_opener_column() {
        for (source, owner) in [
            ("  ```txt\n``` not-close\n  ```\n", RecoveryOwner::CodeFence),
            ("  >>>\n>>> not-close\n  >>>\n", RecoveryOwner::Quote),
        ] {
            let (events, state) = recorded(source, Mode::Block);
            assert!(
                recoveries(&events)
                    .iter()
                    .all(|(recovery, _)| recovery.owner != owner
                        || recovery.slot != RecoverySlot::ClosingDelimiter),
                "{source:?}"
            );
            assert_eq!(state.consumed, source.len(), "{source:?}");
            assert_eq!(state.frame_depth, 0, "{source:?}");
        }
    }

    #[test]
    fn lf_crlf_tabs_and_utf8_keep_byte_ranges_and_one_committed_visit() {
        for source in ["# α\r\n\t- β\r\n", ">\tα\n> β", "```x\r\nα\r\n```\r\n"] {
            let (_, state) = recorded(source, Mode::Block);
            assert_eq!(state.consumed, source.len(), "{source:?}");
            assert_eq!(state.byte_visits, source.len(), "{source:?}");
            assert_eq!(state.frame_depth, 0, "{source:?}");
        }
    }

    #[test]
    fn ten_thousand_nested_groups_are_iterative_and_frame_bounded() {
        const DEPTH: usize = 10_000;
        let source = format!("{}x{}", "[".repeat(DEPTH), "]".repeat(DEPTH));
        let (events, state) = recorded(&source, Mode::Line);
        assert_eq!(
            events
                .iter()
                .filter(|event| matches!(event, Event::Enter(SyntaxKind::YmInlineGroup)))
                .count(),
            DEPTH
        );
        assert!(recoveries(&events).is_empty());
        assert_eq!(state.consumed, source.len());
        assert_eq!(state.byte_visits, source.len());
        assert_eq!(state.frame_depth, 0);
    }

    #[test]
    fn ten_thousand_mixed_section_list_quote_group_frames_use_one_forward_pass() {
        const EACH: usize = 3_334;
        let mut source = String::new();
        for level in 1..=EACH {
            source.extend(std::iter::repeat_n('#', level));
            source.push_str(" h\n");
        }
        for depth in 0..EACH {
            source.extend(std::iter::repeat_n(' ', depth * 2));
            source.push_str("- x\n");
        }
        for depth in 1..EACH {
            source.extend(std::iter::repeat_n('>', depth));
            source.push_str(" x\n");
        }
        source.extend(std::iter::repeat_n('>', EACH));
        source.push(' ');
        source.extend(std::iter::repeat_n('[', EACH));
        source.push('x');
        source.extend(std::iter::repeat_n(']', EACH));

        let (events, state) = recorded(&source, Mode::Block);
        assert!(recoveries(&events).is_empty());
        assert_eq!(state.consumed, source.len());
        assert_eq!(state.byte_visits, source.len());
        assert_eq!(state.frame_depth, 0);
        assert_eq!(
            events
                .iter()
                .filter(|event| matches!(event, Event::Enter(SyntaxKind::YmSection)))
                .count(),
            EACH
        );
        assert_eq!(
            events
                .iter()
                .filter(|event| matches!(event, Event::Enter(SyntaxKind::YmList)))
                .count(),
            EACH
        );
        assert_eq!(
            events
                .iter()
                .filter(|event| matches!(event, Event::Enter(SyntaxKind::YmQuoteBlock)))
                .count(),
            EACH
        );
        assert_eq!(
            events
                .iter()
                .filter(|event| matches!(event, Event::Enter(SyntaxKind::YmInlineGroup)))
                .count(),
            EACH
        );
    }

    #[test]
    fn gate4_general_command_and_inline_argument_table_is_exact() {
        let (bare, bare_state) = recorded("\\name", Mode::Block);
        assert_eq!(
            bare,
            vec![
                Event::Enter(SyntaxKind::YmDoc),
                Event::Enter(SyntaxKind::YmParagraph),
                Event::Enter(SyntaxKind::YmInlineRef),
                Event::Token(SyntaxKind::YmBackslash, 0..1),
                Event::Token(SyntaxKind::Identifier, 1..5),
                Event::Exit,
                Event::Exit,
                Event::Exit,
            ]
        );
        assert_eq!(
            bare_state,
            Gate3State {
                consumed: 5,
                line: 0,
                column: 5,
                at_line_start: false,
                frame_depth: 0,
                byte_visits: 5,
            }
        );

        for (source, mode, required, forbidden) in [
            (
                "\\name",
                Mode::Block,
                vec![SyntaxKind::YmInlineRef],
                vec![SyntaxKind::YmCommand],
            ),
            (
                "\\name(x);",
                Mode::Block,
                vec![
                    SyntaxKind::YmInlineRef,
                    SyntaxKind::YmYulangArgs,
                    SyntaxKind::OperatorChain,
                ],
                vec![SyntaxKind::YmCommand],
            ),
            (
                "\\name[doc]",
                Mode::Block,
                vec![SyntaxKind::YmCommand, SyntaxKind::YmDocArg],
                vec![],
            ),
            (
                "\\name(x)[doc]{body}",
                Mode::Block,
                vec![
                    SyntaxKind::YmCommand,
                    SyntaxKind::YmYulangArgs,
                    SyntaxKind::YmDocArg,
                    SyntaxKind::YmCommandBody,
                ],
                vec![],
            ),
            (
                "\\name:\n  body",
                Mode::Block,
                vec![SyntaxKind::YmCommand, SyntaxKind::YmCommandBody],
                vec![],
            ),
            (
                "\\outer{\\inner{body}}",
                Mode::Block,
                vec![SyntaxKind::YmCommand, SyntaxKind::YmCommandBody],
                vec![],
            ),
            (
                "\\outer{\nbody\n}\nafter",
                Mode::Block,
                vec![
                    SyntaxKind::YmCommand,
                    SyntaxKind::YmCommandBody,
                    SyntaxKind::YmParagraph,
                ],
                vec![],
            ),
            (
                "\\ref(x);",
                Mode::Line,
                vec![
                    SyntaxKind::YmInlineRef,
                    SyntaxKind::YmYulangArgs,
                    SyntaxKind::Semicolon,
                ],
                vec![],
            ),
            (
                "[d]:f(x)",
                Mode::Line,
                vec![
                    SyntaxKind::YmInlineApply,
                    SyntaxKind::YmInlineApplyArgs,
                    SyntaxKind::OperatorChain,
                ],
                vec![],
            ),
        ] {
            let (events, state) = recorded(source, mode);
            let actual = kinds(&events);
            for kind in required {
                assert!(actual.contains(&kind), "{source:?}: missing {kind:?}");
            }
            for kind in forbidden {
                assert!(!actual.contains(&kind), "{source:?}: unexpected {kind:?}");
            }
            assert!(recoveries(&events).is_empty(), "{source:?}");
            assert_exact_final_state(source, state);
            assert_eq!(state.frame_depth, 0, "{source:?}");
        }

        let (single_probe, state) = recorded("\\cmd(a)(b)[doc]", Mode::Block);
        assert!(kinds(&single_probe).contains(&SyntaxKind::YmInlineRef));
        assert!(!kinds(&single_probe).contains(&SyntaxKind::YmCommand));
        assert_exact_final_state("\\cmd(a)(b)[doc]", state);

        let (promoted, _) = recorded("\\cmd(a)[doc](b){body}", Mode::Block);
        assert_eq!(
            kinds(&promoted)
                .into_iter()
                .filter(|kind| *kind == SyntaxKind::YmCommandArgs)
                .count(),
            1
        );
        assert!(kinds(&promoted).contains(&SyntaxKind::YmCommandBody));
    }

    #[test]
    fn gate4_my_and_use_ownership_and_recovery_table_is_exact() {
        for (source, required) in [
            (
                "\\my f x = value;",
                vec![
                    SyntaxKind::YmMyBindingHead,
                    SyntaxKind::PatternMlApplicationTail,
                    SyntaxKind::YmMyExpressionBody,
                    SyntaxKind::OperatorChain,
                ],
            ),
            (
                "\\my(f x){body}",
                vec![
                    SyntaxKind::YmMyBindingHead,
                    SyntaxKind::Pattern,
                    SyntaxKind::YmCommandBody,
                ],
            ),
            (
                "\\my f x:\n  body",
                vec![SyntaxKind::YmMyBindingHead, SyntaxKind::YmCommandBody],
            ),
            (
                "\\my f =\n  value",
                vec![SyntaxKind::YmMyExpressionBody, SyntaxKind::OperatorChain],
            ),
            (
                "\\use std::io;",
                vec![SyntaxKind::YmUse, SyntaxKind::UseTree, SyntaxKind::UsePath],
            ),
            (
                "\\use(std::io)",
                vec![SyntaxKind::YmUse, SyntaxKind::UseTree, SyntaxKind::UsePath],
            ),
        ] {
            let (events, state) = recorded(source, Mode::Block);
            let actual = kinds(&events);
            for kind in required {
                assert!(actual.contains(&kind), "{source:?}: missing {kind:?}");
            }
            assert!(recoveries(&events).is_empty(), "{source:?}");
            assert_exact_final_state(source, state);
        }

        for (source, expected) in [
            (
                "\\my =",
                vec![
                    (RecoveryOwner::My, RecoverySlot::Head),
                    (RecoveryOwner::My, RecoverySlot::ExpressionBody),
                ],
            ),
            (
                "\\my f",
                vec![(RecoveryOwner::My, RecoverySlot::BodyIntroducer)],
            ),
            (
                "\\my(f = value;",
                vec![(RecoveryOwner::My, RecoverySlot::ClosingDelimiter)],
            ),
            ("\\use()", vec![(RecoveryOwner::Use, RecoverySlot::Route)]),
            (
                "\\use std::io",
                vec![(RecoveryOwner::Use, RecoverySlot::Terminator)],
            ),
            (
                "\\use(std::io",
                vec![(RecoveryOwner::Use, RecoverySlot::ClosingDelimiter)],
            ),
        ] {
            let (events, state) = recorded(source, Mode::Block);
            let actual: Vec<_> = recoveries(&events)
                .into_iter()
                .map(|(recovery, _)| (recovery.owner, recovery.slot))
                .collect();
            for recovery in expected {
                assert!(
                    actual.contains(&recovery),
                    "{source:?}: missing {recovery:?} in {actual:?}"
                );
            }
            assert_exact_final_state(source, state);
        }
    }

    #[test]
    fn gate4_if_chain_and_do_capture_layout_table_is_exact() {
        let chain = "\\if(a):\n  one\n\n\\elsif(b){two}\n\n\\else:\n  three";
        let (events, state) = recorded(chain, Mode::Block);
        let actual = kinds(&events);
        for kind in [
            SyntaxKind::YmIfChain,
            SyntaxKind::YmIf,
            SyntaxKind::YmElsif,
            SyntaxKind::YmElse,
        ] {
            assert!(actual.contains(&kind), "missing {kind:?}");
        }
        assert!(recoveries(&events).is_empty());
        assert_exact_final_state(chain, state);

        for source in ["\\elsif(a){x}", "\\else{x}"] {
            let (events, _) = recorded(source, Mode::Block);
            assert_eq!(
                recoveries(&events)
                    .into_iter()
                    .filter(|(recovery, _)| recovery.owner == RecoveryOwner::IfChain
                        && recovery.slot == RecoverySlot::BranchPredecessor)
                    .count(),
                1,
                "{source:?}",
            );
        }

        for source in [
            "\\wrap(do)\nafter",
            "\\wrap(do):\n  local\nafter",
            "\\wrap(do){local}\nafter",
            "\\outer(do)\n\\inner(do)\nafter",
        ] {
            let (events, state) = recorded(source, Mode::Block);
            assert!(
                kinds(&events).contains(&SyntaxKind::YmDoCapture),
                "{source:?}"
            );
            assert!(recoveries(&events).is_empty(), "{source:?}");
            assert_exact_final_state(source, state);
            assert_eq!(
                kinds(&events)
                    .into_iter()
                    .filter(|kind| *kind == SyntaxKind::YmDoCapture)
                    .count(),
                source.matches("(do)").count(),
                "{source:?}",
            );
        }

        let (mixed, _) = recorded("\\wrap(do)(x)\nafter", Mode::Block);
        assert!(!kinds(&mixed).contains(&SyntaxKind::YmDoCapture));
        assert_eq!(
            recoveries(&mixed)
                .into_iter()
                .filter(|(recovery, _)| recovery.owner == RecoveryOwner::DoCapture
                    && recovery.slot == RecoverySlot::Arguments)
                .count(),
            1
        );

        let (empty_condition, _) = recorded("\\if(){x}", Mode::Block);
        assert!(kinds(&empty_condition).contains(&SyntaxKind::Missing));
        assert!(!kinds(&empty_condition).contains(&SyntaxKind::YmYulangArgs));
        assert!(recoveries(&empty_condition).is_empty());

        for (source, expected) in [
            (
                "\\wrap(do )\nafter",
                vec![(
                    Recovery {
                        kind: SyntaxKind::Error,
                        owner: RecoveryOwner::DoCapture,
                        slot: RecoverySlot::Arguments,
                    },
                    8..9,
                )],
            ),
            (
                "\\wrap(do, x)\nafter",
                vec![(
                    Recovery {
                        kind: SyntaxKind::Error,
                        owner: RecoveryOwner::DoCapture,
                        slot: RecoverySlot::Arguments,
                    },
                    8..11,
                )],
            ),
            (
                "\\wrap(do x\nafter",
                vec![
                    (
                        Recovery {
                            kind: SyntaxKind::Error,
                            owner: RecoveryOwner::DoCapture,
                            slot: RecoverySlot::Arguments,
                        },
                        8..10,
                    ),
                    (
                        Recovery {
                            kind: SyntaxKind::Missing,
                            owner: RecoveryOwner::DoCapture,
                            slot: RecoverySlot::ClosingDelimiter,
                        },
                        10..10,
                    ),
                ],
            ),
        ] {
            let (events, state) = recorded(source, Mode::Block);
            assert_eq!(recoveries(&events), expected, "{source:?}");
            assert_exact_final_state(source, state);
        }
    }

    #[test]
    fn gate4_embedded_delimiters_are_owned_once_and_recover_locally() {
        for source in [
            "\\ref((x))",
            "\\ref(\" ) \" /* ) */ x)",
            "[d]:f(g(x), y)",
            "\\if(\" ) \" == x){ok}",
        ] {
            let (events, state) = recorded(source, Mode::Line);
            assert!(
                recoveries(&events).is_empty(),
                "{source:?}: {:?}",
                recoveries(&events)
            );
            assert!(!kinds(&events).contains(&SyntaxKind::Root), "{source:?}");
            assert!(
                !kinds(&events).contains(&SyntaxKind::Statement),
                "{source:?}"
            );
            assert_exact_final_state(source, state);
        }

        for (source, mode, owner) in [
            ("\\ref(x", Mode::Line, RecoveryOwner::InlineReference),
            ("[d]:f(x", Mode::Line, RecoveryOwner::InlineApply),
            ("\\cmd(x){body", Mode::Block, RecoveryOwner::Command),
            ("\\my f {body", Mode::Block, RecoveryOwner::My),
            ("\\if(x:{body}", Mode::Block, RecoveryOwner::IfBranch),
            ("\\if(x){body", Mode::Block, RecoveryOwner::IfBranch),
        ] {
            let (events, state) = recorded(source, mode);
            assert!(
                recoveries(&events).iter().any(|(recovery, _)| {
                    recovery.owner == owner && recovery.slot == RecoverySlot::ClosingDelimiter
                }),
                "{source:?}: {:?}",
                recoveries(&events)
            );
            assert_exact_final_state(source, state);
        }
    }

    #[test]
    fn missing_braced_command_close_returns_the_block_doc_close_unconsumed() {
        let source = "\\cmd{body\n---\nafter";
        let (events, state) = recorded(source, Mode::BlockDocument);
        assert_eq!(
            recoveries(&events),
            vec![(
                Recovery {
                    kind: SyntaxKind::Missing,
                    owner: RecoveryOwner::Command,
                    slot: RecoverySlot::ClosingDelimiter,
                },
                10..10,
            )]
        );
        assert_eq!(state.consumed, 10);
        assert_eq!(state.byte_visits, 10);
        assert_eq!(&source[state.consumed..], "---\nafter");
        assert_eq!(state.frame_depth, 0);
    }

    #[test]
    fn gate4_nested_recovery_resumes_inside_section_quote_and_list() {
        let source = "# section\n> - \\cmd(x){broken\n>   continued\n# next\nafter";
        let (events, state) = recorded(source, Mode::Block);
        let actual = kinds(&events);
        for kind in [
            SyntaxKind::YmSection,
            SyntaxKind::YmQuoteBlock,
            SyntaxKind::YmList,
            SyntaxKind::YmCommand,
        ] {
            assert!(actual.contains(&kind), "missing {kind:?}");
        }
        assert!(recoveries(&events).iter().any(|(recovery, _)| {
            recovery.owner == RecoveryOwner::Command
                && recovery.slot == RecoverySlot::ClosingDelimiter
        }));
        assert!(tokens(&events).iter().any(|(kind, range)| {
            *kind == SyntaxKind::YmText && &source[range.clone()] == "after"
        }));
        assert_exact_final_state(source, state);
    }

    #[test]
    fn ten_thousand_nested_commands_are_iterative_and_embedded_bytes_visit_once() {
        const DEPTH: usize = 10_000;
        let source = format!("{}x{}", "\\c{".repeat(DEPTH), "}".repeat(DEPTH));
        let (events, state) = recorded(&source, Mode::Block);
        assert_eq!(
            events
                .iter()
                .filter(|event| matches!(event, Event::Enter(SyntaxKind::YmCommand)))
                .count(),
            DEPTH,
        );
        assert!(recoveries(&events).is_empty());
        assert_exact_final_state(&source, state);

        let embedded = "\\call(f(\" ) \"), g /* ) */ (x)){body}";
        let (_, state) = recorded(embedded, Mode::Block);
        assert_exact_final_state(embedded, state);
    }
}
