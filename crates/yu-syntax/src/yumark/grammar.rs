//! Gate 3 isolated inline and block grammar.
//!
//! This is the one iterative grammar required by the doc-comment addendum
//! §§4, 5, 7–9. Commands and document envelopes belong to later gates.

use std::ops::Range;

use unicode_ident::{is_xid_continue, is_xid_start};

use crate::{
    SyntaxKind,
    lexical::{
        item::{BorrowedTarget, Boundary, StopKind},
        yumark::{
            FenceBoundary, FenceLineDecision, FenceOpener, FencePrefixPolicy, is_yulang_fence_info,
            judge_fence_line,
        },
    },
    operator_table::OperatorTable,
};

use super::frame::{EnvelopeStop, FrameOwner, InlineClose, YumarkFrame, YumarkFrameStack};
use super::judge::{
    ActiveClose as JudgeActiveClose, ChunkContext, ChunkKind, InlineClose as JudgeInlineClose,
    judge_chunk,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum RecoveryOwner {
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
    fn replace_enter(&mut self, checkpoint: &Self::Checkpoint, kind: SyntaxKind);
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
) -> Gate3State {
    let mut parser = Parser {
        source,
        position: 0,
        line: 0,
        column: 0,
        at_line_start: true,
        byte_visits: 0,
        operators,
        sink,
        frames: YumarkFrameStack::new(),
    };
    parser.frames.push(YumarkFrame::Document {
        base: 0,
        envelope_stop: match mode {
            Mode::Block => EnvelopeStop::BlockDocument,
            Mode::Line => EnvelopeStop::LineDocument,
        },
    });
    parser.sink.enter(SyntaxKind::YmDoc);
    match mode {
        Mode::Block => parser.parse_block_iterative(),
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
    operators: &'operators OperatorTable,
    sink: &'sink mut S,
    frames: YumarkFrameStack,
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

impl<S: Sink> Parser<'_, '_, '_, S> {
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

    /// The production Gate-3 block path. All structural nesting is represented
    /// by `open`; it never calls a Yumark block parser through Rust recursion.
    fn parse_block_iterative(&mut self) {
        let mut open = Vec::new();
        while self.position < self.source.len() {
            let line = physical_line(&self.source[self.position..], self.position);
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
                        self.sink.enter(SyntaxKind::YmSectionClose);
                        self.emit_token(SyntaxKind::YmHeadingMarker, line.indent_end..marker_end);
                        self.sink.exit();
                        self.sink.recovery(
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
        self.parse_paragraph(line);
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
        }
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

    fn parse_paragraph(&mut self, first: PhysicalLine) {
        self.sink.enter(SyntaxKind::YmParagraph);
        let mut line = first;
        let list_content_column = match self.frames.last() {
            Some(YumarkFrame::ListItem { content_column, .. }) => Some(*content_column),
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
                if next.indent_end == next.content_end {
                    return false;
                }
                if prefixed
                    || list_content_column
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
        // One inline driver owns the complete paragraph range, so groups may
        // cross an owned physical newline without closing/reopening or rescans.
        self.parse_inline_until(line.content_end);
        self.sink.exit();
        if line.end > line.content_end {
            self.emit_token(SyntaxKind::Newline, line.content_end..line.end);
        }
    }

    fn parse_inline_until(&mut self, limit: usize) {
        let mut inline: Vec<InlineFrame<S::Checkpoint>> = Vec::new();
        while self.position < limit {
            let rest = &self.source[self.position..limit];
            let active_close = inline.last().map(|frame| {
                JudgeActiveClose::Inline(match frame.close {
                    InlineClose::RightBracket => JudgeInlineClose::RightBracket,
                    InlineClose::Emphasis => JudgeInlineClose::Emphasis,
                    InlineClose::Strong => JudgeInlineClose::Strong,
                })
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
                self.open_inline(
                    &mut inline,
                    SyntaxKind::YmInlineGroup,
                    SyntaxKind::LBracket,
                    InlineClose::RightBracket,
                    RecoveryOwner::InlineGroup,
                    1,
                    FrameOwner::InlineGroup,
                );
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
                    .replace_enter(&frame.checkpoint, SyntaxKind::YmInlineLink);
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
                .replace_enter(&frame.checkpoint, SyntaxKind::YmInlineApply);
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
            self.sink.exit();
        } else {
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
}
