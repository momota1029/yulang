//! One isolated structural Yumark driver with AST and direct-CST adapters.

use std::{collections::HashMap, ops::Range, sync::Arc};

use crate::{
    grammar::{
        declaration::Recovered,
        expression::{
            commit_call_arguments_interior, finish_call_arguments_interior,
            finish_direct_call_arguments_interior, parse_call_arguments_interior,
            settle_ast_call_arguments_borrowed_close, settle_direct_call_arguments_borrowed_close,
        },
    },
    operator::OperatorTable,
    scan::word::scan_word,
    session::{
        Committed, CommittedRecoveryRecord, Delimiter, ExpectationSources, ExpectedSyntax,
        FullCstOutput, GrammarRole, LineState, PunctuationEvidence, RecoveryKind, RecoverySiteKey,
        SynIn, SyntaxExpectation, UnexpectedCategory, UnexpectedSyntax, YumarkEmbeddedOuterKind,
        YumarkEnvelopeStop, YumarkFrame, YumarkInlineClose, YumarkOwner, YumarkRole, YumarkSlot,
        YumarkSyntaxEvidence,
    },
    syntax_kind::SyntaxKind,
};
use chasa::{
    Back, ErrorSink, Input,
    error::std::{Unexpected, UnexpectedEndOfInput},
};

use super::judge::{QuoteMarkerFacts, quote_marker_facts};

use super::{
    YumarkBlankLine, YumarkBlock, YumarkCodeFence, YumarkDocument, YumarkEmphasis, YumarkHeading,
    YumarkInline, YumarkInlineApply, YumarkInlineDocument, YumarkInlineGroup, YumarkInlineImage,
    YumarkInlineLink, YumarkInlineReference, YumarkParagraph, YumarkQuote, YumarkQuoteForm,
    YumarkSection, YumarkSectionForm, YumarkStrong, YumarkText, YumarkYulangArguments,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Gate3Envelope {
    pub(super) base_column: usize,
    pub(super) stop: YumarkEnvelopeStop,
}

pub(super) struct DirectGate3Outcome<'source> {
    pub(super) output: FullCstOutput<'source>,
    pub(super) range: Range<usize>,
    pub(super) remainder: &'source str,
    pub(super) line: LineState,
    pub(super) frame_depth: usize,
    #[cfg(test)]
    pub(super) work: Gate3WorkCounters,
}

pub(super) struct AstGate3Outcome<'source> {
    pub(super) document: YumarkDocument<'source>,
    pub(super) recoveries: Vec<AstGate3Recovery>,
    #[cfg(test)]
    pub(super) work: Gate3WorkCounters,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct AstGate3Recovery {
    pub(super) role: GrammarRole,
    pub(super) range: Range<usize>,
    pub(super) kind: RecoveryKind,
    pub(super) expected: ExpectedSyntax,
    pub(super) order: usize,
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(super) struct Gate3WorkCounters {
    pub(super) paragraph_bytes: usize,
    pub(super) fence_bytes: usize,
    pub(super) frame_pushes: usize,
    pub(super) frame_pops: usize,
    pub(super) section_lookups: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ParagraphBoundaryContext {
    effective_base: usize,
    envelope_stop: YumarkEnvelopeStop,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum InlineLimit {
    FixedEnd(usize),
    Paragraph(ParagraphBoundaryContext),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct YumarkArgumentBoundary {
    active_close: Option<YumarkInlineClose>,
    limit: InlineLimit,
}

pub(super) fn probe_gate3_bridge_candidate<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
{
    let checkpoint = i.checkpoint();
    let accepted = if i.input.remainder().starts_with('(') {
        let _open = advance_yumark_input(i, 1);
        let floor = i.local.push_yumark_delimiter(Delimiter::Parenthesis);
        i.local.push_yumark_frame(YumarkFrame::EmbeddedYulang {
            owner: YumarkOwner::InlineReference,
            outer_kind: YumarkEmbeddedOuterKind::Paired(Delimiter::Parenthesis),
            delimiter_floor: floor,
        });
        !yumark_argument_boundary(
            i,
            floor,
            YumarkArgumentBoundary {
                active_close: None,
                limit: InlineLimit::Paragraph(ParagraphBoundaryContext {
                    effective_base: 0,
                    envelope_stop: YumarkEnvelopeStop::ParentFrame,
                }),
            },
        )
    } else {
        false
    };
    i.rollback(checkpoint);
    accepted
}

#[cfg(test)]
pub(super) fn probe_gate3_bridge_candidate_direct<'parse, 'source, 'local, E>(
    source: &'source str,
    i: SynIn<'parse, 'source, 'local, E>,
) -> (bool, FullCstOutput<'source>)
where
    E: ErrorSink<usize>,
{
    let mut committed = crate::session::Probe::new(i).commit(FullCstOutput::new(source));
    committed.start_node(SyntaxKind::Root);
    let accepted = committed.probe(|probe| probe_gate3_bridge_candidate(probe.input()));
    committed.finish_node();
    (accepted, committed.into_output())
}

pub(super) fn parse_gate3_ast<'source, E>(
    table: &OperatorTable,
    envelope: Gate3Envelope,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> AstGate3Outcome<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut io = AstIo {
        i,
        recoveries: Vec::new(),
        #[cfg(test)]
        work: Gate3WorkCounters::default(),
    };
    let document = drive_document(table, envelope, &mut io)
        .expect("the AST adapter retains the Yumark document");
    AstGate3Outcome {
        document,
        recoveries: io.recoveries,
        #[cfg(test)]
        work: io.work,
    }
}

pub(super) fn commit_gate3_direct<'parse, 'source, 'local, E>(
    source: &'source str,
    table: &OperatorTable,
    envelope: Gate3Envelope,
    i: SynIn<'parse, 'source, 'local, E>,
) -> DirectGate3Outcome<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut io = DirectIo {
        committed: crate::session::Probe::new(i).commit(FullCstOutput::new(source)),
        #[cfg(test)]
        work: Gate3WorkCounters::default(),
    };
    io.start_node(SyntaxKind::Root);
    let start = io.pos();
    let _ = drive_document(table, envelope, &mut io);
    let range = start..io.pos();
    io.finish_node();
    let (remainder, line, frame_depth) = io.committed.probe(|probe| {
        (
            probe.input().input.remainder(),
            probe.input().local.line(),
            probe.input().local.yumark_frame_depth(),
        )
    });
    DirectGate3Outcome {
        output: io.committed.into_output(),
        range,
        remainder,
        line,
        frame_depth,
        #[cfg(test)]
        work: io.work,
    }
}

trait DriverIo<'source, E: ErrorSink<usize>> {
    const RETAIN_AST: bool;

    type Mark: Copy;

    fn pos(&mut self) -> usize;
    fn remainder(&mut self) -> &'source str;
    fn line(&mut self) -> LineState;
    fn advance_yumark(&mut self, length: usize) -> Range<usize>;
    fn push_frame(&mut self, frame: YumarkFrame);
    fn pop_frame(&mut self) -> Option<YumarkFrame>;
    fn frame_depth(&mut self) -> usize;
    fn start_node(&mut self, kind: SyntaxKind);
    fn mark(&mut self) -> Self::Mark;
    fn start_node_at(&mut self, mark: Self::Mark, kind: SyntaxKind);
    fn token(&mut self, kind: SyntaxKind, range: Range<usize>);
    fn finish_node(&mut self);
    fn recovery(
        &mut self,
        owner: YumarkOwner,
        slot: YumarkSlot,
        range: Range<usize>,
        kind: RecoveryKind,
        expected: ExpectedSyntax,
    );
    fn scan_word(&mut self) -> Option<Range<usize>>;
    fn word_pending_after_backslash(&mut self) -> bool;
    #[cfg(test)]
    fn note_paragraph_bytes(&mut self, bytes: usize);
    #[cfg(test)]
    fn note_fence_bytes(&mut self, bytes: usize);
    #[cfg(test)]
    fn note_frame_push(&mut self);
    #[cfg(test)]
    fn note_frame_pop(&mut self);
    #[cfg(test)]
    fn note_section_lookup(&mut self);
    fn call_arguments(
        &mut self,
        table: &OperatorTable,
        owner: YumarkOwner,
        adapter: SyntaxKind,
        open: Range<usize>,
        boundary: YumarkArgumentBoundary,
    ) -> YumarkYulangArguments;
}

struct AstIo<'a, 'parse, 'source, 'local, E: ErrorSink<usize>> {
    i: &'a mut SynIn<'parse, 'source, 'local, E>,
    recoveries: Vec<AstGate3Recovery>,
    #[cfg(test)]
    work: Gate3WorkCounters,
}

impl<'source, E> DriverIo<'source, E> for AstIo<'_, '_, 'source, '_, E>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    const RETAIN_AST: bool = true;
    type Mark = ();

    fn pos(&mut self) -> usize {
        self.i.pos()
    }
    fn remainder(&mut self) -> &'source str {
        self.i.input.remainder()
    }
    fn line(&mut self) -> LineState {
        self.i.local.line()
    }
    fn advance_yumark(&mut self, length: usize) -> Range<usize> {
        advance_yumark_input(self.i, length)
    }
    fn push_frame(&mut self, frame: YumarkFrame) {
        self.i.local.push_yumark_frame(frame);
    }
    fn pop_frame(&mut self) -> Option<YumarkFrame> {
        self.i.local.pop_yumark_frame()
    }
    fn frame_depth(&mut self) -> usize {
        self.i.local.yumark_frame_depth()
    }
    fn start_node(&mut self, _: SyntaxKind) {}
    fn mark(&mut self) -> Self::Mark {}
    fn start_node_at(&mut self, _: Self::Mark, _: SyntaxKind) {}
    fn token(&mut self, _: SyntaxKind, _: Range<usize>) {}
    fn finish_node(&mut self) {}
    fn recovery(
        &mut self,
        owner: YumarkOwner,
        slot: YumarkSlot,
        range: Range<usize>,
        kind: RecoveryKind,
        expected: ExpectedSyntax,
    ) {
        let order = self.recoveries.len();
        self.recoveries.push(AstGate3Recovery {
            role: GrammarRole::Yumark(YumarkRole { owner, slot }),
            range,
            kind,
            expected,
            order,
        });
    }

    fn scan_word(&mut self) -> Option<Range<usize>> {
        self.i.run(scan_word).map(|word| word.range())
    }

    fn word_pending_after_backslash(&mut self) -> bool {
        let checkpoint = self.i.checkpoint();
        let pending = self.i.input.next() == Some('\\') && self.i.run(scan_word).is_some();
        self.i.rollback(checkpoint);
        pending
    }

    #[cfg(test)]
    fn note_paragraph_bytes(&mut self, bytes: usize) {
        self.work.paragraph_bytes += bytes;
    }
    #[cfg(test)]
    fn note_fence_bytes(&mut self, bytes: usize) {
        self.work.fence_bytes += bytes;
    }
    #[cfg(test)]
    fn note_frame_push(&mut self) {
        self.work.frame_pushes += 1;
    }
    #[cfg(test)]
    fn note_frame_pop(&mut self) {
        self.work.frame_pops += 1;
    }
    #[cfg(test)]
    fn note_section_lookup(&mut self) {
        self.work.section_lookups += 1;
    }

    fn call_arguments(
        &mut self,
        table: &OperatorTable,
        owner: YumarkOwner,
        _: SyntaxKind,
        open: Range<usize>,
        boundary: YumarkArgumentBoundary,
    ) -> YumarkYulangArguments {
        let floor = self.i.local.push_yumark_delimiter(Delimiter::Parenthesis);
        self.i.local.push_yumark_frame(YumarkFrame::EmbeddedYulang {
            owner,
            outer_kind: YumarkEmbeddedOuterKind::Paired(Delimiter::Parenthesis),
            delimiter_floor: floor,
        });
        let mut episode = parse_call_arguments_interior(
            table,
            self.i,
            |i| yumark_argument_boundary(i, floor, boundary),
        );
        settle_ast_call_arguments_borrowed_close(
            self.i,
            &mut episode,
            |i| yumark_argument_boundary(i, floor, boundary),
        );
        for recovery in self.i.local.drain_yumark_embedded_recoveries() {
            let order = self.recoveries.len();
            self.recoveries.push(AstGate3Recovery {
                role: recovery.spec.role,
                range: recovery.range,
                kind: recovery.kind,
                expected: recovery.spec.expected,
                order,
            });
        }
        let close = if self.i.local.yumark_at_delimiter_floor(floor)
            && self.i.input.remainder().starts_with(')')
        {
            Recovered::Complete(advance_yumark_input(self.i, 1))
        } else {
            let at = self.i.pos();
            self.recovery(
                owner,
                YumarkSlot::ClosingDelimiter,
                at..at,
                RecoveryKind::Missing,
                ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Parenthesis)),
            );
            Recovered::Incomplete
        };
        let _ = finish_call_arguments_interior(self.i, episode);
        assert!(
            matches!(self.i.local.pop_yumark_frame(), Some(YumarkFrame::EmbeddedYulang { owner: actual, .. }) if actual == owner)
        );
        self.i
            .local
            .pop_yumark_delimiter(floor, Delimiter::Parenthesis);
        YumarkYulangArguments {
            range: open.start..self.i.pos(),
            close,
        }
    }
}

struct DirectIo<'parse, 'source, 'local, E: ErrorSink<usize>> {
    committed: Committed<'parse, 'source, 'local, E, FullCstOutput<'source>>,
    #[cfg(test)]
    work: Gate3WorkCounters,
}

impl<'source, E> DriverIo<'source, E> for DirectIo<'_, 'source, '_, E>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    const RETAIN_AST: bool = false;
    type Mark = rowan::Checkpoint;

    fn pos(&mut self) -> usize {
        self.committed.probe(|p| p.input().pos())
    }
    fn remainder(&mut self) -> &'source str {
        self.committed.probe(|p| p.input().input.remainder())
    }
    fn line(&mut self) -> LineState {
        self.committed.probe(|p| p.input().local.line())
    }
    fn advance_yumark(&mut self, length: usize) -> Range<usize> {
        self.committed
            .probe(|probe| advance_yumark_input(probe.input(), length))
    }
    fn push_frame(&mut self, frame: YumarkFrame) {
        self.committed
            .probe(|p| p.input().local.push_yumark_frame(frame));
    }
    fn pop_frame(&mut self) -> Option<YumarkFrame> {
        self.committed.probe(|p| p.input().local.pop_yumark_frame())
    }
    fn frame_depth(&mut self) -> usize {
        self.committed
            .probe(|p| p.input().local.yumark_frame_depth())
    }
    fn start_node(&mut self, kind: SyntaxKind) {
        self.committed.start_node(kind);
    }
    fn mark(&mut self) -> Self::Mark {
        self.committed.checkpoint()
    }
    fn start_node_at(&mut self, mark: Self::Mark, kind: SyntaxKind) {
        self.committed.start_node_at(mark, kind);
    }
    fn token(&mut self, kind: SyntaxKind, range: Range<usize>) {
        self.committed.token(kind, range);
    }
    fn finish_node(&mut self) {
        self.committed.finish_node();
    }
    fn recovery(
        &mut self,
        owner: YumarkOwner,
        slot: YumarkSlot,
        range: Range<usize>,
        kind: RecoveryKind,
        expected: ExpectedSyntax,
    ) {
        let role = GrammarRole::Yumark(YumarkRole { owner, slot });
        let unexpected = match kind {
            RecoveryKind::Missing => Arc::from([]),
            RecoveryKind::Error => Arc::from([UnexpectedSyntax::Token {
                range: range.clone(),
                category: UnexpectedCategory::OtherCharacter,
            }]),
        };
        let record = self.committed.probe(|probe| {
            CommittedRecoveryRecord::new(
                probe.input().local,
                RecoverySiteKey {
                    role,
                    range: range.clone(),
                },
                kind,
                unexpected,
                Arc::from([SyntaxExpectation {
                    role,
                    expected,
                    range: range.clone(),
                    sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
                }]),
                0,
            )
        });
        match kind {
            RecoveryKind::Missing => self.committed.emit_missing(record),
            RecoveryKind::Error => self.committed.emit_error(record),
        }
    }

    fn scan_word(&mut self) -> Option<Range<usize>> {
        self.committed
            .probe(|probe| probe.input().run(scan_word).map(|word| word.range()))
    }

    fn word_pending_after_backslash(&mut self) -> bool {
        self.committed.probe(|probe| {
            let i = probe.input();
            let checkpoint = i.checkpoint();
            let pending = i.input.next() == Some('\\') && i.run(scan_word).is_some();
            i.rollback(checkpoint);
            pending
        })
    }

    #[cfg(test)]
    fn note_paragraph_bytes(&mut self, bytes: usize) {
        self.work.paragraph_bytes += bytes;
    }
    #[cfg(test)]
    fn note_fence_bytes(&mut self, bytes: usize) {
        self.work.fence_bytes += bytes;
    }
    #[cfg(test)]
    fn note_frame_push(&mut self) {
        self.work.frame_pushes += 1;
    }
    #[cfg(test)]
    fn note_frame_pop(&mut self) {
        self.work.frame_pops += 1;
    }
    #[cfg(test)]
    fn note_section_lookup(&mut self) {
        self.work.section_lookups += 1;
    }

    fn call_arguments(
        &mut self,
        table: &OperatorTable,
        owner: YumarkOwner,
        adapter: SyntaxKind,
        open: Range<usize>,
        boundary: YumarkArgumentBoundary,
    ) -> YumarkYulangArguments {
        self.committed.start_node(adapter);
        self.committed.token(SyntaxKind::LParen, open.clone());
        let floor = self.committed.probe(|probe| {
            let floor = probe
                .input()
                .local
                .push_yumark_delimiter(Delimiter::Parenthesis);
            probe
                .input()
                .local
                .push_yumark_frame(YumarkFrame::EmbeddedYulang {
                    owner,
                    outer_kind: YumarkEmbeddedOuterKind::Paired(Delimiter::Parenthesis),
                    delimiter_floor: floor,
                });
            floor
        });
        let mut episode = commit_call_arguments_interior(table, &mut self.committed, |i| {
            yumark_argument_boundary(i, floor, boundary)
        });
        settle_direct_call_arguments_borrowed_close(&mut self.committed, &mut episode, |i| {
            yumark_argument_boundary(i, floor, boundary)
        });
        let close = if self.committed.probe(|probe| {
            probe.input().local.yumark_at_delimiter_floor(floor)
                && probe.input().input.remainder().starts_with(')')
        }) {
            let close = self
                .committed
                .probe(|probe| advance_yumark_input(probe.input(), 1));
            self.committed.token(SyntaxKind::RParen, close.clone());
            Recovered::Complete(close)
        } else {
            let at = self.pos();
            self.recovery(
                owner,
                YumarkSlot::ClosingDelimiter,
                at..at,
                RecoveryKind::Missing,
                ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Parenthesis)),
            );
            Recovered::Incomplete
        };
        finish_direct_call_arguments_interior(&mut self.committed, episode);
        self.committed.probe(|probe| {
            assert!(matches!(probe.input().local.pop_yumark_frame(), Some(YumarkFrame::EmbeddedYulang { owner: actual, .. }) if actual == owner));
            probe.input().local.pop_yumark_delimiter(floor, Delimiter::Parenthesis);
        });
        self.committed.finish_node();
        YumarkYulangArguments {
            range: open.start..self.pos(),
            close,
        }
    }
}

fn yumark_argument_boundary<E>(
    i: &mut SynIn<E>,
    floor: crate::session::YumarkDelimiterFloor,
    boundary: YumarkArgumentBoundary,
) -> bool
where
    E: ErrorSink<usize>,
{
    if !i.local.yumark_at_delimiter_floor(floor) {
        return false;
    }
    let source = i.input.remainder();
    source.is_empty()
        || active_inline_close_pending(source, boundary.active_close)
        || match boundary.limit {
            InlineLimit::FixedEnd(end) => i.pos() >= end,
            InlineLimit::Paragraph(context) => paragraph_boundary_pending(source, context),
        }
}

fn yumark_source_unit_len(source: &str) -> Option<usize> {
    if source.starts_with("\r\n") {
        Some(2)
    } else {
        source.chars().next().map(char::len_utf8)
    }
}

fn advance_yumark_input<E>(i: &mut SynIn<E>, length: usize) -> Range<usize>
where
    E: ErrorSink<usize>,
{
    let start = i.pos();
    let end = start
        .checked_add(length)
        .expect("committed Yumark range endpoint is representable");
    let source = i.input.source();
    assert!(end <= source.len(), "committed Yumark range is in source");
    assert!(
        source.is_char_boundary(start) && source.is_char_boundary(end),
        "committed Yumark range cannot split a UTF-8 scalar"
    );
    assert!(
        !(start > 0
            && source.as_bytes()[start - 1] == b'\r'
            && source.as_bytes().get(start) == Some(&b'\n')),
        "committed Yumark range cannot start inside CRLF"
    );
    assert!(
        !(end > 0
            && source.as_bytes()[end - 1] == b'\r'
            && source.as_bytes().get(end) == Some(&b'\n')),
        "committed Yumark range cannot end inside CRLF"
    );
    while i.pos() < end {
        let character_start = i.pos();
        let remainder = i.input.remainder();
        let unit = yumark_source_unit_len(remainder).expect("committed Yumark unit exists");
        if unit == 2 && remainder.starts_with("\r\n") {
            i.input.next();
            i.input.next();
            i.local.set_line(LineState {
                last_newline: Some((character_start, character_start + 2)),
                line_start: character_start + 2,
                line_indent: 0,
                at_line_start: true,
            });
            continue;
        }
        let character = i.input.next().expect("committed Yumark range is in source");
        let character_end = i.pos();
        if character == '\n' {
            i.local.set_line(LineState {
                last_newline: Some((character_start, character_end)),
                line_start: character_end,
                line_indent: 0,
                at_line_start: true,
            });
        } else {
            let mut line = i.local.line();
            if matches!(character, ' ' | '\t') && line.at_line_start {
                line.line_indent += 1;
            } else if !matches!(character, ' ' | '\t') {
                line.at_line_start = false;
            }
            i.local.set_line(line);
        }
    }
    assert_eq!(i.pos(), end);
    start..end
}

fn advance_yumark<'source, E, I>(io: &mut I, length: usize) -> Range<usize>
where
    E: ErrorSink<usize>,
    I: DriverIo<'source, E>,
{
    io.advance_yumark(length)
}

#[derive(Clone, Copy)]
enum InlineFrameKind {
    Root,
    Group { open_start: usize },
    Image { marker_start: usize },
    Emphasis { open_start: usize },
    Strong { open_start: usize },
}

struct InlineFrame<M> {
    kind: InlineFrameKind,
    mark: M,
    items: Option<Vec<Recovered<YumarkInline>>>,
    start: usize,
}

fn inline_frame_close(kind: InlineFrameKind) -> Option<YumarkInlineClose> {
    match kind {
        InlineFrameKind::Root => None,
        InlineFrameKind::Group { .. } | InlineFrameKind::Image { .. } => {
            Some(YumarkInlineClose::RightBracket)
        }
        InlineFrameKind::Emphasis { .. } => Some(YumarkInlineClose::Emphasis),
        InlineFrameKind::Strong { .. } => Some(YumarkInlineClose::Strong),
    }
}

fn active_inline_close_pending(source: &str, close: Option<YumarkInlineClose>) -> bool {
    match close {
        Some(YumarkInlineClose::RightBracket) => source.starts_with(']'),
        Some(YumarkInlineClose::Emphasis) => source.starts_with('*'),
        Some(YumarkInlineClose::Strong) => source.starts_with("**"),
        None => false,
    }
}

fn inline_close_expected(owner: YumarkOwner) -> ExpectedSyntax {
    match owner {
        YumarkOwner::InlineGroup | YumarkOwner::InlineImage => {
            ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Bracket))
        }
        YumarkOwner::Emphasis => ExpectedSyntax::Yumark(YumarkSyntaxEvidence::EmphasisMarker),
        YumarkOwner::Strong => ExpectedSyntax::Yumark(YumarkSyntaxEvidence::StrongMarker),
        _ => unreachable!("only inline delimiter owners use this helper"),
    }
}

fn inline_limit_pending<'source, E, I>(io: &mut I, limit: InlineLimit) -> bool
where
    E: ErrorSink<usize>,
    I: DriverIo<'source, E>,
{
    match limit {
        InlineLimit::FixedEnd(end) => io.pos() >= end,
        InlineLimit::Paragraph(context) => paragraph_boundary_pending(io.remainder(), context),
    }
}

fn inline_construct_pending<'source, E, I>(io: &mut I, top: InlineFrameKind) -> bool
where
    E: ErrorSink<usize>,
    I: DriverIo<'source, E>,
{
    let source = io.remainder();
    active_inline_close_pending(source, inline_frame_close(top))
        || source.starts_with("![")
        || source.starts_with("**")
        || source.starts_with('[')
        || source.starts_with('*')
        || (source.starts_with('\\') && io.word_pending_after_backslash())
}

fn drive_inline<'source, E, I>(
    table: &OperatorTable,
    io: &mut I,
    limit: InlineLimit,
) -> Option<YumarkInlineDocument>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
    I: DriverIo<'source, E>,
{
    let start = io.pos();
    let mut frames = vec![InlineFrame {
        kind: InlineFrameKind::Root,
        mark: io.mark(),
        items: I::RETAIN_AST.then(Vec::new),
        start,
    }];

    while !inline_limit_pending::<E, I>(io, limit) {
        let source = io.remainder();
        let top = frames.last().expect("inline root frame").kind;
        let close_len = match top {
            InlineFrameKind::Group { .. } | InlineFrameKind::Image { .. }
                if source.starts_with(']') =>
            {
                Some(1)
            }
            InlineFrameKind::Strong { .. } if source.starts_with("**") => Some(2),
            InlineFrameKind::Emphasis { .. } if source.starts_with('*') => Some(1),
            _ => None,
        };
        if let Some(close_len) = close_len {
            let close = advance_yumark::<E, I>(io, close_len);
            io.token(
                match top {
                    InlineFrameKind::Strong { .. } => SyntaxKind::YmStrongMarker,
                    InlineFrameKind::Emphasis { .. } => SyntaxKind::YmEmphasisMarker,
                    _ => SyntaxKind::RBracket,
                },
                close.clone(),
            );
            if !matches!(top, InlineFrameKind::Image { .. }) {
                io.finish_node();
            }
            let mut frame = frames.pop().expect("matched inline frame");
            let document = frame.items.take().map(|items| YumarkInlineDocument {
                items,
                range: match top {
                    InlineFrameKind::Group { open_start }
                    | InlineFrameKind::Image {
                        marker_start: open_start,
                    }
                    | InlineFrameKind::Emphasis { open_start }
                    | InlineFrameKind::Strong { open_start } => open_start + close_len..close.start,
                    InlineFrameKind::Root => unreachable!(),
                },
            });
            let boundary = YumarkArgumentBoundary {
                active_close: frames
                    .last()
                    .and_then(|frame| inline_frame_close(frame.kind)),
                limit,
            };
            let item = finish_inline_frame(table, io, frame, document, close, boundary);
            if let (Some(parent), Some(item)) = (frames.last_mut(), item) {
                parent
                    .items
                    .as_mut()
                    .expect("AST parent")
                    .push(Recovered::Complete(item));
            }
            continue;
        }

        if source.starts_with("![") {
            let mark = io.mark();
            let marker = advance_yumark::<E, I>(io, 2);
            io.start_node(SyntaxKind::YmInlineImage);
            io.token(SyntaxKind::YmBangLBracket, marker.clone());
            io.push_frame(YumarkFrame::Inline {
                owner: YumarkOwner::InlineImage,
                close: YumarkInlineClose::RightBracket,
            });
            frames.push(InlineFrame {
                kind: InlineFrameKind::Image {
                    marker_start: marker.start,
                },
                mark,
                items: I::RETAIN_AST.then(Vec::new),
                start: marker.start,
            });
            continue;
        }
        if source.starts_with("**") {
            let mark = io.mark();
            let open = advance_yumark::<E, I>(io, 2);
            io.start_node(SyntaxKind::YmStrong);
            io.token(SyntaxKind::YmStrongMarker, open.clone());
            io.push_frame(YumarkFrame::Inline {
                owner: YumarkOwner::Strong,
                close: YumarkInlineClose::Strong,
            });
            frames.push(InlineFrame {
                kind: InlineFrameKind::Strong {
                    open_start: open.start,
                },
                mark,
                items: I::RETAIN_AST.then(Vec::new),
                start: open.start,
            });
            continue;
        }
        if source.starts_with('[') {
            let mark = io.mark();
            let open = advance_yumark::<E, I>(io, 1);
            io.start_node(SyntaxKind::YmInlineGroup);
            io.token(SyntaxKind::LBracket, open.clone());
            io.push_frame(YumarkFrame::Inline {
                owner: YumarkOwner::InlineGroup,
                close: YumarkInlineClose::RightBracket,
            });
            frames.push(InlineFrame {
                kind: InlineFrameKind::Group {
                    open_start: open.start,
                },
                mark,
                items: I::RETAIN_AST.then(Vec::new),
                start: open.start,
            });
            continue;
        }
        if source.starts_with('*') {
            let mark = io.mark();
            let open = advance_yumark::<E, I>(io, 1);
            io.start_node(SyntaxKind::YmEmphasis);
            io.token(SyntaxKind::YmEmphasisMarker, open.clone());
            io.push_frame(YumarkFrame::Inline {
                owner: YumarkOwner::Emphasis,
                close: YumarkInlineClose::Emphasis,
            });
            frames.push(InlineFrame {
                kind: InlineFrameKind::Emphasis {
                    open_start: open.start,
                },
                mark,
                items: I::RETAIN_AST.then(Vec::new),
                start: open.start,
            });
            continue;
        }
        if source.starts_with('\\') && io.word_pending_after_backslash() {
            let boundary = YumarkArgumentBoundary {
                active_close: inline_frame_close(top),
                limit,
            };
            let item = parse_inline_reference(table, io, boundary);
            if let Some(items) = frames.last_mut().and_then(|frame| frame.items.as_mut()) {
                items.push(Recovered::Complete(YumarkInline::Reference(item)));
            }
            continue;
        }

        let raw_start = io.pos();
        loop {
            if inline_limit_pending::<E, I>(io, limit) {
                break;
            }
            let tail = io.remainder();
            if io.pos() > raw_start && inline_construct_pending::<E, I>(io, top) {
                break;
            }
            let length = yumark_source_unit_len(tail).expect("inline source");
            advance_yumark::<E, I>(io, length);
            #[cfg(test)]
            if matches!(limit, InlineLimit::Paragraph(_)) {
                io.note_paragraph_bytes(length);
            }
            if inline_construct_pending::<E, I>(io, top) {
                break;
            }
        }
        let range = raw_start..io.pos();
        io.start_node(SyntaxKind::YmText);
        io.token(SyntaxKind::YmText, range.clone());
        io.finish_node();
        if let Some(items) = frames.last_mut().and_then(|frame| frame.items.as_mut()) {
            items.push(Recovered::Complete(YumarkInline::Text(YumarkText {
                range,
            })));
        }
    }

    while frames.len() > 1 {
        let mut frame = frames.pop().expect("unclosed inline frame");
        let (owner, open_start) = match frame.kind {
            InlineFrameKind::Group { open_start } => (YumarkOwner::InlineGroup, open_start),
            InlineFrameKind::Image { marker_start } => (YumarkOwner::InlineImage, marker_start),
            InlineFrameKind::Emphasis { open_start } => (YumarkOwner::Emphasis, open_start),
            InlineFrameKind::Strong { open_start } => (YumarkOwner::Strong, open_start),
            InlineFrameKind::Root => unreachable!(),
        };
        let at = io.pos();
        io.recovery(
            owner,
            YumarkSlot::ClosingDelimiter,
            at..at,
            RecoveryKind::Missing,
            inline_close_expected(owner),
        );
        io.finish_node();
        let document = frame.items.take().map(|items| YumarkInlineDocument {
            items,
            range: open_start + 1..at,
        });
        let item = incomplete_inline_frame(frame, document, at);
        let popped = io.pop_frame();
        debug_assert!(popped.is_some());
        if let (Some(parent), Some(item)) = (frames.last_mut(), item) {
            parent
                .items
                .as_mut()
                .expect("AST parent")
                .push(Recovered::Complete(item));
        }
    }
    let root = frames.pop().expect("inline root");
    root.items.map(|items| YumarkInlineDocument {
        items,
        range: start..io.pos(),
    })
}

fn finish_inline_frame<'source, E, I>(
    table: &OperatorTable,
    io: &mut I,
    frame: InlineFrame<I::Mark>,
    document: Option<YumarkInlineDocument>,
    close: Range<usize>,
    boundary: YumarkArgumentBoundary,
) -> Option<YumarkInline>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
    I: DriverIo<'source, E>,
{
    let _ = io.pop_frame();
    match frame.kind {
        InlineFrameKind::Group { open_start } => {
            let group = document.map(|document| YumarkInlineGroup {
                open: open_start..open_start + 1,
                document,
                close: Recovered::Complete(close.clone()),
                range: open_start..close.end,
            });
            if io.remainder().starts_with('(') {
                io.start_node_at(frame.mark, SyntaxKind::YmInlineLink);
                let destination_open = advance_yumark::<E, I>(io, 1);
                io.token(SyntaxKind::LParen, destination_open.clone());
                let destination_start = io.pos();
                let destination = consume_until_inline_destination_close::<E, I>(io);
                if destination.is_empty() {
                    debug_assert_eq!(destination, destination_start..destination_start);
                } else {
                    io.token(SyntaxKind::YmText, destination.clone());
                }
                let destination_close = if io.remainder().starts_with(')') {
                    let close = advance_yumark::<E, I>(io, 1);
                    io.token(SyntaxKind::RParen, close.clone());
                    Recovered::Complete(close)
                } else {
                    let at = io.pos();
                    io.recovery(
                        YumarkOwner::InlineLink,
                        YumarkSlot::ClosingDelimiter,
                        at..at,
                        RecoveryKind::Missing,
                        ExpectedSyntax::Punctuation(PunctuationEvidence::Close(
                            Delimiter::Parenthesis,
                        )),
                    );
                    Recovered::Incomplete
                };
                io.finish_node();
                return group.map(|group| {
                    YumarkInline::Link(YumarkInlineLink {
                        range: group.range.start..io.pos(),
                        group,
                        destination,
                        close: destination_close,
                    })
                });
            }
            if io.remainder().starts_with(':') {
                io.start_node_at(frame.mark, SyntaxKind::YmInlineApply);
                io.start_node(SyntaxKind::YmInlineApplyHead);
                let colon = advance_yumark::<E, I>(io, 1);
                io.token(SyntaxKind::Colon, colon.clone());
                let name = io.scan_word().unwrap_or_else(|| io.pos()..io.pos());
                io.token(SyntaxKind::Identifier, name.clone());
                io.finish_node();
                let arguments = if io.remainder().starts_with('(') {
                    let open = advance_yumark::<E, I>(io, 1);
                    Some(io.call_arguments(
                        table,
                        YumarkOwner::InlineApply,
                        SyntaxKind::YmInlineApplyArgs,
                        open,
                        boundary,
                    ))
                } else {
                    None
                };
                io.finish_node();
                return group.map(|group| {
                    YumarkInline::Apply(YumarkInlineApply {
                        range: group.range.start..io.pos(),
                        group,
                        head: colon.start..name.end,
                        arguments,
                    })
                });
            }
            group.map(YumarkInline::Group)
        }
        InlineFrameKind::Image { marker_start } => {
            let destination = if io.remainder().starts_with('(') {
                let open = advance_yumark::<E, I>(io, 1);
                io.token(SyntaxKind::LParen, open.clone());
                let start = io.pos();
                let consumed = consume_until_inline_destination_close::<E, I>(io);
                let range = if consumed.is_empty() {
                    start..start
                } else {
                    consumed
                };
                if !range.is_empty() {
                    io.token(SyntaxKind::YmText, range.clone());
                }
                Recovered::Complete(range)
            } else {
                io.recovery(
                    YumarkOwner::InlineImage,
                    YumarkSlot::Destination,
                    close.end..close.end,
                    RecoveryKind::Missing,
                    ExpectedSyntax::Path,
                );
                Recovered::Incomplete
            };
            let destination_close = if matches!(destination, Recovered::Complete(_)) {
                if io.remainder().starts_with(')') {
                    let range = advance_yumark::<E, I>(io, 1);
                    io.token(SyntaxKind::RParen, range.clone());
                    Some(Recovered::Complete(range))
                } else {
                    let at = io.pos();
                    io.recovery(
                        YumarkOwner::InlineImage,
                        YumarkSlot::ClosingDelimiter,
                        at..at,
                        RecoveryKind::Missing,
                        ExpectedSyntax::Punctuation(PunctuationEvidence::Close(
                            Delimiter::Parenthesis,
                        )),
                    );
                    Some(Recovered::Incomplete)
                }
            } else {
                None
            };
            io.finish_node();
            document.map(|document| {
                YumarkInline::Image(YumarkInlineImage {
                    marker: marker_start..marker_start + 2,
                    document,
                    group_close: Recovered::Complete(close),
                    destination,
                    destination_close,
                    range: marker_start..io.pos(),
                })
            })
        }
        InlineFrameKind::Emphasis { open_start } => document.map(|document| {
            YumarkInline::Emphasis(YumarkEmphasis {
                open: open_start..open_start + 1,
                document,
                close: Recovered::Complete(close.clone()),
                range: open_start..close.end,
            })
        }),
        InlineFrameKind::Strong { open_start } => document.map(|document| {
            YumarkInline::Strong(YumarkStrong {
                open: open_start..open_start + 2,
                document,
                close: Recovered::Complete(close.clone()),
                range: open_start..close.end,
            })
        }),
        InlineFrameKind::Root => unreachable!(),
    }
}

fn incomplete_inline_frame(
    frame: InlineFrame<impl Copy>,
    document: Option<YumarkInlineDocument>,
    at: usize,
) -> Option<YumarkInline> {
    match frame.kind {
        InlineFrameKind::Group { open_start } => document.map(|document| {
            YumarkInline::Group(YumarkInlineGroup {
                open: open_start..open_start + 1,
                document,
                close: Recovered::Incomplete,
                range: open_start..at,
            })
        }),
        InlineFrameKind::Image { marker_start } => document.map(|document| {
            YumarkInline::Image(YumarkInlineImage {
                marker: marker_start..marker_start + 2,
                document,
                group_close: Recovered::Incomplete,
                destination: Recovered::Incomplete,
                destination_close: None,
                range: marker_start..at,
            })
        }),
        InlineFrameKind::Emphasis { open_start } => document.map(|document| {
            YumarkInline::Emphasis(YumarkEmphasis {
                open: open_start..open_start + 1,
                document,
                close: Recovered::Incomplete,
                range: open_start..at,
            })
        }),
        InlineFrameKind::Strong { open_start } => document.map(|document| {
            YumarkInline::Strong(YumarkStrong {
                open: open_start..open_start + 2,
                document,
                close: Recovered::Incomplete,
                range: open_start..at,
            })
        }),
        InlineFrameKind::Root => unreachable!(),
    }
}

fn consume_until_inline_destination_close<'source, E, I>(io: &mut I) -> Range<usize>
where
    E: ErrorSink<usize>,
    I: DriverIo<'source, E>,
{
    let start = io.pos();
    while !io.remainder().is_empty()
        && !io.remainder().starts_with(')')
        && physical_newline_len(io.remainder()).is_none()
    {
        let length = yumark_source_unit_len(io.remainder()).expect("nonempty destination");
        advance_yumark::<E, I>(io, length);
    }
    start..io.pos()
}

fn parse_inline_reference<'source, E, I>(
    table: &OperatorTable,
    io: &mut I,
    boundary: YumarkArgumentBoundary,
) -> YumarkInlineReference
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
    I: DriverIo<'source, E>,
{
    io.start_node(SyntaxKind::YmInlineRef);
    let backslash = advance_yumark::<E, I>(io, 1);
    io.token(SyntaxKind::YmBackslash, backslash.clone());
    let name = io
        .scan_word()
        .expect("reference candidate has a canonical word");
    io.token(SyntaxKind::Identifier, name.clone());
    let mut arguments = None;
    let mut terminator = None;
    if io.remainder().starts_with('(') {
        let open = advance_yumark::<E, I>(io, 1);
        arguments = Some(io.call_arguments(
            table,
            YumarkOwner::InlineReference,
            SyntaxKind::YmYulangArgs,
            open,
            boundary,
        ));
    }
    if io.remainder().starts_with(';') {
        let range = advance_yumark::<E, I>(io, 1);
        io.token(SyntaxKind::Semicolon, range.clone());
        terminator = Some(range);
    }
    io.finish_node();
    YumarkInlineReference {
        backslash: backslash.clone(),
        name: Recovered::Complete(name),
        arguments,
        terminator,
        range: backslash.start..io.pos(),
    }
}

enum BlockFrame<'source> {
    Root {
        start: usize,
        envelope: Gate3Envelope,
        blocks: Option<Vec<Recovered<YumarkBlock<'source>>>>,
    },
    ImplicitSection {
        start: usize,
        level: usize,
        heading: Option<YumarkHeading>,
        body_start: usize,
        blocks: Option<Vec<Recovered<YumarkBlock<'source>>>>,
        close: Option<Range<usize>>,
    },
    ExplicitSection {
        start: usize,
        level: usize,
        parent_indent: usize,
        body_indent: usize,
        heading: Option<YumarkHeading>,
        introducer: Range<usize>,
        body_start: usize,
        blocks: Option<Vec<Recovered<YumarkBlock<'source>>>>,
        close: Option<Range<usize>>,
    },
    List {
        start: usize,
        indent: usize,
        items: Option<Vec<Recovered<super::YumarkListItem<'source>>>>,
    },
    ListItem {
        start: usize,
        marker: Range<usize>,
        indent: usize,
        content_column: usize,
        body_start: usize,
        blocks: Option<Vec<Recovered<YumarkBlock<'source>>>>,
    },
    PrefixQuote {
        start: usize,
        depth: usize,
        base: usize,
        markers: Option<Vec<Range<usize>>>,
        body_start: usize,
        blocks: Option<Vec<Recovered<YumarkBlock<'source>>>>,
    },
    ExplicitQuote {
        start: usize,
        depth: usize,
        base: usize,
        open: Range<usize>,
        body_start: usize,
        blocks: Option<Vec<Recovered<YumarkBlock<'source>>>>,
    },
}

#[derive(Clone, Copy)]
struct DriverFrameContext {
    effective_base: usize,
    envelope_stop: YumarkEnvelopeStop,
}

struct DriverFrame<'source> {
    context: DriverFrameContext,
    section_link: Option<usize>,
    quote_link: Option<usize>,
    kind: BlockFrame<'source>,
}

struct DocumentDriverState<'source> {
    stack: Vec<DriverFrame<'source>>,
    open_section_by_level: HashMap<usize, usize>,
    innermost_quote: Option<usize>,
}

impl<'source> DocumentDriverState<'source> {
    fn new(root: BlockFrame<'source>, context: DriverFrameContext) -> Self {
        Self {
            stack: vec![DriverFrame {
                context,
                section_link: None,
                quote_link: None,
                kind: root,
            }],
            open_section_by_level: HashMap::new(),
            innermost_quote: None,
        }
    }

    fn is_empty(&self) -> bool {
        self.stack.is_empty()
    }

    fn len(&self) -> usize {
        self.stack.len()
    }

    fn effective_base(&self) -> usize {
        self.stack
            .last()
            .expect("document driver root")
            .context
            .effective_base
    }

    fn envelope_stop(&self) -> YumarkEnvelopeStop {
        self.stack
            .last()
            .expect("document driver root")
            .context
            .envelope_stop
    }

    fn last(&self) -> Option<&BlockFrame<'source>> {
        self.stack.last().map(|frame| &frame.kind)
    }

    fn last_mut(&mut self) -> Option<&mut BlockFrame<'source>> {
        self.stack.last_mut().map(|frame| &mut frame.kind)
    }

    fn root(&self) -> &BlockFrame<'source> {
        &self.stack.first().expect("document driver root").kind
    }

    fn push<E, I>(
        &mut self,
        io: &mut I,
        kind: BlockFrame<'source>,
        persistent: YumarkFrame,
        effective_base: usize,
    ) where
        E: ErrorSink<usize>,
        I: DriverIo<'source, E>,
    {
        let index = self.stack.len();
        let section_link = kind
            .section_level()
            .and_then(|level| self.open_section_by_level.insert(level, index));
        let quote_link = kind.is_quote().then(|| self.innermost_quote.replace(index)).flatten();
        let envelope_stop = self.envelope_stop();
        io.push_frame(persistent);
        #[cfg(test)]
        io.note_frame_push();
        self.stack.push(DriverFrame {
            context: DriverFrameContext {
                effective_base,
                envelope_stop,
            },
            section_link,
            quote_link,
            kind,
        });
    }

    fn pop(&mut self) -> BlockFrame<'source> {
        let frame = self.stack.pop().expect("nested document driver frame");
        if let Some(level) = frame.kind.section_level() {
            if let Some(previous) = frame.section_link {
                self.open_section_by_level.insert(level, previous);
            } else {
                self.open_section_by_level.remove(&level);
            }
        }
        if frame.kind.is_quote() {
            debug_assert_eq!(self.innermost_quote, Some(self.stack.len()));
            self.innermost_quote = frame.quote_link;
        }
        frame.kind
    }

    fn finish_pop<E, I>(&mut self, io: &mut I)
    where
        E: ErrorSink<usize>,
        I: DriverIo<'source, E>,
    {
        let popped = io.pop_frame();
        debug_assert!(popped.is_some());
        #[cfg(test)]
        io.note_frame_pop();
    }

    fn section_index(&self, level: usize) -> Option<usize> {
        self.open_section_by_level.get(&level).copied()
    }

    fn quote_index(&self) -> Option<usize> {
        self.innermost_quote
    }
}

impl<'source> BlockFrame<'source> {
    fn blocks_mut(&mut self) -> Option<&mut Vec<Recovered<YumarkBlock<'source>>>> {
        match self {
            Self::Root { blocks, .. }
            | Self::ImplicitSection { blocks, .. }
            | Self::ExplicitSection { blocks, .. }
            | Self::ListItem { blocks, .. }
            | Self::PrefixQuote { blocks, .. }
            | Self::ExplicitQuote { blocks, .. } => blocks.as_mut(),
            Self::List { .. } => None,
        }
    }

    fn section_level(&self) -> Option<usize> {
        match self {
            Self::ImplicitSection { level, .. } | Self::ExplicitSection { level, .. } => {
                Some(*level)
            }
            _ => None,
        }
    }

    fn is_quote(&self) -> bool {
        matches!(self, Self::PrefixQuote { .. } | Self::ExplicitQuote { .. })
    }
}

fn drive_document<'source, E, I>(
    table: &OperatorTable,
    envelope: Gate3Envelope,
    io: &mut I,
) -> Option<YumarkDocument<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
    I: DriverIo<'source, E>,
{
    let initial_depth = io.frame_depth();
    let start = io.pos();
    io.start_node(SyntaxKind::YmDoc);
    io.push_frame(YumarkFrame::Document {
        base: envelope.base_column,
        envelope_stop: envelope.stop,
    });
    let mut state = DocumentDriverState::new(
        BlockFrame::Root {
            start,
            envelope,
            blocks: I::RETAIN_AST.then(Vec::new),
        },
        DriverFrameContext {
            effective_base: envelope.base_column,
            envelope_stop: envelope.stop,
        },
    );

    loop {
        if close_finished_frames::<E, I>(io, &mut state) {
            if state.is_empty() {
                break;
            }
            continue;
        }
        if state.is_empty() {
            break;
        }

        if root_boundary(io, &state) {
            while state.len() > 1 {
                close_top_frame::<E, I>(io, &mut state, None);
            }
            let root = state.stack.pop().expect("root frame").kind;
            io.finish_node();
            assert!(matches!(io.pop_frame(), Some(YumarkFrame::Document { .. })));
            assert_eq!(io.frame_depth(), initial_depth);
            if let BlockFrame::Root { start, blocks, .. } = root {
                return blocks.map(|blocks| YumarkDocument {
                    blocks,
                    range: start..io.pos(),
                });
            }
            unreachable!();
        }

        if settle_innermost_quote::<E, I>(io, &mut state) {
            continue;
        }

        let source = io.remainder();
        if let Some(blank_len) = blank_line_len(source) {
            let block_start = io.pos();
            io.start_node(SyntaxKind::YmBlankLine);
            emit_horizontal_and_newline::<E, I>(io, blank_len);
            io.finish_node();
            append_block(
                &mut state,
                I::RETAIN_AST.then(|| {
                    YumarkBlock::BlankLine(YumarkBlankLine {
                        range: block_start..io.pos(),
                    })
                }),
            );
            continue;
        }

        let indent = leading_horizontal(source);
        let line = &source[indent..];
        if close_for_layout::<E, I>(io, &mut state, indent, line) {
            continue;
        }

        if let Some((level, marker_len)) = section_close_marker(line) {
            if close_matching_section::<E, I>(io, &mut state, indent, level, marker_len) {
                continue;
            }
            if indent > 0 {
                let r = advance_yumark::<E, I>(io, indent);
                io.token(SyntaxKind::Whitespace, r);
            }
            let range = advance_yumark::<E, I>(io, marker_len);
            io.recovery(
                YumarkOwner::Section,
                YumarkSlot::SectionClose,
                range.clone(),
                RecoveryKind::Error,
                ExpectedSyntax::Yumark(YumarkSyntaxEvidence::SectionCloseMarker),
            );
            append_block(&mut state, None);
            continue;
        }
        if let Some((level, marker_len)) = heading_marker(line) {
            close_sections_for_heading::<E, I>(io, &mut state, level);
            open_section::<E, I>(table, io, &mut state, indent, level, marker_len);
            continue;
        }
        if let Some(marker_len) = list_marker_len(line) {
            open_or_continue_list::<E, I>(table, io, &mut state, indent, marker_len);
            continue;
        }
        if strict_fence_opener(line) {
            let parent_quote = raw_fence_parent_quote(&state);
            let fence = parse_raw_fence::<E, I>(io, indent, parent_quote);
            append_block(&mut state, fence.node.map(YumarkBlock::CodeFence));
            if fence.closed {
                let horizontal = leading_horizontal(io.remainder());
                if horizontal > 0 {
                    let range = advance_yumark::<E, I>(io, horizontal);
                    io.token(SyntaxKind::Whitespace, range);
                }
                if let Some(newline) = physical_newline_len(io.remainder()) {
                    let range = advance_yumark::<E, I>(io, newline);
                    io.token(SyntaxKind::Newline, range);
                }
            }
            continue;
        }
        if let Some(QuoteMarkerFacts {
            depth,
            marker_len,
            explicit,
            ..
        }) = quote_marker_facts(line, indent, state.effective_base())
        {
            open_quote::<E, I>(io, &mut state, indent, depth, marker_len, explicit);
            continue;
        }

        let paragraph = parse_paragraph::<E, I>(table, io, &state);
        append_block(&mut state, paragraph.map(YumarkBlock::Paragraph));
    }
    unreachable!("root closure returns")
}

fn append_block<'source>(
    state: &mut DocumentDriverState<'source>,
    block: Option<YumarkBlock<'source>>,
) {
    if let Some(block) = block {
        state
            .last_mut()
            .and_then(BlockFrame::blocks_mut)
            .expect("document-owning frame")
            .push(Recovered::Complete(block));
    }
}

fn root_boundary<'source, E, I>(io: &mut I, state: &DocumentDriverState<'source>) -> bool
where
    E: ErrorSink<usize>,
    I: DriverIo<'source, E>,
{
    if !matches!(state.root(), BlockFrame::Root { .. }) {
        return false;
    }
    let BlockFrame::Root { envelope, .. } = state.root() else {
        unreachable!()
    };
    if io.remainder().is_empty() {
        return true;
    }
    if envelope.stop == YumarkEnvelopeStop::LineDocument
        && physical_newline_len(io.remainder()).is_some()
    {
        return true;
    }
    envelope.stop == YumarkEnvelopeStop::BlockDocument
        && io.line().at_line_start
        && io.line().line_indent == envelope.base_column
        && strict_marker(io.remainder(), "---", true)
}

fn close_finished_frames<'source, E, I>(
    io: &mut I,
    state: &mut DocumentDriverState<'source>,
) -> bool
where
    E: ErrorSink<usize>,
    I: DriverIo<'source, E>,
{
    if io.remainder().is_empty() && state.len() > 1 {
        close_top_frame::<E, I>(io, state, None);
        return true;
    }
    false
}

fn close_top_frame<'source, E, I>(
    io: &mut I,
    state: &mut DocumentDriverState<'source>,
    explicit_close: Option<Range<usize>>,
) where
    E: ErrorSink<usize>,
    I: DriverIo<'source, E>,
{
    let frame = state.pop();
    let block = match frame {
        BlockFrame::ImplicitSection {
            start,
            level: _,
            heading,
            body_start,
            blocks,
            close,
            ..
        } => {
            io.finish_node();
            if let Some(close) = explicit_close.as_ref() {
                io.start_node(SyntaxKind::YmSectionClose);
                io.token(SyntaxKind::YmHeadingMarker, close.clone());
                io.finish_node();
            }
            io.finish_node();
            io.finish_node();
            heading.map(|heading| {
                YumarkBlock::Section(YumarkSection {
                    heading,
                    form: YumarkSectionForm::Implicit {
                        document: YumarkDocument {
                            blocks: blocks.expect("AST blocks"),
                            range: body_start..io.pos(),
                        },
                    },
                    close: explicit_close.or(close),
                    range: start..io.pos(),
                })
            })
        }
        BlockFrame::ExplicitSection {
            start,
            heading,
            introducer,
            body_start,
            blocks,
            close,
            ..
        } => {
            io.finish_node();
            if let Some(close) = explicit_close.as_ref() {
                io.start_node(SyntaxKind::YmSectionClose);
                io.token(SyntaxKind::YmHeadingMarker, close.clone());
                io.finish_node();
            }
            io.finish_node();
            io.finish_node();
            heading.map(|heading| {
                YumarkBlock::Section(YumarkSection {
                    heading,
                    form: YumarkSectionForm::Explicit {
                        body_introducer: introducer,
                        document: Recovered::Complete(YumarkDocument {
                            blocks: blocks.expect("AST blocks"),
                            range: body_start..io.pos(),
                        }),
                    },
                    close: explicit_close.or(close),
                    range: start..io.pos(),
                })
            })
        }
        BlockFrame::ListItem {
            start,
            marker,
            indent,
            content_column,
            body_start,
            blocks,
        } => {
            io.finish_node();
            io.finish_node();
            io.finish_node();
            let item = blocks.map(|blocks| super::YumarkListItem {
                marker,
                indent,
                content_column,
                body: YumarkDocument {
                    blocks,
                    range: body_start..io.pos(),
                },
                range: start..io.pos(),
            });
            if let Some(BlockFrame::List {
                items: Some(items), ..
            }) = state.last_mut()
            {
                if let Some(item) = item {
                    items.push(Recovered::Complete(item));
                }
            }
            state.finish_pop::<E, I>(io);
            return;
        }
        BlockFrame::List {
            start,
            indent,
            items,
        } => {
            io.finish_node();
            items.map(|items| {
                YumarkBlock::List(super::YumarkList {
                    items,
                    indent,
                    range: start..io.pos(),
                })
            })
        }
        BlockFrame::PrefixQuote {
            start,
            markers,
            body_start,
            blocks,
            ..
        } => {
            io.finish_node();
            io.finish_node();
            markers.map(|markers| {
                YumarkBlock::Quote(YumarkQuote {
                    form: YumarkQuoteForm::Prefix { markers },
                    document: YumarkDocument {
                        blocks: blocks.expect("AST blocks"),
                        range: body_start..io.pos(),
                    },
                    range: start..io.pos(),
                })
            })
        }
        BlockFrame::ExplicitQuote {
            start,
            open,
            body_start,
            blocks,
            ..
        } => {
            io.finish_node();
            let close = if let Some(close) = explicit_close {
                io.token(SyntaxKind::YmQuoteFenceMarker, close.clone());
                Recovered::Complete(close)
            } else {
                let at = io.pos();
                io.recovery(
                    YumarkOwner::Quote,
                    YumarkSlot::ClosingDelimiter,
                    at..at,
                    RecoveryKind::Missing,
                    ExpectedSyntax::Yumark(YumarkSyntaxEvidence::QuoteFenceMarker),
                );
                Recovered::Incomplete
            };
            io.finish_node();
            blocks.map(|blocks| {
                YumarkBlock::Quote(YumarkQuote {
                    form: YumarkQuoteForm::Explicit { open, close },
                    document: YumarkDocument {
                        blocks,
                        range: body_start..io.pos(),
                    },
                    range: start..io.pos(),
                })
            })
        }
        BlockFrame::Root { .. } => unreachable!(),
    };
    state.finish_pop::<E, I>(io);
    append_block(state, block);
}

fn close_for_layout<'source, E, I>(
    io: &mut I,
    state: &mut DocumentDriverState<'source>,
    indent: usize,
    line: &str,
) -> bool
where
    E: ErrorSink<usize>,
    I: DriverIo<'source, E>,
{
    match state.last() {
        Some(BlockFrame::ExplicitSection { body_indent, .. }) if indent < *body_indent => {
            close_top_frame::<E, I>(io, state, None);
            true
        }
        Some(BlockFrame::ListItem {
            indent: item_indent,
            content_column,
            ..
        }) => {
            let item_indent = *item_indent;
            let content_column = *content_column;
            let marker = list_marker_len(line);
            if indent < item_indent
                || (indent >= item_indent && indent < content_column && marker.is_none())
                || (indent == item_indent && marker.is_some())
            {
                close_top_frame::<E, I>(io, state, None);
                if indent < item_indent
                    || (indent >= item_indent && indent < content_column && marker.is_none())
                {
                    if matches!(state.last(), Some(BlockFrame::List { .. })) {
                        close_top_frame::<E, I>(io, state, None);
                    }
                }
                true
            } else {
                false
            }
        }
        Some(BlockFrame::List {
            indent: list_indent,
            ..
        }) if indent < *list_indent || list_marker_len(line).is_none() => {
            close_top_frame::<E, I>(io, state, None);
            true
        }
        _ => false,
    }
}

fn section_close_marker(source: &str) -> Option<(usize, usize)> {
    let level = source.bytes().take_while(|b| *b == b'#').count();
    (level > 0 && source[level..].starts_with('.')).then_some((level, level + 1))
}

fn close_matching_section<'source, E, I>(
    io: &mut I,
    state: &mut DocumentDriverState<'source>,
    indent: usize,
    level: usize,
    marker_len: usize,
) -> bool
where
    E: ErrorSink<usize>,
    I: DriverIo<'source, E>,
{
    #[cfg(test)]
    io.note_section_lookup();
    let Some(index) = state.section_index(level) else {
        return false;
    };
    while state.len() - 1 > index {
        close_top_frame::<E, I>(io, state, None);
    }
    if indent > 0 {
        let range = advance_yumark::<E, I>(io, indent);
        io.token(SyntaxKind::Whitespace, range);
    }
    let close = advance_yumark::<E, I>(io, marker_len);
    close_top_frame::<E, I>(io, state, Some(close));
    true
}

fn close_sections_for_heading<'source, E, I>(
    io: &mut I,
    state: &mut DocumentDriverState<'source>,
    level: usize,
) where
    E: ErrorSink<usize>,
    I: DriverIo<'source, E>,
{
    loop {
        let closes = matches!(state.last(),
            Some(BlockFrame::ImplicitSection { level: active, .. }) if *active >= level
        );
        if closes {
            close_top_frame::<E, I>(io, state, None);
        } else {
            break;
        }
    }
}

fn open_section<'source, E, I>(
    table: &OperatorTable,
    io: &mut I,
    state: &mut DocumentDriverState<'source>,
    indent: usize,
    level: usize,
    marker_len: usize,
) where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
    I: DriverIo<'source, E>,
{
    let start = io.pos();
    let mark_line = io.remainder();
    let after_prefix = &mark_line[indent + marker_len + 1..];
    let (content_len, newline_len) = line_extent(after_prefix);
    let content = &after_prefix[..content_len];
    let trimmed = content.trim_end_matches([' ', '\t']);
    let explicit = trimmed.ends_with(':');
    let title_len = if explicit {
        trimmed.len() - 1
    } else {
        content_len
    };

    io.start_node(SyntaxKind::YmSection);
    io.start_node(if explicit {
        SyntaxKind::YmExplicitSection
    } else {
        SyntaxKind::YmImplicitSection
    });
    if indent > 0 {
        let range = advance_yumark::<E, I>(io, indent);
        io.token(SyntaxKind::Whitespace, range);
    }
    io.start_node(SyntaxKind::YmHeading);
    let marker = advance_yumark::<E, I>(io, marker_len);
    io.token(SyntaxKind::YmHeadingMarker, marker.clone());
    let space = advance_yumark::<E, I>(io, 1);
    io.token(SyntaxKind::Whitespace, space);
    let title_end = io.pos() + title_len;
    let title = drive_inline::<E, I>(table, io, InlineLimit::FixedEnd(title_end));
    let introducer = if explicit {
        if content_len > title_len {
            let horizontal_len = content_len - title_len - 1;
            if horizontal_len > 0 {
                let range = advance_yumark::<E, I>(io, horizontal_len);
                io.token(SyntaxKind::Whitespace, range);
            }
        }
        let colon = advance_yumark::<E, I>(io, 1);
        io.token(SyntaxKind::Colon, colon.clone());
        colon
    } else {
        io.pos()..io.pos()
    };
    if !explicit && io.pos() < start + indent + marker_len + 1 + content_len {
        let remaining = start + indent + marker_len + 1 + content_len - io.pos();
        let range = advance_yumark::<E, I>(io, remaining);
        io.token(SyntaxKind::YmText, range);
    }
    io.finish_node();
    if let Some(nl) = newline_len {
        let range = advance_yumark::<E, I>(io, nl);
        io.token(SyntaxKind::Newline, range);
    }

    let heading = title.map(|title| YumarkHeading {
        marker,
        level,
        title,
        range: start..io.pos(),
    });
    let body_start = io.pos();
    io.start_node(SyntaxKind::YmDoc);
    if explicit {
        let body_indent = leading_horizontal(io.remainder());
        if io.remainder().is_empty() || body_indent <= indent {
            let at = io.pos();
            io.recovery(
                YumarkOwner::Section,
                YumarkSlot::Body,
                at..at,
                RecoveryKind::Missing,
                ExpectedSyntax::Statement,
            );
            io.finish_node();
            io.finish_node();
            io.finish_node();
            append_block(
                state,
                heading.map(|heading| {
                    YumarkBlock::Section(YumarkSection {
                        heading,
                        form: YumarkSectionForm::Explicit {
                            body_introducer: introducer,
                            document: Recovered::Incomplete,
                        },
                        close: None,
                        range: start..io.pos(),
                    })
                }),
            );
            return;
        }
        state.push::<E, I>(
            io,
            BlockFrame::ExplicitSection {
                start,
                level,
                parent_indent: indent,
                body_indent,
                heading,
                introducer,
                body_start,
                blocks: I::RETAIN_AST.then(Vec::new),
                close: None,
            },
            YumarkFrame::ExplicitSection {
                level,
                parent_indent: indent,
                body_indent,
            },
            body_indent,
        );
    } else {
        let effective_base = state.effective_base();
        state.push::<E, I>(
            io,
            BlockFrame::ImplicitSection {
                start,
                level,
                heading,
                body_start,
                blocks: I::RETAIN_AST.then(Vec::new),
                close: None,
            },
            YumarkFrame::ImplicitSection { level },
            effective_base,
        );
    }
}

fn open_or_continue_list<'source, E, I>(
    table: &OperatorTable,
    io: &mut I,
    state: &mut DocumentDriverState<'source>,
    indent: usize,
    marker_len: usize,
) where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
    I: DriverIo<'source, E>,
{
    if matches!(state.last(), Some(BlockFrame::ListItem { indent: active, .. }) if *active == indent)
    {
        close_top_frame::<E, I>(io, state, None);
    }
    let same_list =
        matches!(state.last(), Some(BlockFrame::List { indent: active, .. }) if *active == indent);
    if !same_list {
        let start = io.pos();
        io.start_node(SyntaxKind::YmList);
        let effective_base = state.effective_base();
        state.push::<E, I>(
            io,
            BlockFrame::List {
                start,
                indent,
                items: I::RETAIN_AST.then(Vec::new),
            },
            YumarkFrame::List { indent },
            effective_base,
        );
    }
    let start = io.pos();
    io.start_node(SyntaxKind::YmListItem);
    if indent > 0 {
        let range = advance_yumark::<E, I>(io, indent);
        io.token(SyntaxKind::Whitespace, range);
    }
    let marker = advance_yumark::<E, I>(io, marker_len);
    io.token(SyntaxKind::YmListMarker, marker.clone());
    let content_column = indent + marker_len;
    io.start_node(SyntaxKind::YmListItemBody);
    io.start_node(SyntaxKind::YmDoc);
    let body_start = io.pos();
    state.push::<E, I>(
        io,
        BlockFrame::ListItem {
            start,
            marker: marker.clone(),
            indent,
            content_column,
            body_start,
            blocks: I::RETAIN_AST.then(Vec::new),
        },
        YumarkFrame::ListItem {
            marker,
            indent,
            content_column,
        },
        content_column,
    );
    let horizontal = leading_horizontal(io.remainder());
    let content = &io.remainder()[horizontal..];
    if !content.is_empty() && physical_newline_len(content).is_none() {
        let paragraph = parse_paragraph::<E, I>(table, io, state);
        append_block(state, paragraph.map(YumarkBlock::Paragraph));
    }
}

fn open_quote<'source, E, I>(
    io: &mut I,
    state: &mut DocumentDriverState<'source>,
    indent: usize,
    depth: usize,
    marker_len: usize,
    explicit: bool,
) where
    E: ErrorSink<usize>,
    I: DriverIo<'source, E>,
{
    let start = io.pos();
    io.start_node(SyntaxKind::YmQuoteBlock);
    if indent > 0 {
        let range = advance_yumark::<E, I>(io, indent);
        io.token(SyntaxKind::Whitespace, range);
    }
    let marker = advance_yumark::<E, I>(io, marker_len);
    io.token(
        if explicit {
            SyntaxKind::YmQuoteFenceMarker
        } else {
            SyntaxKind::YmQuotePrefix
        },
        marker.clone(),
    );
    if explicit {
        let horizontal = leading_horizontal(io.remainder());
        if horizontal > 0 {
            let range = advance_yumark::<E, I>(io, horizontal);
            io.token(SyntaxKind::Whitespace, range);
        }
        if let Some(nl) = physical_newline_len(io.remainder()) {
            let range = advance_yumark::<E, I>(io, nl);
            io.token(SyntaxKind::Newline, range);
        }
        io.start_node(SyntaxKind::YmDoc);
        let body_start = io.pos();
        state.push::<E, I>(
            io,
            BlockFrame::ExplicitQuote {
                start,
                depth,
                base: indent,
                open: marker.clone(),
                body_start,
                blocks: I::RETAIN_AST.then(Vec::new),
            },
            YumarkFrame::ExplicitQuote { depth, marker },
            0,
        );
    } else {
        io.start_node(SyntaxKind::YmDoc);
        let body_start = io.pos();
        let marker_end_column = marker.end - io.line().line_start;
        state.push::<E, I>(
            io,
            BlockFrame::PrefixQuote {
                start,
                depth,
                base: indent,
                markers: I::RETAIN_AST.then(|| vec![marker]),
                body_start,
                blocks: I::RETAIN_AST.then(Vec::new),
            },
            YumarkFrame::PrefixQuote { depth },
            marker_end_column,
        );
    }
}

fn settle_innermost_quote<'source, E, I>(
    io: &mut I,
    state: &mut DocumentDriverState<'source>,
) -> bool
where
    E: ErrorSink<usize>,
    I: DriverIo<'source, E>,
{
    if !io.line().at_line_start {
        return false;
    }
    let Some(index) = state.quote_index() else {
        return false;
    };
    let (prefix, active, base) = match &state.stack[index].kind {
        BlockFrame::PrefixQuote { depth, base, .. } => (true, *depth, *base),
        BlockFrame::ExplicitQuote { depth, base, .. } => (false, *depth, *base),
        _ => unreachable!("quote index points at a quote frame"),
    };
    let indent = leading_horizontal(io.remainder());
    let line = &io.remainder()[indent..];
    let Some(facts) = quote_marker_facts(line, indent, base) else {
        if prefix {
            while state.len() - 1 >= index {
                close_top_frame::<E, I>(io, state, None);
            }
            return true;
        }
        return false;
    };
    if prefix {
        if facts.explicit {
            if indent > 0 {
                let range = advance_yumark::<E, I>(io, indent);
                io.token(SyntaxKind::Whitespace, range);
            }
            let marker = advance_yumark::<E, I>(io, facts.marker_len);
            io.recovery(
                YumarkOwner::Quote,
                YumarkSlot::QuoteForm,
                marker,
                RecoveryKind::Error,
                ExpectedSyntax::Statement,
            );
            return true;
        }
        if facts.depth > active {
            return false;
        }
        if facts.depth < active {
            while state.len() - 1 >= index {
                close_top_frame::<E, I>(io, state, None);
            }
            return true;
        }
        if indent > 0 {
            let range = advance_yumark::<E, I>(io, indent);
            io.token(SyntaxKind::Whitespace, range);
        }
        let marker = advance_yumark::<E, I>(io, facts.marker_len);
        io.token(SyntaxKind::YmQuotePrefix, marker.clone());
        if let BlockFrame::PrefixQuote {
            markers: Some(markers),
            ..
        } = &mut state.stack[index].kind
        {
            markers.push(marker);
        }
        return true;
    }
    if !facts.explicit {
        if indent > 0 {
            let range = advance_yumark::<E, I>(io, indent);
            io.token(SyntaxKind::Whitespace, range);
        }
        let marker = advance_yumark::<E, I>(io, facts.marker_end);
        io.recovery(
            YumarkOwner::Quote,
            YumarkSlot::QuoteForm,
            marker,
            RecoveryKind::Error,
            ExpectedSyntax::Statement,
        );
        return true;
    }
    if facts.depth != active {
        return false;
    }
    while state.len() - 1 > index {
        close_top_frame::<E, I>(io, state, None);
    }
    if indent > 0 {
        let range = advance_yumark::<E, I>(io, indent);
        io.token(SyntaxKind::Whitespace, range);
    }
    let close = advance_yumark::<E, I>(io, facts.marker_len);
    close_top_frame::<E, I>(io, state, Some(close));
    let suffix = leading_horizontal(io.remainder());
    if suffix > 0 {
        let range = advance_yumark::<E, I>(io, suffix);
        io.token(SyntaxKind::Whitespace, range);
    }
    if let Some(nl) = physical_newline_len(io.remainder()) {
        let range = advance_yumark::<E, I>(io, nl);
        io.token(SyntaxKind::Newline, range);
    }
    true
}

fn parse_paragraph<'source, E, I>(
    table: &OperatorTable,
    io: &mut I,
    state: &DocumentDriverState<'source>,
) -> Option<YumarkParagraph>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
    I: DriverIo<'source, E>,
{
    let start = io.pos();
    io.start_node(SyntaxKind::YmParagraph);
    let document = drive_inline::<E, I>(
        table,
        io,
        InlineLimit::Paragraph(ParagraphBoundaryContext {
            effective_base: state.effective_base(),
            envelope_stop: state.envelope_stop(),
        }),
    );
    io.finish_node();
    document.map(|document| YumarkParagraph {
        document,
        range: start..io.pos(),
    })
}

fn paragraph_boundary_pending(source: &str, context: ParagraphBoundaryContext) -> bool {
    if source.is_empty() {
        return true;
    }
    let Some(newline) = physical_newline_len(source) else {
        return false;
    };
    if context.envelope_stop == YumarkEnvelopeStop::LineDocument {
        return true;
    }
    let next = &source[newline..];
    if next.is_empty() || blank_line_len(next).is_some() {
        return true;
    }
    let indent = leading_horizontal(next);
    let line = &next[indent..];
    if indent < context.effective_base {
        return true;
    }
    section_close_marker(line).is_some()
        || heading_marker(line).is_some()
        || list_marker_len(line).is_some()
        || strict_fence_opener(line)
        || quote_marker_facts(line, indent, context.effective_base).is_some()
        || (indent == context.effective_base && strict_marker(line, "---", true))
}

#[derive(Clone, Copy)]
enum RawFenceParentQuote {
    Prefix { depth: usize, base: usize },
}

struct RawFenceParse {
    node: Option<YumarkCodeFence>,
    closed: bool,
}

fn raw_fence_parent_quote(state: &DocumentDriverState<'_>) -> Option<RawFenceParentQuote> {
    let index = state.quote_index()?;
    match &state.stack[index].kind {
        BlockFrame::PrefixQuote { depth, base, .. } => Some(RawFenceParentQuote::Prefix {
            depth: *depth,
            base: *base,
        }),
        BlockFrame::ExplicitQuote { .. } => None,
        _ => unreachable!("quote index points at a quote frame"),
    }
}

fn exact_raw_fence_prefix_len(source: &str, parent: RawFenceParentQuote) -> Option<usize> {
    let indent = leading_horizontal(source);
    let line = &source[indent..];
    match parent {
        RawFenceParentQuote::Prefix { depth, base } => {
            let facts = quote_marker_facts(line, indent, base)?;
            (!facts.explicit && facts.depth == depth).then_some(indent + facts.marker_len)
        }
    }
}

fn raw_fence_close_facts(
    source: &str,
    parent: Option<RawFenceParentQuote>,
    fence_column: usize,
) -> Option<(usize, usize)> {
    let prefix_len = match parent {
        Some(parent) => exact_raw_fence_prefix_len(source, parent)?,
        None => 0,
    };
    let content = &source[prefix_len..];
    let indent = leading_horizontal(content);
    (indent == fence_column && strict_marker(&content[indent..], "```", true))
        .then_some((prefix_len, indent))
}

fn parse_raw_fence<'source, E, I>(
    io: &mut I,
    indent: usize,
    parent_quote: Option<RawFenceParentQuote>,
) -> RawFenceParse
where
    E: ErrorSink<usize>,
    I: DriverIo<'source, E>,
{
    let start = io.pos();
    let opener_column = start.saturating_sub(io.line().line_start) + indent;
    let fence_column = if matches!(parent_quote, Some(RawFenceParentQuote::Prefix { .. })) {
        indent
    } else {
        opener_column
    };
    io.start_node(SyntaxKind::YmCodeFence);
    if indent > 0 {
        let horizontal = advance_yumark::<E, I>(io, indent);
        io.token(SyntaxKind::Whitespace, horizontal);
    }
    let open = advance_yumark::<E, I>(io, 3);
    io.token(SyntaxKind::YmFenceMarker, open.clone());
    io.push_frame(YumarkFrame::RawFence {
        marker: open.clone(),
        indent: opener_column,
    });
    let (info_len, newline_len) = line_extent(io.remainder());
    io.start_node(SyntaxKind::YmCodeFenceInfo);
    let info = if info_len == 0 {
        io.pos()..io.pos()
    } else {
        let range = advance_yumark::<E, I>(io, info_len);
        io.token(SyntaxKind::YmText, range.clone());
        range
    };
    io.finish_node();
    let opening_newline =
        advance_yumark::<E, I>(io, newline_len.expect("fence opener has newline"));
    io.token(SyntaxKind::Newline, opening_newline.clone());
    let text_start = io.pos();
    loop {
        if io.remainder().is_empty() {
            break;
        }
        if raw_fence_close_facts(io.remainder(), parent_quote, fence_column).is_some() {
            break;
        }
        consume_raw_fence_line::<E, I>(io);
    }
    io.start_node(SyntaxKind::YmCodeFenceText);
    let text = if io.pos() == text_start {
        text_start..text_start
    } else {
        let range = text_start..io.pos();
        io.token(SyntaxKind::YmCodeFenceText, range.clone());
        range
    };
    io.finish_node();
    let close_facts = raw_fence_close_facts(io.remainder(), parent_quote, fence_column);
    let close = if let Some((prefix_len, close_indent)) = close_facts {
        if prefix_len > 0 {
            let prefix = advance_yumark::<E, I>(io, prefix_len);
            io.token(SyntaxKind::YmQuotePrefix, prefix);
        }
        if close_indent > 0 {
            let spaces = advance_yumark::<E, I>(io, close_indent);
            io.token(SyntaxKind::Whitespace, spaces);
        }
        let range = advance_yumark::<E, I>(io, 3);
        io.token(SyntaxKind::YmFenceMarker, range.clone());
        Recovered::Complete(range)
    } else {
        let at = io.pos();
        io.recovery(
            YumarkOwner::CodeFence,
            YumarkSlot::ClosingDelimiter,
            at..at,
            RecoveryKind::Missing,
            ExpectedSyntax::Yumark(YumarkSyntaxEvidence::FenceMarker),
        );
        Recovered::Incomplete
    };
    io.finish_node();
    let _ = io.pop_frame();
    RawFenceParse {
        closed: close_facts.is_some(),
        node: I::RETAIN_AST.then(|| YumarkCodeFence {
            open,
            info,
            opening_newline,
            text,
            close,
            range: start..io.pos(),
        }),
    }
}

fn consume_raw_fence_line<'source, E, I>(io: &mut I)
where
    E: ErrorSink<usize>,
    I: DriverIo<'source, E>,
{
    loop {
        if io.remainder().is_empty() {
            return;
        }
        if let Some(newline) = physical_newline_len(io.remainder()) {
            advance_yumark::<E, I>(io, newline);
            #[cfg(test)]
            io.note_fence_bytes(newline);
            return;
        }
        let length = yumark_source_unit_len(io.remainder()).expect("nonempty raw fence line");
        advance_yumark::<E, I>(io, length);
        #[cfg(test)]
        io.note_fence_bytes(length);
    }
}

fn line_extent(source: &str) -> (usize, Option<usize>) {
    if let Some(index) = source.find('\n') {
        if index > 0 && source.as_bytes()[index - 1] == b'\r' {
            (index - 1, Some(2))
        } else {
            (index, Some(1))
        }
    } else {
        (source.len(), None)
    }
}

fn emit_horizontal_and_newline<'source, E, I>(io: &mut I, length: usize)
where
    E: ErrorSink<usize>,
    I: DriverIo<'source, E>,
{
    let horizontal = leading_horizontal(io.remainder()).min(length);
    if horizontal > 0 {
        let range = advance_yumark::<E, I>(io, horizontal);
        io.token(SyntaxKind::Whitespace, range);
    }
    if horizontal < length {
        let range = advance_yumark::<E, I>(io, length - horizontal);
        io.token(SyntaxKind::Newline, range);
    }
}

fn physical_newline_len(source: &str) -> Option<usize> {
    if source.starts_with("\r\n") {
        Some(2)
    } else if source.starts_with('\n') {
        Some(1)
    } else {
        None
    }
}

fn leading_horizontal(source: &str) -> usize {
    source
        .bytes()
        .take_while(|b| matches!(b, b' ' | b'\t'))
        .count()
}

fn blank_line_len(source: &str) -> Option<usize> {
    let horizontal = leading_horizontal(source);
    physical_newline_len(&source[horizontal..]).map(|nl| horizontal + nl)
}

fn strict_marker(source: &str, marker: &str, eof: bool) -> bool {
    let Some(mut tail) = source.strip_prefix(marker) else {
        return false;
    };
    while let Some(rest) = tail.strip_prefix([' ', '\t']) {
        tail = rest;
    }
    tail.starts_with('\n') || tail.starts_with("\r\n") || (eof && tail.is_empty())
}

fn strict_fence_opener(source: &str) -> bool {
    source.starts_with("```") && line_extent(source).1.is_some()
}

fn heading_marker(source: &str) -> Option<(usize, usize)> {
    let level = source.bytes().take_while(|b| *b == b'#').count();
    (level > 0 && source[level..].starts_with(' ')).then_some((level, level))
}

fn list_marker_len(source: &str) -> Option<usize> {
    if source.starts_with("- ") {
        return Some(2);
    }
    let digits = source.bytes().take_while(|b| b.is_ascii_digit()).count();
    (digits > 0 && source[digits..].starts_with(". ")).then_some(digits + 2)
}
