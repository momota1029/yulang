//! Gate 5 isolated doc-declaration adapters.
//!
//! The envelope follows the authoritative doc-comment addendum §§2–3, while
//! both products are sinks over the single Gate-3/4 driver required by §§4,
//! 8–9, and 11.  The AST sink alone owns structural vectors.  The direct sink
//! streams into one Rowan builder and never constructs or replays that AST.
//! Selected `yulang` fence bodies remain deferred by the later parsed-fence
//! addendum §§1 and 7 and the gap-closure memo §6; an adapter reports that
//! boundary instead of fabricating a raw or embedded body.

use std::ops::Range;

use rowan::{Checkpoint, GreenNode, GreenNodeBuilder};

use crate::cursor::{SyntaxOutput, SyntaxOutputCheckpoint};
use crate::{OperatorTable, SyntaxKind};

use super::{
    grammar::{self, Gate3State, Mode, Recovery, RecoveryOwner, RecoverySlot, Sink},
    judge::{
        BlockCloseContext, BlockCloseDecision, DocumentMarkerKind, StatementPosition,
        judge_block_close, judge_document_marker, judge_line_document,
    },
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum AdapterDeferred {
    /// The parsed-fence addendum reserves this body for O6 convergence.
    SelectedYulangFenceBody { range: Range<usize> },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct AstToken {
    pub(crate) kind: SyntaxKind,
    pub(crate) range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct RecoveryRecord {
    pub(crate) recovery: Recovery,
    pub(crate) range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum AstElement {
    Node(AstNode),
    Token(AstToken),
    Recovery(RecoveryRecord),
}

/// Structural storage shared by the typed §8 AST vocabulary.
///
/// This value exists only in the AST adapter.  The direct adapter has no
/// corresponding node or event buffer.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct AstNode {
    pub(crate) kind: SyntaxKind,
    pub(crate) range: Range<usize>,
    pub(crate) children: Vec<AstElement>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum RecoveredRange {
    Present(Range<usize>),
    Missing { at: usize },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum DocCommentForm {
    Line {
        prefix: Range<usize>,
    },
    Block {
        open: Range<usize>,
        close: RecoveredRange,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct DocCommentDeclarationAst {
    pub(crate) form: DocCommentForm,
    pub(crate) document: YumarkDocument,
    pub(crate) range: Range<usize>,
    pub(crate) recoveries: Vec<RecoveryRecord>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkDocument {
    pub(crate) range: Range<usize>,
    pub(crate) blocks: Vec<YumarkBlock>,
    pub(crate) inlines: Vec<YumarkInline>,
    pub(crate) trivia: Vec<AstToken>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum YumarkBlock {
    BlankLine(AstNode),
    Section(AstNode),
    List(AstNode),
    Quote(AstNode),
    CodeFence(AstNode),
    Paragraph(AstNode),
    Command(YumarkCommand),
    My(YumarkMy),
    Use(YumarkUse),
    IfChain(YumarkIfChain),
    Recovery(RecoveryRecord),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum YumarkInline {
    Text(AstToken),
    Group(AstNode),
    Link(AstNode),
    Image(AstNode),
    Apply(AstNode),
    Reference(AstNode),
    Emphasis(AstNode),
    Strong(AstNode),
    Recovery(RecoveryRecord),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkCommand {
    pub(crate) range: Range<usize>,
    pub(crate) arguments: Vec<AstNode>,
    pub(crate) local_body: Option<AstNode>,
    pub(crate) do_capture: Option<AstNode>,
    pub(crate) structure: AstNode,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkMy {
    pub(crate) range: Range<usize>,
    pub(crate) head: Option<AstNode>,
    pub(crate) body: Option<AstNode>,
    pub(crate) structure: AstNode,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkUse {
    pub(crate) range: Range<usize>,
    pub(crate) structure: AstNode,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkIfChain {
    pub(crate) range: Range<usize>,
    pub(crate) branches: Vec<AstNode>,
    pub(crate) structure: AstNode,
}

pub(crate) struct IsolatedAst<'source> {
    pub(crate) declaration: DocCommentDeclarationAst,
    pub(crate) remainder: &'source str,
    pub(crate) state: Gate3State,
}

pub(crate) struct IsolatedDirect<'source> {
    pub(crate) green: GreenNode,
    pub(crate) recoveries: Vec<RecoveryRecord>,
    pub(crate) range: Range<usize>,
    pub(crate) remainder: &'source str,
    pub(crate) state: Gate3State,
}

#[derive(Clone)]
struct AstCheckpoint {
    depth: usize,
    index: usize,
    position: usize,
}

struct BuildingNode {
    kind: SyntaxKind,
    start: usize,
    children: Vec<AstElement>,
}

#[derive(Default)]
struct AstSink {
    roots: Vec<AstElement>,
    open: Vec<BuildingNode>,
    position: usize,
}

impl AstSink {
    fn current(&self) -> &Vec<AstElement> {
        self.open.last().map_or(&self.roots, |node| &node.children)
    }

    fn current_mut(&mut self) -> &mut Vec<AstElement> {
        self.open
            .last_mut()
            .map_or(&mut self.roots, |node| &mut node.children)
    }

    fn finish(mut self) -> AstNode {
        assert!(self.open.is_empty(), "the AST sink finishes balanced");
        match self.roots.pop() {
            Some(AstElement::Node(node)) if self.roots.is_empty() => node,
            _ => panic!("a doc adapter produces one declaration root"),
        }
    }
}

impl Sink for AstSink {
    type Checkpoint = AstCheckpoint;

    fn checkpoint(&mut self) -> Self::Checkpoint {
        AstCheckpoint {
            depth: self.open.len(),
            index: self.current().len(),
            position: self.position,
        }
    }

    fn enter(&mut self, kind: SyntaxKind) {
        self.open.push(BuildingNode {
            kind,
            start: self.position,
            children: Vec::new(),
        });
    }

    fn token(&mut self, kind: SyntaxKind, range: Range<usize>) {
        self.position = self.position.max(range.end);
        self.current_mut()
            .push(AstElement::Token(AstToken { kind, range }));
    }

    fn exit(&mut self) {
        let node = self.open.pop().expect("an AST Exit has an Enter");
        let end = element_end(&node.children).unwrap_or(self.position.max(node.start));
        self.current_mut().push(AstElement::Node(AstNode {
            kind: node.kind,
            range: node.start..end,
            children: node.children,
        }));
    }

    fn recovery(&mut self, recovery: Recovery, range: Range<usize>) {
        self.position = self.position.max(range.end);
        self.current_mut()
            .push(AstElement::Recovery(RecoveryRecord { recovery, range }));
    }

    fn replace_enter(&mut self, checkpoint: &Self::Checkpoint, kind: SyntaxKind) {
        let node = self
            .open
            .iter_mut()
            .rev()
            .find(|node| node.start == checkpoint.position)
            .expect("replace_enter refers to an open AST node");
        node.kind = kind;
    }

    fn start_enter_at(&mut self, checkpoint: &Self::Checkpoint, kind: SyntaxKind) {
        let index = if self.open.len() == checkpoint.depth {
            checkpoint.index
        } else {
            assert_eq!(self.open.len(), checkpoint.depth + 1);
            self.current()
                .iter()
                .position(|child| element_start(child) >= checkpoint.position)
                .unwrap_or_else(|| self.current().len())
        };
        let children = self.current_mut().split_off(index);
        self.open.push(BuildingNode {
            kind,
            start: checkpoint.position,
            children,
        });
    }
}

fn element_end(children: &[AstElement]) -> Option<usize> {
    children
        .iter()
        .filter_map(|child| match child {
            AstElement::Node(node) => Some(node.range.end),
            AstElement::Token(token) => Some(token.range.end),
            AstElement::Recovery(recovery) => Some(recovery.range.end),
        })
        .max()
}

fn element_start(element: &AstElement) -> usize {
    match element {
        AstElement::Node(node) => node.range.start,
        AstElement::Token(token) => token.range.start,
        AstElement::Recovery(recovery) => recovery.range.start,
    }
}

#[derive(Clone)]
struct DirectCheckpoint {
    checkpoint: Checkpoint,
    depth: usize,
    position: usize,
}

struct DirectSink<'source> {
    source: &'source str,
    builder: GreenNodeBuilder<'static>,
    open: Vec<SyntaxKind>,
    recoveries: Vec<RecoveryRecord>,
    emitted: usize,
    deferred: Option<AdapterDeferred>,
}

#[derive(Clone)]
struct StreamingDirectCheckpoint {
    checkpoint: SyntaxOutputCheckpoint,
    depth: usize,
    position: usize,
}

struct StreamingDirectSink<'source, 'output> {
    source: &'source str,
    output: &'output mut dyn SyntaxOutput,
    depth: usize,
    emitted: usize,
    deferred: Option<AdapterDeferred>,
}

impl<'source, 'output> StreamingDirectSink<'source, 'output> {
    fn new(source: &'source str, output: &'output mut dyn SyntaxOutput) -> Self {
        Self {
            source,
            output,
            depth: 0,
            emitted: 0,
            deferred: None,
        }
    }

    fn defer_gap(&mut self, end: usize) {
        if self.deferred.is_none() {
            self.deferred = Some(AdapterDeferred::SelectedYulangFenceBody {
                range: self.emitted..end,
            });
        }
    }

    fn publish_recovery(
        &mut self,
        checkpoint: Option<&StreamingDirectCheckpoint>,
        recovery: Recovery,
        range: Range<usize>,
    ) {
        match recovery.kind {
            SyntaxKind::Missing => {
                if range.start != self.emitted {
                    self.defer_gap(range.start);
                    return;
                }
                self.output.start_node(SyntaxKind::Missing.into());
                self.output.finish_node();
            }
            SyntaxKind::Error if range.start < self.emitted => {
                let Some(checkpoint) = checkpoint.filter(|checkpoint| {
                    checkpoint.position == range.start
                        && (checkpoint.depth == self.depth || checkpoint.depth + 1 == self.depth)
                }) else {
                    self.defer_gap(range.end);
                    return;
                };
                self.output
                    .start_node_at(&checkpoint.checkpoint, SyntaxKind::Error.into());
                self.output.finish_node();
            }
            SyntaxKind::Error => {
                if range.start > self.emitted {
                    self.defer_gap(range.start);
                    return;
                }
                self.output.start_node(SyntaxKind::Error.into());
                if !range.is_empty() {
                    self.output
                        .token(SyntaxKind::Error.into(), &self.source[range.clone()]);
                    self.emitted = range.end;
                }
                self.output.finish_node();
            }
            kind => panic!("unexpected Yumark recovery kind {kind:?}"),
        }
    }
}

impl Sink for StreamingDirectSink<'_, '_> {
    type Checkpoint = StreamingDirectCheckpoint;

    fn checkpoint(&mut self) -> Self::Checkpoint {
        StreamingDirectCheckpoint {
            checkpoint: self.output.checkpoint(),
            depth: self.depth,
            position: self.emitted,
        }
    }

    fn enter(&mut self, kind: SyntaxKind) {
        self.output.start_node(kind.into());
        self.depth += 1;
    }

    fn token(&mut self, kind: SyntaxKind, range: Range<usize>) {
        if range.start > self.emitted {
            self.defer_gap(range.start);
        }
        if range.end <= self.emitted {
            return;
        }
        let start = range.start.max(self.emitted);
        self.output
            .token(kind.into(), &self.source[start..range.end]);
        self.emitted = range.end;
    }

    fn exit(&mut self) {
        self.depth = self
            .depth
            .checked_sub(1)
            .expect("a direct Exit has an Enter");
        self.output.finish_node();
    }

    fn recovery(&mut self, recovery: Recovery, range: Range<usize>) {
        self.publish_recovery(None, recovery, range);
    }

    fn recovery_at(
        &mut self,
        checkpoint: &Self::Checkpoint,
        recovery: Recovery,
        range: Range<usize>,
    ) {
        self.publish_recovery(Some(checkpoint), recovery, range);
    }

    fn replace_enter(&mut self, _: &Self::Checkpoint, _: SyntaxKind) {
        unreachable!("Gate 6 uses start_node_at for every postclassified owner")
    }

    fn start_enter_at(&mut self, checkpoint: &Self::Checkpoint, kind: SyntaxKind) {
        self.output
            .start_node_at(&checkpoint.checkpoint, kind.into());
        self.depth += 1;
    }
}

fn parse_document_direct(
    source: &str,
    mode: Mode,
    document_base_col: usize,
    operators: &OperatorTable,
    output: &mut dyn SyntaxOutput,
) -> Result<Gate3State, AdapterDeferred> {
    let mut sink = StreamingDirectSink::new(source, output);
    let state =
        grammar::parse_at_document_base(source, mode, document_base_col, operators, &mut sink);
    assert_eq!(sink.depth, 0, "the direct Yumark sink finishes balanced");
    if let Some(deferred) = sink.deferred {
        Err(deferred)
    } else {
        Ok(state)
    }
}

pub(crate) fn parse_line_document_direct(
    source: &str,
    operators: &OperatorTable,
    output: &mut dyn SyntaxOutput,
) -> Result<Gate3State, AdapterDeferred> {
    parse_document_direct(source, Mode::Line, 0, operators, output)
}

pub(crate) fn parse_block_document_direct(
    source: &str,
    document_base_col: usize,
    operators: &OperatorTable,
    output: &mut dyn SyntaxOutput,
) -> Result<Gate3State, AdapterDeferred> {
    parse_document_direct(
        source,
        Mode::BlockDocument,
        document_base_col,
        operators,
        output,
    )
}

impl<'source> DirectSink<'source> {
    fn new(source: &'source str) -> Self {
        Self {
            source,
            builder: GreenNodeBuilder::new(),
            open: Vec::new(),
            recoveries: Vec::new(),
            emitted: 0,
            deferred: None,
        }
    }

    fn output_checkpoint(&self) -> DirectCheckpoint {
        DirectCheckpoint {
            checkpoint: self.builder.checkpoint(),
            depth: self.open.len(),
            position: self.emitted,
        }
    }

    fn defer_gap(&mut self, end: usize) {
        if self.deferred.is_none() {
            self.deferred = Some(AdapterDeferred::SelectedYulangFenceBody {
                range: self.emitted..end,
            });
        }
    }

    fn finish(self) -> Result<(GreenNode, Vec<RecoveryRecord>), AdapterDeferred> {
        if let Some(deferred) = self.deferred {
            return Err(deferred);
        }
        assert!(self.open.is_empty(), "the direct sink finishes balanced");
        Ok((self.builder.finish(), self.recoveries))
    }

    fn publish_recovery(
        &mut self,
        checkpoint: Option<&DirectCheckpoint>,
        recovery: Recovery,
        range: Range<usize>,
    ) {
        self.recoveries.push(RecoveryRecord {
            recovery,
            range: range.clone(),
        });
        match recovery.kind {
            SyntaxKind::Missing => {
                if range.start != self.emitted {
                    self.defer_gap(range.start);
                    return;
                }
                self.builder.start_node(SyntaxKind::Missing.into());
                self.builder.finish_node();
            }
            SyntaxKind::Error if range.start < self.emitted => {
                let Some(checkpoint) = checkpoint.filter(|checkpoint| {
                    checkpoint.position == range.start
                        && (checkpoint.depth == self.open.len()
                            || checkpoint.depth + 1 == self.open.len())
                }) else {
                    self.defer_gap(range.end);
                    return;
                };
                self.builder
                    .start_node_at(checkpoint.checkpoint, SyntaxKind::Error.into());
                self.builder.finish_node();
            }
            SyntaxKind::Error => {
                if range.start > self.emitted {
                    self.defer_gap(range.start);
                    return;
                }
                self.builder.start_node(SyntaxKind::Error.into());
                if !range.is_empty() {
                    self.builder
                        .token(SyntaxKind::Error.into(), &self.source[range.clone()]);
                    self.emitted = range.end;
                }
                self.builder.finish_node();
            }
            kind => panic!("unexpected Yumark recovery kind {kind:?}"),
        }
    }
}

impl Sink for DirectSink<'_> {
    type Checkpoint = DirectCheckpoint;

    fn checkpoint(&mut self) -> Self::Checkpoint {
        self.output_checkpoint()
    }

    fn enter(&mut self, kind: SyntaxKind) {
        self.builder.start_node(kind.into());
        self.open.push(kind);
    }

    fn token(&mut self, kind: SyntaxKind, range: Range<usize>) {
        if range.start > self.emitted {
            self.defer_gap(range.start);
        }
        if range.end <= self.emitted {
            return;
        }
        let start = range.start.max(self.emitted);
        self.builder
            .token(kind.into(), &self.source[start..range.end]);
        self.emitted = range.end;
    }

    fn exit(&mut self) {
        self.open.pop().expect("a direct Exit has an Enter");
        self.builder.finish_node();
    }

    fn recovery(&mut self, recovery: Recovery, range: Range<usize>) {
        self.publish_recovery(None, recovery, range);
    }

    fn recovery_at(
        &mut self,
        checkpoint: &Self::Checkpoint,
        recovery: Recovery,
        range: Range<usize>,
    ) {
        self.publish_recovery(Some(checkpoint), recovery, range);
    }

    fn replace_enter(&mut self, _: &Self::Checkpoint, _: SyntaxKind) {
        unreachable!("Gate 5 uses start_node_at for every postclassified owner")
    }

    fn start_enter_at(&mut self, checkpoint: &Self::Checkpoint, kind: SyntaxKind) {
        self.builder
            .start_node_at(checkpoint.checkpoint, kind.into());
        self.open.push(kind);
    }
}

struct OffsetSink<'sink, S> {
    base: usize,
    sink: &'sink mut S,
}

impl<S: Sink> Sink for OffsetSink<'_, S> {
    type Checkpoint = S::Checkpoint;

    fn checkpoint(&mut self) -> Self::Checkpoint {
        self.sink.checkpoint()
    }
    fn enter(&mut self, kind: SyntaxKind) {
        self.sink.enter(kind);
    }
    fn token(&mut self, kind: SyntaxKind, range: Range<usize>) {
        self.sink
            .token(kind, range.start + self.base..range.end + self.base);
    }
    fn exit(&mut self) {
        self.sink.exit();
    }
    fn recovery(&mut self, recovery: Recovery, range: Range<usize>) {
        self.sink
            .recovery(recovery, range.start + self.base..range.end + self.base);
    }
    fn recovery_at(
        &mut self,
        checkpoint: &Self::Checkpoint,
        recovery: Recovery,
        range: Range<usize>,
    ) {
        self.sink.recovery_at(
            checkpoint,
            recovery,
            range.start + self.base..range.end + self.base,
        );
    }
    fn replace_enter(&mut self, checkpoint: &Self::Checkpoint, kind: SyntaxKind) {
        self.sink.replace_enter(checkpoint, kind);
    }
    fn start_enter_at(&mut self, checkpoint: &Self::Checkpoint, kind: SyntaxKind) {
        self.sink.start_enter_at(checkpoint, kind);
    }
}

struct EnvelopeResult {
    form: DocCommentForm,
    range: Range<usize>,
    state: Gate3State,
}

fn drive<S: Sink>(source: &str, operators: &OperatorTable, sink: &mut S) -> Option<EnvelopeResult>
where
    S::Checkpoint: 'static,
{
    let marker = judge_document_marker(
        source,
        0,
        StatementPosition::CanonicalLineStart { base_col: 0 },
    )?;
    sink.enter(SyntaxKind::DocCommentDeclaration);
    match marker.kind {
        DocumentMarkerKind::Line => {
            let extent = judge_line_document(source, 0).expect("the line marker was accepted");
            sink.token(SyntaxKind::DocLinePrefix, extent.prefix.clone());
            let mut offset = OffsetSink {
                base: extent.body.start,
                sink,
            };
            let state = grammar::parse(
                &source[extent.body.clone()],
                Mode::Line,
                operators,
                &mut offset,
            );
            sink.exit();
            Some(EnvelopeResult {
                form: DocCommentForm::Line {
                    prefix: extent.prefix,
                },
                range: 0..extent.body.end,
                state,
            })
        }
        DocumentMarkerKind::BlockOpen => {
            let (content_end, opening_end) = first_physical_line(source)
                .expect("a strict block opener always has a physical newline");
            sink.token(SyntaxKind::DocBlockOpen, marker.range.clone());
            if marker.range.end < content_end {
                sink.token(SyntaxKind::Whitespace, marker.range.end..content_end);
            }
            sink.token(SyntaxKind::Newline, content_end..opening_end);
            let state = {
                let mut offset = OffsetSink {
                    base: opening_end,
                    sink,
                };
                grammar::parse(
                    &source[opening_end..],
                    Mode::BlockDocument,
                    operators,
                    &mut offset,
                )
            };
            let close_start = opening_end + state.consumed;
            let close = judge_block_close(
                &source[close_start..],
                close_start,
                BlockCloseContext {
                    after_opening_line: true,
                    at_physical_line_start: true,
                    indent_col: 0,
                    base_col: 0,
                },
            );
            let (close, end) = match close {
                BlockCloseDecision::Close(range) => {
                    sink.token(SyntaxKind::DocBlockClose, range.clone());
                    let end = range.end;
                    (RecoveredRange::Present(range), end)
                }
                BlockCloseDecision::MissingDocCommentClosingDelimiter { range } => {
                    sink.recovery(
                        Recovery {
                            kind: SyntaxKind::Missing,
                            owner: RecoveryOwner::DocComment,
                            slot: RecoverySlot::ClosingDelimiter,
                        },
                        range.clone(),
                    );
                    (RecoveredRange::Missing { at: range.start }, range.start)
                }
                BlockCloseDecision::Text => {
                    debug_assert_eq!(close_start, source.len());
                    sink.recovery(
                        Recovery {
                            kind: SyntaxKind::Missing,
                            owner: RecoveryOwner::DocComment,
                            slot: RecoverySlot::ClosingDelimiter,
                        },
                        close_start..close_start,
                    );
                    (RecoveredRange::Missing { at: close_start }, close_start)
                }
            };
            sink.exit();
            Some(EnvelopeResult {
                form: DocCommentForm::Block {
                    open: marker.range,
                    close,
                },
                range: 0..end,
                state,
            })
        }
    }
}

fn first_physical_line(source: &str) -> Option<(usize, usize)> {
    let lf = source.find('\n')?;
    let content_end = lf - usize::from(lf > 0 && source.as_bytes()[lf - 1] == b'\r');
    Some((content_end, lf + 1))
}

pub(crate) fn parse_ast<'source>(
    source: &'source str,
    operators: &OperatorTable,
) -> Option<Result<IsolatedAst<'source>, AdapterDeferred>> {
    let mut sink = AstSink::default();
    let envelope = drive(source, operators, &mut sink)?;
    let root = sink.finish();
    let covered = token_ranges(&root);
    if let Some(gap) = first_gap(&covered, envelope.range.clone()) {
        return Some(Err(AdapterDeferred::SelectedYulangFenceBody { range: gap }));
    }
    let document_node = root
        .children
        .iter()
        .find_map(|child| match child {
            AstElement::Node(node) if node.kind == SyntaxKind::YmDoc => Some(node.clone()),
            _ => None,
        })
        .expect("a doc declaration owns one Yumark document");
    let recoveries = collect_recoveries(&root);
    let declaration = DocCommentDeclarationAst {
        form: envelope.form,
        document: document(document_node),
        range: envelope.range.clone(),
        recoveries,
    };
    Some(Ok(IsolatedAst {
        declaration,
        remainder: &source[envelope.range.end..],
        state: envelope.state,
    }))
}

pub(crate) fn parse_direct<'source>(
    source: &'source str,
    operators: &OperatorTable,
) -> Option<Result<IsolatedDirect<'source>, AdapterDeferred>> {
    let mut sink = DirectSink::new(source);
    let envelope = drive(source, operators, &mut sink)?;
    let range = envelope.range.clone();
    Some(sink.finish().map(|(green, recoveries)| IsolatedDirect {
        green,
        recoveries,
        range: range.clone(),
        remainder: &source[range.end..],
        state: envelope.state,
    }))
}

fn document(node: AstNode) -> YumarkDocument {
    let mut blocks = Vec::new();
    let mut inlines = Vec::new();
    let mut trivia = Vec::new();
    for child in &node.children {
        match child {
            AstElement::Token(token) if token.kind == SyntaxKind::YmText => {
                inlines.push(YumarkInline::Text(token.clone()));
            }
            AstElement::Token(token) => trivia.push(token.clone()),
            AstElement::Recovery(recovery) => {
                blocks.push(YumarkBlock::Recovery(recovery.clone()));
                inlines.push(YumarkInline::Recovery(recovery.clone()));
            }
            AstElement::Node(child) => match child.kind {
                SyntaxKind::YmBlankLine => blocks.push(YumarkBlock::BlankLine(child.clone())),
                SyntaxKind::YmSection => blocks.push(YumarkBlock::Section(child.clone())),
                SyntaxKind::YmList => blocks.push(YumarkBlock::List(child.clone())),
                SyntaxKind::YmQuoteBlock => blocks.push(YumarkBlock::Quote(child.clone())),
                SyntaxKind::YmCodeFence => blocks.push(YumarkBlock::CodeFence(child.clone())),
                SyntaxKind::YmParagraph => blocks.push(YumarkBlock::Paragraph(child.clone())),
                SyntaxKind::YmCommand => blocks.push(YumarkBlock::Command(command(child.clone()))),
                SyntaxKind::YmMy => blocks.push(YumarkBlock::My(my(child.clone()))),
                SyntaxKind::YmUse => blocks.push(YumarkBlock::Use(YumarkUse {
                    range: child.range.clone(),
                    structure: child.clone(),
                })),
                SyntaxKind::YmIfChain => blocks.push(YumarkBlock::IfChain(if_chain(child.clone()))),
                SyntaxKind::YmInlineGroup => inlines.push(YumarkInline::Group(child.clone())),
                SyntaxKind::YmInlineLink => inlines.push(YumarkInline::Link(child.clone())),
                SyntaxKind::YmInlineImage => inlines.push(YumarkInline::Image(child.clone())),
                SyntaxKind::YmInlineApply => inlines.push(YumarkInline::Apply(child.clone())),
                SyntaxKind::YmInlineRef => inlines.push(YumarkInline::Reference(child.clone())),
                SyntaxKind::YmEmphasis => inlines.push(YumarkInline::Emphasis(child.clone())),
                SyntaxKind::YmStrong => inlines.push(YumarkInline::Strong(child.clone())),
                _ => {}
            },
        }
    }
    YumarkDocument {
        range: node.range,
        blocks,
        inlines,
        trivia,
    }
}

fn command(node: AstNode) -> YumarkCommand {
    let arguments = child_nodes(&node, SyntaxKind::YmCommandArgs);
    let local_body = first_child(&node, SyntaxKind::YmCommandBody);
    let do_capture = first_child(&node, SyntaxKind::YmDoCapture);
    YumarkCommand {
        range: node.range.clone(),
        arguments,
        local_body,
        do_capture,
        structure: node,
    }
}

fn my(node: AstNode) -> YumarkMy {
    YumarkMy {
        range: node.range.clone(),
        head: first_child(&node, SyntaxKind::YmMyBindingHead),
        body: first_child(&node, SyntaxKind::YmMyExpressionBody)
            .or_else(|| first_child(&node, SyntaxKind::YmCommandBody)),
        structure: node,
    }
}

fn if_chain(node: AstNode) -> YumarkIfChain {
    let branches = node
        .children
        .iter()
        .filter_map(|child| match child {
            AstElement::Node(child)
                if matches!(
                    child.kind,
                    SyntaxKind::YmIf | SyntaxKind::YmElsif | SyntaxKind::YmElse
                ) =>
            {
                Some(child.clone())
            }
            _ => None,
        })
        .collect();
    YumarkIfChain {
        range: node.range.clone(),
        branches,
        structure: node,
    }
}

fn child_nodes(node: &AstNode, kind: SyntaxKind) -> Vec<AstNode> {
    node.children
        .iter()
        .filter_map(|child| match child {
            AstElement::Node(child) if child.kind == kind => Some(child.clone()),
            _ => None,
        })
        .collect()
}

fn first_child(node: &AstNode, kind: SyntaxKind) -> Option<AstNode> {
    child_nodes(node, kind).into_iter().next()
}

fn collect_recoveries(node: &AstNode) -> Vec<RecoveryRecord> {
    let mut recoveries = Vec::new();
    fn visit(node: &AstNode, out: &mut Vec<RecoveryRecord>) {
        for child in &node.children {
            match child {
                AstElement::Node(child) => visit(child, out),
                AstElement::Recovery(recovery) => out.push(recovery.clone()),
                AstElement::Token(_) => {}
            }
        }
    }
    visit(node, &mut recoveries);
    recoveries
}

fn token_ranges(node: &AstNode) -> Vec<Range<usize>> {
    let mut ranges = Vec::new();
    fn visit(node: &AstNode, out: &mut Vec<Range<usize>>) {
        for child in &node.children {
            match child {
                AstElement::Node(child) => visit(child, out),
                AstElement::Token(token) => out.push(token.range.clone()),
                AstElement::Recovery(recovery) if !recovery.range.is_empty() => {
                    out.push(recovery.range.clone());
                }
                AstElement::Recovery(_) => {}
            }
        }
    }
    visit(node, &mut ranges);
    ranges.sort_by_key(|range| (range.start, range.end));
    ranges
}

fn first_gap(ranges: &[Range<usize>], envelope: Range<usize>) -> Option<Range<usize>> {
    let mut end = envelope.start;
    for range in ranges {
        if range.end <= end {
            continue;
        }
        if range.start > end {
            return Some(end..range.start);
        }
        end = range.end;
    }
    (end < envelope.end).then_some(end..envelope.end)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{GrammarSlotRole, SyntaxNode, structural_diagnostic};

    fn products(source: &str) -> (IsolatedAst<'_>, IsolatedDirect<'_>) {
        let operators = OperatorTable::empty();
        let ast = parse_ast(source, &operators)
            .expect("accepted doc marker")
            .unwrap_or_else(|deferred| panic!("{source:?}: {deferred:?}"));
        let direct = parse_direct(source, &operators)
            .expect("accepted doc marker")
            .unwrap_or_else(|deferred| panic!("{source:?}: {deferred:?}"));
        (ast, direct)
    }

    fn direct_kinds(green: &GreenNode) -> Vec<SyntaxKind> {
        let root = SyntaxNode::new_root(green.clone());
        std::iter::once(root.kind())
            .chain(root.descendants().skip(1).map(|node| node.kind()))
            .filter(|kind| {
                !matches!(
                    kind,
                    SyntaxKind::Missing | SyntaxKind::Error | SyntaxKind::Invalid
                )
            })
            .collect()
    }

    fn ast_kinds(node: &AstNode, out: &mut Vec<SyntaxKind>) {
        out.push(node.kind);
        for child in &node.children {
            if let AstElement::Node(child) = child {
                ast_kinds(child, out);
            }
        }
    }

    #[test]
    fn line_and_block_envelopes_are_lossless_and_return_the_exact_remainder() {
        for (source, expected_range, expected_remainder) in [
            ("--[x]:bold\nnext", 0..10, "\nnext"),
            ("---\r\n# H\r\n---  \r\nnext", 0..13, "  \r\nnext"),
            ("---\nbody", 0..8, ""),
        ] {
            let (ast, direct) = products(source);
            assert_eq!(ast.declaration.range, expected_range, "{source:?}");
            assert_eq!(direct.range, expected_range, "{source:?}");
            assert_eq!(ast.remainder, expected_remainder, "{source:?}");
            assert_eq!(direct.remainder, expected_remainder, "{source:?}");
            let root = SyntaxNode::new_root(direct.green.clone());
            assert_eq!(root.text().to_string(), source[expected_range].to_owned());
            assert_eq!(direct.state.frame_depth, 0);
        }
    }

    #[test]
    fn nonembedded_ast_and_direct_structures_are_equal_for_the_gate5_surface() {
        for source in [
            "--*em* **strong** [g] [l](d) ![i](s) [a]:op",
            "---\n# H\n- item\n> quote\n```rust\nraw\n```\n---",
            "---\n\\cmd[doc](x){body}\n\\my f = x;\n\\use route;\n---",
            "---\n\\cmd(x){body}\n\\wrap(do)\nafter\n---",
            "---\n\\if(x){one}\n\\elsif(y):\n  two\n\\else{three}\n---",
        ] {
            let (ast, direct) = products(source);
            let operators = OperatorTable::empty();
            let mut sink = AstSink::default();
            drive(source, &operators, &mut sink).expect("accepted doc");
            let root = sink.finish();
            let mut ast_actual = Vec::new();
            ast_kinds(&root, &mut ast_actual);
            let direct_actual = direct_kinds(&direct.green);
            assert_eq!(ast_actual, direct_actual, "{source:?}");
            assert_eq!(ast.declaration.recoveries, direct.recoveries, "{source:?}");
        }
    }

    #[test]
    fn recovery_identity_range_order_and_eof_missing_are_shared() {
        for source in [
            "--![alt] *open",
            "---\n#.\n\\wrap(do x\n---",
            "---\n\\else(x){body}\n---",
            "---\n>>>\n> mixed\n>>>\n---",
            "---\n```txt\nbody",
        ] {
            let (ast, direct) = products(source);
            assert_eq!(ast.declaration.recoveries, direct.recoveries, "{source:?}");
            assert!(!direct.recoveries.is_empty(), "{source:?}");
            let root = SyntaxNode::new_root(direct.green.clone());
            assert_eq!(root.text().to_string(), source[direct.range].to_owned());
            let diagnostics = structural_diagnostic::collect(&root);
            assert_eq!(diagnostics.len(), direct.recoveries.len(), "{source:?}");
        }

        let (ast, direct) = products("---\nbody");
        let expected = RecoveryRecord {
            recovery: Recovery {
                kind: SyntaxKind::Missing,
                owner: RecoveryOwner::DocComment,
                slot: RecoverySlot::ClosingDelimiter,
            },
            range: 8..8,
        };
        assert_eq!(ast.declaration.recoveries.last(), Some(&expected));
        assert_eq!(direct.recoveries.last(), Some(&expected));
        let root = SyntaxNode::new_root(direct.green);
        let diagnostic = structural_diagnostic::collect(&root)
            .into_iter()
            .last()
            .expect("EOF Missing diagnostic");
        assert_eq!(
            diagnostic
                .identity()
                .slot()
                .expect("mapped Yumark slot")
                .role(),
            GrammarSlotRole::ClosingDelimiter,
        );
    }

    #[test]
    fn rejected_marker_is_state_and_output_neutral() {
        let operators = OperatorTable::empty();
        assert!(parse_ast("---x\n", &operators).is_none());
        assert!(parse_direct("---x\n", &operators).is_none());
        assert!(parse_ast("ordinary", &operators).is_none());
        assert!(parse_direct("ordinary", &operators).is_none());
    }

    #[test]
    fn selected_yulang_fence_is_explicitly_deferred_without_fabricated_body() {
        let source = "---\n```yulang\nmy x = 1\n```\n---";
        let operators = OperatorTable::empty();
        assert!(matches!(
            parse_ast(source, &operators),
            Some(Err(AdapterDeferred::SelectedYulangFenceBody { .. }))
        ));
        assert!(matches!(
            parse_direct(source, &operators),
            Some(Err(AdapterDeferred::SelectedYulangFenceBody { .. }))
        ));
    }

    #[test]
    fn embedded_canonical_recovery_uses_the_current_direct_transport_only() {
        let source = "--\\ref(x[,a])";
        let (ast, direct) = products(source);
        assert!(
            ast.declaration.recoveries.is_empty(),
            "O6 owns embedded AST facts"
        );
        assert!(
            direct.recoveries.is_empty(),
            "the wrapper adds no duplicate"
        );

        let root = SyntaxNode::new_root(direct.green);
        let diagnostics = structural_diagnostic::collect(&root);
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].range(), &(9..9));
        let slot = diagnostics[0]
            .identity()
            .slot()
            .expect("canonical IndexItem is already in the current transport");
        assert_eq!(slot.owner(), SyntaxKind::IndexTail);
        assert_eq!(slot.role(), GrammarSlotRole::Item);
    }

    #[test]
    fn static_driver_evidence_has_no_opaque_scan_replay_or_ast_in_direct_sink() {
        let adapter = include_str!("adapter.rs");
        for name in [
            "scan_opaque_body",
            "scan_raw_yumark_fence_body",
            "scan_yulang_fence_body",
            "parse_root",
        ] {
            let call = format!("{name}(");
            assert!(!adapter.contains(&call), "forbidden path {call}");
        }
        let direct = adapter
            .split("struct DirectSink")
            .nth(1)
            .expect("direct sink source")
            .split("struct OffsetSink")
            .next()
            .expect("bounded direct sink source");
        assert!(!direct.contains("DocCommentDeclarationAst {"));
        assert!(!direct.contains("YumarkDocument {"));
    }
}
