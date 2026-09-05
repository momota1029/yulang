//! Immutable parse context and rollback-owned scanner/layout state.

use std::{ops::Range, sync::Arc};

use chasa::{
    Back, ErrorSink,
    error::std::{Unexpected, UnexpectedEndOfInput},
    prelude::In,
};

use crate::{
    HeaderInfo,
    input::SourceInput,
    operator::OperatorTable,
    parse::SyntaxEnvironment,
    scan::{
        trivia::{TriviaRun, scan_trivia},
        word::scan_word,
    },
    sink::RowanSink,
    syntax_kind::SyntaxKind,
};

/// One delimiter-owned layout boundary frame.
///
/// The base is fixed immediately after the opener's maximal trivia run.  It
/// is intentionally independent of the first item so nested containers and
/// recovery cannot accidentally recalculate it from later source.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct LayoutDelimitedFrame {
    base_indent: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum LayoutDelimitedBoundary {
    ImplicitNewline,
    DeeperNewline,
    None,
}

impl LayoutDelimitedFrame {
    pub(crate) fn after_opening_trivia(
        incoming_base: usize,
        trivia: &TriviaRun,
        following_indent: usize,
    ) -> Self {
        let base_indent = if trivia_has_physical_newline(trivia) && following_indent > incoming_base
        {
            following_indent
        } else {
            incoming_base
        };
        Self { base_indent }
    }

    pub(crate) fn inline(incoming_base: usize) -> Self {
        Self {
            base_indent: incoming_base,
        }
    }

    pub(crate) fn base_indent(self) -> usize {
        self.base_indent
    }

    pub(crate) fn boundary_after_trivia(
        self,
        trivia: &TriviaRun,
        following_indent: usize,
    ) -> LayoutDelimitedBoundary {
        if !trivia_has_physical_newline(trivia) {
            LayoutDelimitedBoundary::None
        } else if following_indent <= self.base_indent {
            LayoutDelimitedBoundary::ImplicitNewline
        } else {
            LayoutDelimitedBoundary::DeeperNewline
        }
    }
}

fn trivia_has_physical_newline(trivia: &TriviaRun) -> bool {
    trivia
        .parts()
        .iter()
        .any(|part| matches!(part.kind(), crate::scan::trivia::TriviaPartKind::Newline))
}

pub(crate) type SynIn<'a, 'source, 'b, E> = In<'a, SourceInput<'source>, (), &'b mut ParseLocal, E>;

/// The chasa input made available to shared grammar recognition.
pub(crate) type GrammarInput<'a, 'source, 'b, E> = SynIn<'a, 'source, 'b, E>;

/// Data selected before parsing and never mutated by speculative branches.
pub(crate) struct ParseEnv<'source, 'context> {
    source: &'source str,
    mode: ParseMode,
    syntax_environment: Option<&'context SyntaxEnvironment>,
    operators: Option<&'context OperatorTable>,
    header: Option<&'context HeaderInfo>,
}

impl<'source> ParseEnv<'source, 'static> {
    pub(crate) fn header(source: &'source str) -> Self {
        Self {
            source,
            mode: ParseMode::Header,
            syntax_environment: None,
            operators: None,
            header: None,
        }
    }
}

impl<'source, 'context> ParseEnv<'source, 'context> {
    pub(crate) fn full(
        source: &'source str,
        syntax_environment: &'context SyntaxEnvironment,
        operators: &'context OperatorTable,
        header: &'context HeaderInfo,
    ) -> Self {
        Self {
            source,
            mode: ParseMode::Full,
            syntax_environment: Some(syntax_environment),
            operators: Some(operators),
            header: Some(header),
        }
    }

    pub(crate) fn source(&self) -> &'source str {
        self.source
    }

    pub(crate) fn mode(&self) -> ParseMode {
        self.mode
    }

    pub(crate) fn syntax_environment(&self) -> Option<&'context SyntaxEnvironment> {
        self.syntax_environment
    }

    pub(crate) fn operators(&self) -> Option<&'context OperatorTable> {
        self.operators
    }

    pub(crate) fn header_info(&self) -> Option<&'context HeaderInfo> {
        self.header
    }
}

/// Whether shared grammar is discovering a header or building a full CST.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ParseMode {
    Header,
    Full,
}

/// One statement-owner scope visible to nested continuation and list judges.
///
/// This is deliberately separate from delimiter, stop, and indentation stacks:
/// braced statement owners hide outer statement baselines and If companions,
/// while ordinary delimiters keep the ambient owner visible.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct AmbientOwnerScopeFrame {
    kind: AmbientOwnerScopeKind,
    statement_baseline: Option<usize>,
    if_visibility_floor: Option<usize>,
}

impl AmbientOwnerScopeFrame {
    pub(crate) fn root_statement() -> Self {
        Self {
            kind: AmbientOwnerScopeKind::RootStatement,
            statement_baseline: Some(0),
            if_visibility_floor: None,
        }
    }

    pub(crate) fn indented_statement(statement_baseline: usize) -> Self {
        Self {
            kind: AmbientOwnerScopeKind::IndentedStatement,
            statement_baseline: Some(statement_baseline),
            if_visibility_floor: None,
        }
    }

    pub(crate) fn braced_barrier(origin: BracedBarrierOrigin, if_visibility_floor: usize) -> Self {
        Self {
            kind: AmbientOwnerScopeKind::BracedBarrier(origin),
            statement_baseline: None,
            if_visibility_floor: Some(if_visibility_floor),
        }
    }

    pub(crate) fn inline_canonical_statement(owner: InlineStatementOwnerKind) -> Self {
        Self {
            kind: AmbientOwnerScopeKind::InlineCanonicalStatement(owner),
            statement_baseline: None,
            if_visibility_floor: None,
        }
    }

    pub(crate) fn kind(self) -> AmbientOwnerScopeKind {
        self.kind
    }

    pub(crate) fn statement_baseline(self) -> Option<usize> {
        self.statement_baseline
    }

    pub(crate) fn if_visibility_floor(self) -> Option<usize> {
        self.if_visibility_floor
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum AmbientOwnerScopeKind {
    RootStatement,
    IndentedStatement,
    BracedBarrier(BracedBarrierOrigin),
    InlineCanonicalStatement(InlineStatementOwnerKind),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum BracedBarrierOrigin {
    BracedStatementBlockExpression,
    CatchBracedArmSequence,
    DeclarationCompanion,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum InlineStatementOwnerKind {
    WithBodyTail,
    ModColonBody,
    ImplColonBody,
    RoleColonBody,
    ActColonBody,
    DeclarationCompanion,
}

/// Identity for one complete IfExpression companion lifetime.
///
/// The raw counter stays private so callers can compare ownership without
/// erasing a matching frame to an existential boolean.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct IfExpressionCompanionId(u32);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct IfExpressionCompanionFrame {
    id: IfExpressionCompanionId,
    if_base_indent: usize,
    exact_words: &'static [&'static str],
}

/// One explicit work item in the iterative Yumark grammar.
///
/// The stack is inert until the isolated grammar gates begin. Keeping every
/// structural nesting form explicit here prevents later parser recursion from
/// becoming the accidental depth policy.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum YumarkFrame {
    Document {
        base: usize,
        envelope_stop: YumarkEnvelopeStop,
    },
    Inline {
        owner: YumarkOwner,
        close: YumarkInlineClose,
    },
    ImplicitSection {
        level: usize,
    },
    ExplicitSection {
        level: usize,
        parent_indent: usize,
        body_indent: usize,
    },
    List {
        indent: usize,
    },
    ListItem {
        marker: Range<usize>,
        indent: usize,
        content_column: usize,
    },
    ExplicitQuote {
        depth: usize,
        marker: Range<usize>,
    },
    PrefixQuote {
        depth: usize,
    },
    RawFence {
        marker: Range<usize>,
        indent: usize,
    },
    BracedBody {
        owner: YumarkOwner,
    },
    IndentedBody {
        owner: YumarkOwner,
        parent_indent: usize,
        body_indent: usize,
    },
    DoCapture {
        command_start: usize,
        indent: usize,
    },
    IfChain {
        indent: usize,
        seen_else: bool,
    },
    EmbeddedYulang {
        owner: YumarkOwner,
        outer_kind: YumarkEmbeddedOuterKind,
        delimiter_floor: YumarkDelimiterFloor,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum YumarkEnvelopeStop {
    LineDocument,
    BlockDocument,
    ParentFrame,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum YumarkInlineClose {
    RightBracket,
    Emphasis,
    Strong,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum YumarkEmbeddedOuterKind {
    Paired(Delimiter),
    RequiredSemicolon,
}

/// The exact canonical delimiter depth borrowed by one Yumark wrapper.
///
/// The value stays opaque outside session ownership: Yumark can test and pop
/// only the floor returned by its matching push operation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct YumarkDelimiterFloor(usize);

/// One canonical recovery committed while a Yumark-owned embedded episode is
/// active. The enclosing AST adapter drains these facts before deciding the
/// borrowed outer close; direct parsing emits the same fact immediately.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkEmbeddedRecoveryFact {
    pub(crate) spec: RecoverySiteSpec,
    pub(crate) range: Range<usize>,
    pub(crate) kind: RecoveryKind,
    pub(crate) unexpected: Option<UnexpectedCategory>,
}

/// One sink-neutral canonical recovery decision and its owner continuation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CanonicalRecoveryEpisode {
    pub(crate) fact: YumarkEmbeddedRecoveryFact,
    pub(crate) continuation: CanonicalRecoveryContinuation,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum CanonicalRecoveryContinuation {
    RetrySameSlot,
    StopAtBoundary,
}

/// Sink-neutral identity shared by an AST recovery owner and its direct-CST
/// emission helper.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct RecoverySiteSpec {
    pub(crate) role: GrammarRole,
    pub(crate) expected: ExpectedSyntax,
}

/// Persistent structural state for the iterative Yumark grammar.
///
/// A checkpoint retains only the current head. Published nodes are immutable,
/// so rollback is a root swap and committed mutations leave no undo journal.
struct YumarkFrameStack {
    head: Option<Arc<YumarkFrameNode>>,
}

struct YumarkFrameNode {
    frame: YumarkFrame,
    parent: Option<Arc<YumarkFrameNode>>,
    depth: usize,
    embedded_recoveries: YumarkEmbeddedRecoveryLog,
}

#[derive(Clone, Default)]
struct YumarkEmbeddedRecoveryLog {
    head: Option<Arc<YumarkEmbeddedRecoveryNode>>,
    len: usize,
}

struct YumarkEmbeddedRecoveryNode {
    fact: YumarkEmbeddedRecoveryFact,
    parent: Option<Arc<YumarkEmbeddedRecoveryNode>>,
}

#[derive(Clone)]
struct YumarkFrameCheckpoint {
    head: Option<Arc<YumarkFrameNode>>,
}

impl YumarkFrameStack {
    fn new() -> Self {
        Self { head: None }
    }

    fn checkpoint(&self) -> YumarkFrameCheckpoint {
        YumarkFrameCheckpoint {
            head: self.head.clone(),
        }
    }

    fn rollback(&mut self, checkpoint: YumarkFrameCheckpoint) {
        self.replace_head(checkpoint.into_head());
    }

    fn push(&mut self, frame: YumarkFrame) {
        let parent = self.head.take();
        let depth = parent.as_ref().map_or(1, |node| node.depth + 1);
        self.head = Some(Arc::new(YumarkFrameNode {
            frame,
            parent,
            depth,
            embedded_recoveries: YumarkEmbeddedRecoveryLog::default(),
        }));
    }

    fn replace_last(&mut self, frame: YumarkFrame) {
        let parent = self
            .head
            .as_ref()
            .expect("cannot replace the top of an empty Yumark frame stack")
            .parent
            .clone();
        let depth = parent.as_ref().map_or(1, |node| node.depth + 1);
        let embedded_recoveries = self
            .head
            .as_ref()
            .expect("cannot replace the top of an empty Yumark frame stack")
            .embedded_recoveries
            .clone();
        self.replace_head(Some(Arc::new(YumarkFrameNode {
            frame,
            parent,
            depth,
            embedded_recoveries,
        })));
    }

    fn record_embedded_recovery(&mut self, fact: YumarkEmbeddedRecoveryFact) {
        let Some(head) = self.head.as_ref() else {
            return;
        };
        if !matches!(head.frame, YumarkFrame::EmbeddedYulang { .. }) {
            return;
        }
        let parent = head.parent.clone();
        let depth = head.depth;
        let embedded_recoveries = YumarkEmbeddedRecoveryLog {
            head: Some(Arc::new(YumarkEmbeddedRecoveryNode {
                fact,
                parent: head.embedded_recoveries.head.clone(),
            })),
            len: head.embedded_recoveries.len + 1,
        };
        self.replace_head(Some(Arc::new(YumarkFrameNode {
            frame: head.frame.clone(),
            parent,
            depth,
            embedded_recoveries,
        })));
    }

    fn drain_embedded_recoveries(&mut self) -> Vec<YumarkEmbeddedRecoveryFact> {
        let Some(head) = self.head.as_ref() else {
            return Vec::new();
        };
        assert!(matches!(head.frame, YumarkFrame::EmbeddedYulang { .. }));
        let mut facts = Vec::with_capacity(head.embedded_recoveries.len);
        let mut recovery = head.embedded_recoveries.head.as_deref();
        while let Some(current) = recovery {
            facts.push(current.fact.clone());
            recovery = current.parent.as_deref();
        }
        facts.reverse();
        if facts.is_empty() {
            return facts;
        }
        self.replace_head(Some(Arc::new(YumarkFrameNode {
            frame: head.frame.clone(),
            parent: head.parent.clone(),
            depth: head.depth,
            embedded_recoveries: YumarkEmbeddedRecoveryLog::default(),
        })));
        facts
    }

    fn pop(&mut self) -> Option<YumarkFrame> {
        let head = self.head.as_ref()?;
        let frame = head.frame.clone();
        let parent = head.parent.clone();
        self.replace_head(parent);
        Some(frame)
    }

    fn last(&self) -> Option<&YumarkFrame> {
        self.head.as_deref().map(|node| &node.frame)
    }

    fn len(&self) -> usize {
        self.head.as_ref().map_or(0, |node| node.depth)
    }

    #[cfg(test)]
    fn values(&self) -> Vec<YumarkFrame> {
        let mut values = Vec::with_capacity(self.len());
        let mut node = self.head.as_deref();
        while let Some(current) = node {
            values.push(current.frame.clone());
            node = current.parent.as_deref();
        }
        values.reverse();
        values
    }

    fn replace_head(&mut self, head: Option<Arc<YumarkFrameNode>>) {
        let old = std::mem::replace(&mut self.head, head);
        release_yumark_frame_chain(old);
    }
}

impl Drop for YumarkFrameStack {
    fn drop(&mut self) {
        release_yumark_frame_chain(self.head.take());
    }
}

impl YumarkFrameCheckpoint {
    fn into_head(mut self) -> Option<Arc<YumarkFrameNode>> {
        self.head.take()
    }
}

impl Drop for YumarkFrameCheckpoint {
    fn drop(&mut self) {
        release_yumark_frame_chain(self.head.take());
    }
}

/// Release uniquely-owned persistent tails iteratively so document nesting
/// cannot become Rust call-stack depth during rollback or destruction.
fn release_yumark_frame_chain(mut head: Option<Arc<YumarkFrameNode>>) {
    while let Some(node) = head {
        match Arc::try_unwrap(node) {
            Ok(mut node) => head = node.parent.take(),
            Err(shared) => {
                drop(shared);
                break;
            }
        }
    }
}

impl Drop for YumarkEmbeddedRecoveryLog {
    fn drop(&mut self) {
        let mut head = self.head.take();
        while let Some(node) = head {
            match Arc::try_unwrap(node) {
                Ok(mut node) => head = node.parent.take(),
                Err(shared) => {
                    drop(shared);
                    break;
                }
            }
        }
    }
}

impl IfExpressionCompanionFrame {
    pub(crate) fn id(self) -> IfExpressionCompanionId {
        self.id
    }

    pub(crate) fn if_base_indent(self) -> usize {
        self.if_base_indent
    }

    pub(crate) fn exact_words(self) -> &'static [&'static str] {
        self.exact_words
    }
}

/// All mutable state whose value can affect a scanner or layout decision.
pub(crate) struct ParseLocal {
    line: LineState,
    indentation_baselines: RollbackStack<IndentationBaseline>,
    inline: bool,
    ml_arg: bool,
    type_ml_arg: bool,
    type_expression_episode_depth: usize,
    type_expression_episode_policies: RollbackStack<TypeExpressionEpisodePolicy>,
    type_expression_scoped_stop_frames: RollbackStack<TypeExpressionScopedStopFrame>,
    stop_sets: RollbackStack<StopSet>,
    delimiters: RollbackStack<Delimiter>,
    expression_delimited_owners: RollbackStack<ExpressionDelimitedOwner>,
    type_delimited_owners: RollbackStack<TypeDelimitedOwner>,
    lexical_modes: RollbackStack<EmbeddedLexicalMode>,
    ambient_owner_scopes: RollbackStack<AmbientOwnerScopeFrame>,
    if_expression_companions: RollbackStack<IfExpressionCompanionFrame>,
    yumark_frames: YumarkFrameStack,
    staged_header_facts: Vec<StagedHeaderFact>,
    operator_probes: Vec<OperatorCandidateProbe>,
    reusable_recoveries: Vec<CommittedRecoveryRecord>,
    reused_recovery_indices: Vec<usize>,
    next_diagnostic_id: u32,
    next_if_expression_companion_id: u32,
    type_malformed_caller_boundary: Option<TypeMalformedCallerBoundaryFence>,
}

impl ParseLocal {
    pub(crate) fn new() -> Self {
        Self {
            line: LineState::default(),
            indentation_baselines: RollbackStack::new(),
            inline: false,
            ml_arg: false,
            type_ml_arg: false,
            type_expression_episode_depth: 0,
            type_expression_episode_policies: RollbackStack::new(),
            type_expression_scoped_stop_frames: RollbackStack::new(),
            stop_sets: RollbackStack::new(),
            delimiters: RollbackStack::new(),
            expression_delimited_owners: RollbackStack::new(),
            type_delimited_owners: RollbackStack::new(),
            lexical_modes: RollbackStack::new(),
            ambient_owner_scopes: RollbackStack::new(),
            if_expression_companions: RollbackStack::new(),
            yumark_frames: YumarkFrameStack::new(),
            staged_header_facts: Vec::new(),
            operator_probes: Vec::new(),
            reusable_recoveries: Vec::new(),
            reused_recovery_indices: Vec::new(),
            next_diagnostic_id: 0,
            next_if_expression_companion_id: 0,
            type_malformed_caller_boundary: None,
        }
    }

    /// Starts a full parse after header discovery, preserving the identities
    /// already committed for header-owned recovery sites.
    pub(crate) fn with_reusable_recoveries(recoveries: &[CommittedRecoveryRecord]) -> Self {
        let mut local = Self::new();
        local.next_diagnostic_id = recoveries
            .iter()
            .map(|record| record.id.0)
            .max()
            .map_or(0, |id| id + 1);
        local.reusable_recoveries.extend_from_slice(recoveries);
        local
    }

    pub(crate) fn checkpoint(&self) -> ParseLocalCheckpoint {
        ParseLocalCheckpoint {
            line: self.line,
            indentation_baselines: self.indentation_baselines.checkpoint(),
            inline: self.inline,
            ml_arg: self.ml_arg,
            type_ml_arg: self.type_ml_arg,
            type_expression_episode_depth: self.type_expression_episode_depth,
            type_expression_episode_policies: self.type_expression_episode_policies.checkpoint(),
            type_expression_scoped_stop_frames: self
                .type_expression_scoped_stop_frames
                .checkpoint(),
            stop_sets: self.stop_sets.checkpoint(),
            delimiters: self.delimiters.checkpoint(),
            expression_delimited_owners: self.expression_delimited_owners.checkpoint(),
            type_delimited_owners: self.type_delimited_owners.checkpoint(),
            lexical_modes: self.lexical_modes.checkpoint(),
            ambient_owner_scopes: self.ambient_owner_scopes.checkpoint(),
            if_expression_companions: self.if_expression_companions.checkpoint(),
            yumark_frames: self.yumark_frames.checkpoint(),
            staged_header_facts_len: self.staged_header_facts.len(),
            operator_probes_len: self.operator_probes.len(),
            reused_recovery_indices_len: self.reused_recovery_indices.len(),
            next_diagnostic_id: self.next_diagnostic_id,
            next_if_expression_companion_id: self.next_if_expression_companion_id,
            type_malformed_caller_boundary: self.type_malformed_caller_boundary,
        }
    }

    pub(crate) fn rollback(&mut self, checkpoint: ParseLocalCheckpoint) {
        // Restore the persistent Yumark head before scanner/layout state
        // visible to its frame judges.
        self.yumark_frames.rollback(checkpoint.yumark_frames);
        self.line = checkpoint.line;
        self.indentation_baselines
            .rollback(checkpoint.indentation_baselines);
        self.inline = checkpoint.inline;
        self.ml_arg = checkpoint.ml_arg;
        self.type_ml_arg = checkpoint.type_ml_arg;
        self.type_expression_episode_depth = checkpoint.type_expression_episode_depth;
        self.type_expression_episode_policies
            .rollback(checkpoint.type_expression_episode_policies);
        self.type_expression_scoped_stop_frames
            .rollback(checkpoint.type_expression_scoped_stop_frames);
        self.stop_sets.rollback(checkpoint.stop_sets);
        self.delimiters.rollback(checkpoint.delimiters);
        self.expression_delimited_owners
            .rollback(checkpoint.expression_delimited_owners);
        self.type_delimited_owners
            .rollback(checkpoint.type_delimited_owners);
        self.lexical_modes.rollback(checkpoint.lexical_modes);
        self.ambient_owner_scopes
            .rollback(checkpoint.ambient_owner_scopes);
        self.if_expression_companions
            .rollback(checkpoint.if_expression_companions);
        self.staged_header_facts
            .truncate(checkpoint.staged_header_facts_len);
        self.operator_probes
            .truncate(checkpoint.operator_probes_len);
        self.reused_recovery_indices
            .truncate(checkpoint.reused_recovery_indices_len);
        self.next_diagnostic_id = checkpoint.next_diagnostic_id;
        self.next_if_expression_companion_id = checkpoint.next_if_expression_companion_id;
        self.type_malformed_caller_boundary = checkpoint.type_malformed_caller_boundary;
    }

    pub(crate) fn line(&self) -> LineState {
        self.line
    }

    pub(crate) fn set_line(&mut self, line: LineState) {
        self.line = line;
    }

    pub(crate) fn type_malformed_caller_boundary(
        &self,
    ) -> Option<TypeMalformedCallerBoundaryFence> {
        self.type_malformed_caller_boundary
    }

    pub(crate) fn set_type_malformed_caller_boundary(
        &mut self,
        fence: Option<TypeMalformedCallerBoundaryFence>,
    ) {
        self.type_malformed_caller_boundary = fence;
    }

    pub(crate) fn push_indentation_baseline(&mut self, baseline: IndentationBaseline) {
        self.indentation_baselines.push(baseline);
    }

    pub(crate) fn pop_indentation_baseline(&mut self) -> Option<IndentationBaseline> {
        self.indentation_baselines.pop()
    }

    pub(crate) fn indentation_baseline(&self) -> Option<IndentationBaseline> {
        self.indentation_baselines.last().copied()
    }

    pub(crate) fn set_inline(&mut self, inline: bool) {
        self.inline = inline;
    }

    pub(crate) fn inline(&self) -> bool {
        self.inline
    }

    pub(crate) fn set_ml_arg(&mut self, ml_arg: bool) {
        self.ml_arg = ml_arg;
    }

    pub(crate) fn ml_arg(&self) -> bool {
        self.ml_arg
    }

    pub(crate) fn set_type_ml_arg(&mut self, type_ml_arg: bool) {
        self.type_ml_arg = type_ml_arg;
    }

    pub(crate) fn type_ml_arg(&self) -> bool {
        self.type_ml_arg
    }

    pub(crate) fn push_type_expression_episode(
        &mut self,
        policy: TypeExpressionEpisodePolicy,
    ) -> usize {
        self.type_expression_episode_depth += 1;
        self.type_expression_episode_policies.push(policy);
        self.type_expression_episode_depth
    }

    pub(crate) fn pop_type_expression_episode(&mut self) -> Option<TypeExpressionEpisodePolicy> {
        let policy = self.type_expression_episode_policies.pop()?;
        self.type_expression_episode_depth = self
            .type_expression_episode_depth
            .checked_sub(1)
            .expect("a TypeExpression episode policy requires a matching depth");
        Some(policy)
    }

    pub(crate) fn type_expression_episode_depth(&self) -> usize {
        self.type_expression_episode_depth
    }

    pub(crate) fn type_expression_episode_policy(&self) -> Option<TypeExpressionEpisodePolicy> {
        self.type_expression_episode_policies.last().copied()
    }

    pub(crate) fn push_type_expression_scoped_stop_frame(
        &mut self,
        frame: TypeExpressionScopedStopFrame,
    ) {
        self.type_expression_scoped_stop_frames.push(frame);
    }

    pub(crate) fn pop_type_expression_scoped_stop_frame(
        &mut self,
    ) -> Option<TypeExpressionScopedStopFrame> {
        self.type_expression_scoped_stop_frames.pop()
    }

    pub(crate) fn type_expression_scoped_stop_frames(
        &self,
    ) -> impl Iterator<Item = &TypeExpressionScopedStopFrame> {
        self.type_expression_scoped_stop_frames
            .values()
            .iter()
            .rev()
    }

    pub(crate) fn push_stop_set(&mut self, stop_set: StopSet) {
        self.stop_sets.push(stop_set);
    }

    pub(crate) fn replace_stop_set(&mut self, stop_set: StopSet) {
        self.stop_sets.replace_last(stop_set);
    }

    pub(crate) fn pop_stop_set(&mut self) -> Option<StopSet> {
        self.stop_sets.pop()
    }

    pub(crate) fn stop_set(&self) -> Option<StopSet> {
        self.stop_sets.last().copied()
    }

    pub(crate) fn push_delimiter(&mut self, delimiter: Delimiter) {
        self.delimiters.push(delimiter);
    }

    pub(crate) fn push_yumark_delimiter(&mut self, delimiter: Delimiter) -> YumarkDelimiterFloor {
        self.delimiters.push(delimiter);
        YumarkDelimiterFloor(self.delimiters.len())
    }

    pub(crate) fn yumark_at_delimiter_floor(&self, floor: YumarkDelimiterFloor) -> bool {
        self.delimiters.len() == floor.0
    }

    pub(crate) fn pop_yumark_delimiter(
        &mut self,
        floor: YumarkDelimiterFloor,
        expected: Delimiter,
    ) {
        assert_eq!(
            self.delimiters.len(),
            floor.0,
            "Yumark may pop only its exact borrowed delimiter floor"
        );
        assert_eq!(self.delimiters.pop(), Some(expected));
    }

    pub(crate) fn pop_delimiter(&mut self) -> Option<Delimiter> {
        self.delimiters.pop()
    }

    pub(crate) fn delimiter(&self) -> Option<Delimiter> {
        self.delimiters.last().copied()
    }

    pub(crate) fn push_expression_delimited_owner(&mut self, owner: ExpressionDelimitedOwner) {
        self.expression_delimited_owners.push(owner);
    }

    pub(crate) fn pop_expression_delimited_owner(&mut self) -> Option<ExpressionDelimitedOwner> {
        self.expression_delimited_owners.pop()
    }

    pub(crate) fn expression_delimited_owner(&self) -> Option<ExpressionDelimitedOwner> {
        self.expression_delimited_owners.last().copied()
    }

    pub(crate) fn push_type_delimited_owner(&mut self, owner: TypeDelimitedOwner) {
        self.type_delimited_owners.push(owner);
    }

    pub(crate) fn pop_type_delimited_owner(&mut self) -> Option<TypeDelimitedOwner> {
        self.type_delimited_owners.pop()
    }

    pub(crate) fn type_delimited_owner(&self) -> Option<TypeDelimitedOwner> {
        self.type_delimited_owners.last().copied()
    }

    pub(crate) fn push_lexical_mode(&mut self, mode: EmbeddedLexicalMode) {
        self.lexical_modes.push(mode);
    }

    pub(crate) fn replace_lexical_mode(&mut self, mode: EmbeddedLexicalMode) {
        self.lexical_modes.replace_last(mode);
    }

    pub(crate) fn pop_lexical_mode(&mut self) -> Option<EmbeddedLexicalMode> {
        self.lexical_modes.pop()
    }

    pub(crate) fn lexical_mode(&self) -> Option<EmbeddedLexicalMode> {
        self.lexical_modes.last().copied()
    }

    pub(crate) fn push_ambient_owner_scope(&mut self, frame: AmbientOwnerScopeFrame) {
        self.ambient_owner_scopes.push(frame);
    }

    pub(crate) fn push_root_statement_ambient_scope(&mut self) -> AmbientOwnerScopeFrame {
        let frame = AmbientOwnerScopeFrame::root_statement();
        self.push_ambient_owner_scope(frame);
        frame
    }

    pub(crate) fn push_indented_statement_ambient_scope(
        &mut self,
        statement_baseline: usize,
    ) -> AmbientOwnerScopeFrame {
        let frame = AmbientOwnerScopeFrame::indented_statement(statement_baseline);
        self.push_ambient_owner_scope(frame);
        frame
    }

    pub(crate) fn push_inline_canonical_statement_ambient_scope(
        &mut self,
        owner: InlineStatementOwnerKind,
    ) -> AmbientOwnerScopeFrame {
        let frame = AmbientOwnerScopeFrame::inline_canonical_statement(owner);
        self.push_ambient_owner_scope(frame);
        frame
    }

    pub(crate) fn pop_ambient_owner_scope(&mut self) -> Option<AmbientOwnerScopeFrame> {
        self.ambient_owner_scopes.pop()
    }

    pub(crate) fn ambient_owner_scope(&self) -> Option<AmbientOwnerScopeFrame> {
        self.ambient_owner_scopes.last().copied()
    }

    /// Iterates ambient statement-owner scopes from innermost to outermost.
    pub(crate) fn ambient_owner_scope_frames(
        &self,
    ) -> impl Iterator<Item = &AmbientOwnerScopeFrame> + '_ {
        self.ambient_owner_scopes.values().iter().rev()
    }

    pub(crate) fn ambient_owner_scope_depth(&self) -> usize {
        self.ambient_owner_scopes.len()
    }

    pub(crate) fn push_braced_ambient_owner_barrier(
        &mut self,
        origin: BracedBarrierOrigin,
    ) -> AmbientOwnerScopeFrame {
        let frame =
            AmbientOwnerScopeFrame::braced_barrier(origin, self.if_expression_companion_depth());
        self.push_ambient_owner_scope(frame);
        frame
    }

    pub(crate) fn push_if_expression_companion(
        &mut self,
        if_base_indent: usize,
        exact_words: &'static [&'static str],
    ) -> IfExpressionCompanionId {
        let id = IfExpressionCompanionId(self.next_if_expression_companion_id);
        self.next_if_expression_companion_id += 1;
        self.if_expression_companions
            .push(IfExpressionCompanionFrame {
                id,
                if_base_indent,
                exact_words,
            });
        id
    }

    pub(crate) fn pop_if_expression_companion(&mut self) -> Option<IfExpressionCompanionFrame> {
        self.if_expression_companions.pop()
    }

    /// Releases the opaque identity of a recovered initial `if` condition
    /// after its frame has closed. No AST or direct recovery record retains
    /// this identity, so a later sibling may reuse it.
    pub(crate) fn rollback_if_expression_companion_allocation(
        &mut self,
        id: IfExpressionCompanionId,
    ) {
        assert!(id.0 < self.next_if_expression_companion_id);
        self.next_if_expression_companion_id = id.0;
    }

    pub(crate) fn if_expression_companion(&self) -> Option<IfExpressionCompanionFrame> {
        self.if_expression_companions.last().copied()
    }

    pub(crate) fn if_expression_companion_depth(&self) -> usize {
        self.if_expression_companions.len()
    }

    pub(crate) fn push_yumark_frame(&mut self, frame: YumarkFrame) {
        self.yumark_frames.push(frame);
    }

    pub(crate) fn replace_yumark_frame(&mut self, frame: YumarkFrame) {
        self.yumark_frames.replace_last(frame);
    }

    pub(crate) fn pop_yumark_frame(&mut self) -> Option<YumarkFrame> {
        self.yumark_frames.pop()
    }

    pub(crate) fn yumark_frame(&self) -> Option<&YumarkFrame> {
        self.yumark_frames.last()
    }

    pub(crate) fn yumark_frame_depth(&self) -> usize {
        self.yumark_frames.len()
    }

    pub(crate) fn yumark_embedded_recovery_active(&self) -> bool {
        matches!(
            self.yumark_frames.last(),
            Some(YumarkFrame::EmbeddedYulang { .. })
        )
    }

    pub(crate) fn record_yumark_embedded_recovery(&mut self, fact: YumarkEmbeddedRecoveryFact) {
        self.yumark_frames.record_embedded_recovery(fact);
    }

    pub(crate) fn drain_yumark_embedded_recoveries(&mut self) -> Vec<YumarkEmbeddedRecoveryFact> {
        self.yumark_frames.drain_embedded_recoveries()
    }

    pub(crate) fn publish_yumark_embedded_recovery(
        &mut self,
        spec: RecoverySiteSpec,
        range: Range<usize>,
        kind: RecoveryKind,
        unexpected: Option<UnexpectedCategory>,
    ) {
        self.record_yumark_embedded_recovery(YumarkEmbeddedRecoveryFact {
            spec,
            range,
            kind,
            unexpected,
        });
    }

    fn nearest_visible_statement_baseline(&self) -> Option<usize> {
        for frame in self.ambient_owner_scopes.values().iter().rev() {
            match frame.kind {
                AmbientOwnerScopeKind::RootStatement | AmbientOwnerScopeKind::IndentedStatement => {
                    return frame.statement_baseline;
                }
                AmbientOwnerScopeKind::BracedBarrier(_) => return None,
                AmbientOwnerScopeKind::InlineCanonicalStatement(_) => {}
            }
        }
        None
    }

    fn if_expression_companion_visibility_floor(&self) -> usize {
        self.ambient_owner_scopes
            .values()
            .iter()
            .rev()
            .find_map(|frame| match frame.kind {
                AmbientOwnerScopeKind::BracedBarrier(_) => frame.if_visibility_floor,
                _ => None,
            })
            .unwrap_or(0)
    }

    pub(crate) fn stage_header_fact(&mut self, fact: StagedHeaderFact) {
        self.staged_header_facts.push(fact);
    }

    pub(crate) fn staged_header_fact_count(&self) -> usize {
        self.staged_header_facts.len()
    }

    pub(crate) fn begin_operator_probe(&mut self, probe: OperatorCandidateProbe) {
        self.operator_probes.push(probe);
    }

    pub(crate) fn operator_probe_count(&self) -> usize {
        self.operator_probes.len()
    }

    /// Allocate a recovery identity only after a continuation has committed.
    pub(crate) fn next_diagnostic_id(&mut self) -> DiagnosticId {
        let id = DiagnosticId(self.next_diagnostic_id);
        self.next_diagnostic_id += 1;
        id
    }

    fn take_reusable_recovery(
        &mut self,
        site: &RecoverySiteKey,
        kind: RecoveryKind,
    ) -> Option<CommittedRecoveryRecord> {
        let index = self
            .reusable_recoveries
            .iter()
            .enumerate()
            .find_map(|(index, record)| {
                (!self.reused_recovery_indices.contains(&index)
                    && record.site == *site
                    && record.kind == kind)
                    .then_some(index)
            })?;
        self.reused_recovery_indices.push(index);
        Some(self.reusable_recoveries[index].clone())
    }

    /// Test-only value snapshot of every parser-local scalar, stack and
    /// transaction collection. Rollback bookkeeping is intentionally omitted:
    /// tests compare grammar-visible state, not the stack's internal journal.
    #[cfg(test)]
    pub(crate) fn value_snapshot(&self) -> ParseLocalValueSnapshot {
        ParseLocalValueSnapshot {
            line: self.line,
            indentation_baselines: self.indentation_baselines.values().to_vec(),
            inline: self.inline,
            ml_arg: self.ml_arg,
            type_ml_arg: self.type_ml_arg,
            type_expression_episode_depth: self.type_expression_episode_depth,
            type_expression_episode_policies: self
                .type_expression_episode_policies
                .values()
                .to_vec(),
            type_expression_scoped_stop_frames: self
                .type_expression_scoped_stop_frames
                .values()
                .to_vec(),
            stop_sets: self.stop_sets.values().to_vec(),
            delimiters: self.delimiters.values().to_vec(),
            expression_delimited_owners: self.expression_delimited_owners.values().to_vec(),
            type_delimited_owners: self.type_delimited_owners.values().to_vec(),
            lexical_modes: self.lexical_modes.values().to_vec(),
            ambient_owner_scopes: self.ambient_owner_scopes.values().to_vec(),
            if_expression_companions: self.if_expression_companions.values().to_vec(),
            yumark_frames: self.yumark_frames.values(),
            staged_header_facts: self.staged_header_facts.clone(),
            operator_probes: self.operator_probes.clone(),
            reusable_recoveries: self.reusable_recoveries.clone(),
            reused_recovery_indices: self.reused_recovery_indices.clone(),
            next_diagnostic_id: self.next_diagnostic_id,
            next_if_expression_companion_id: self.next_if_expression_companion_id,
            type_malformed_caller_boundary: self.type_malformed_caller_boundary,
        }
    }
}

#[cfg(test)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ParseLocalValueSnapshot {
    pub(crate) line: LineState,
    pub(crate) indentation_baselines: Vec<IndentationBaseline>,
    pub(crate) inline: bool,
    pub(crate) ml_arg: bool,
    pub(crate) type_ml_arg: bool,
    pub(crate) type_expression_episode_depth: usize,
    pub(crate) type_expression_episode_policies: Vec<TypeExpressionEpisodePolicy>,
    pub(crate) type_expression_scoped_stop_frames: Vec<TypeExpressionScopedStopFrame>,
    pub(crate) stop_sets: Vec<StopSet>,
    pub(crate) delimiters: Vec<Delimiter>,
    pub(crate) expression_delimited_owners: Vec<ExpressionDelimitedOwner>,
    pub(crate) type_delimited_owners: Vec<TypeDelimitedOwner>,
    pub(crate) lexical_modes: Vec<EmbeddedLexicalMode>,
    pub(crate) ambient_owner_scopes: Vec<AmbientOwnerScopeFrame>,
    pub(crate) if_expression_companions: Vec<IfExpressionCompanionFrame>,
    pub(crate) yumark_frames: Vec<YumarkFrame>,
    pub(crate) staged_header_facts: Vec<StagedHeaderFact>,
    pub(crate) operator_probes: Vec<OperatorCandidateProbe>,
    pub(crate) reusable_recoveries: Vec<CommittedRecoveryRecord>,
    pub(crate) reused_recovery_indices: Vec<usize>,
    pub(crate) next_diagnostic_id: u32,
    pub(crate) next_if_expression_companion_id: u32,
    pub(crate) type_malformed_caller_boundary: Option<TypeMalformedCallerBoundaryFence>,
}

impl Default for ParseLocal {
    fn default() -> Self {
        Self::new()
    }
}

impl Back for ParseLocal {
    type Checkpoint = ParseLocalCheckpoint;

    fn checkpoint(&mut self) -> Self::Checkpoint {
        ParseLocal::checkpoint(self)
    }

    fn rollback(&mut self, checkpoint: Self::Checkpoint) {
        ParseLocal::rollback(self, checkpoint);
    }
}

/// Returns whether a strict visible-statement dedent or an active If
/// companion owns the current trivia-plus-word gap. This probe never consumes
/// source or commits evidence.
pub(crate) fn any_ambient_owner_claims<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia).expect("trivia is total");
    let has_physical_newline = trivia_has_physical_newline(&trivia);
    let following_line_indent = i.local.line().line_indent;
    let word = i.run(scan_word).map(|word| word.text());
    let strict_dedent = has_physical_newline
        && i.local
            .nearest_visible_statement_baseline()
            .is_some_and(|baseline| following_line_indent < baseline);
    let result = strict_dedent
        || if_continuation_owner_from_evidence(
            i.local,
            has_physical_newline,
            following_line_indent,
            word,
        )
        .is_some();
    i.rollback(checkpoint);
    result
}

/// Returns the innermost visible IfExpression identity that owns the current
/// trivia-plus-word gap. This probe never consumes source or commits evidence.
pub(crate) fn if_continuation_owner<E>(i: &mut SynIn<E>) -> Option<IfExpressionCompanionId>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia).expect("trivia is total");
    let has_physical_newline = trivia_has_physical_newline(&trivia);
    let following_line_indent = i.local.line().line_indent;
    let word = i.run(scan_word).map(|word| word.text());
    let result = if_continuation_owner_from_evidence(
        i.local,
        has_physical_newline,
        following_line_indent,
        word,
    );
    i.rollback(checkpoint);
    result
}

fn if_continuation_owner_from_evidence(
    local: &ParseLocal,
    has_physical_newline: bool,
    following_line_indent: usize,
    word: Option<&str>,
) -> Option<IfExpressionCompanionId> {
    let word = word?;
    let floor = local.if_expression_companion_visibility_floor();
    debug_assert!(floor <= local.if_expression_companions.len());
    local.if_expression_companions.values()[floor..]
        .iter()
        .rev()
        .find(|frame| {
            frame.exact_words.iter().any(|exact| *exact == word)
                && (!has_physical_newline || following_line_indent >= frame.if_base_indent)
        })
        .map(|frame| frame.id)
}

/// Small scalar/depth snapshot used by chasa together with its input checkpoint.
#[derive(Clone)]
pub(crate) struct ParseLocalCheckpoint {
    line: LineState,
    indentation_baselines: StackCheckpoint,
    inline: bool,
    ml_arg: bool,
    type_ml_arg: bool,
    type_expression_episode_depth: usize,
    type_expression_episode_policies: StackCheckpoint,
    type_expression_scoped_stop_frames: StackCheckpoint,
    stop_sets: StackCheckpoint,
    delimiters: StackCheckpoint,
    expression_delimited_owners: StackCheckpoint,
    type_delimited_owners: StackCheckpoint,
    lexical_modes: StackCheckpoint,
    ambient_owner_scopes: StackCheckpoint,
    if_expression_companions: StackCheckpoint,
    yumark_frames: YumarkFrameCheckpoint,
    staged_header_facts_len: usize,
    operator_probes_len: usize,
    reused_recovery_indices_len: usize,
    next_diagnostic_id: u32,
    next_if_expression_companion_id: u32,
    type_malformed_caller_boundary: Option<TypeMalformedCallerBoundaryFence>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct TypeMalformedCallerBoundaryFence {
    pub(crate) trivia_start: usize,
}

/// Physical-line state changed while trailing trivia is consumed.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct LineState {
    pub(crate) last_newline: Option<(usize, usize)>,
    pub(crate) line_start: usize,
    pub(crate) line_indent: usize,
    pub(crate) at_line_start: bool,
}

/// A scoped indentation threshold introduced by a block or declaration marker.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct IndentationBaseline {
    pub(crate) column: usize,
    pub(crate) kind: IndentationBaselineKind,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum IndentationBaselineKind {
    Block,
    Introducer,
}

/// Compact grammar stops that can be suspended by pushing another frame.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct StopSet(u32);

impl StopSet {
    pub(crate) fn with(mut self, stop: StopKind) -> Self {
        self.0 |= 1u32 << (stop as u8);
        self
    }

    pub(crate) fn without(mut self, stop: StopKind) -> Self {
        self.0 &= !(1u32 << (stop as u8));
        self
    }

    pub(crate) fn contains(self, stop: StopKind) -> bool {
        self.0 & (1u32 << (stop as u8)) != 0
    }

    pub(crate) fn difference(self, other: Self) -> Self {
        Self(self.0 & !other.0)
    }
}

/// A stop set whose ownership is visible only in one logical TypeExpression
/// episode. Nested recursive TypeExpressions retain the raw stop bits but do
/// not inherit the caller's ownership decision.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct TypeExpressionScopedStopFrame {
    pub(crate) stops: StopSet,
    pub(crate) visible_episode_depth: usize,
}

/// Candidate policy shared by the probe, parser, recovery scanner, and retry
/// that make up one logical TypeExpression slot.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct TypeExpressionEpisodePolicy {
    pub(crate) fresh_primary_locally_owned_stops: StopSet,
    pub(crate) fresh_primary_owns_adjacent_polymorphic_variant_starter: bool,
}

macro_rules! define_stop_kinds {
    ($($kind:ident),+ $(,)?) => {
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        #[repr(u8)]
        pub(crate) enum StopKind {
            $($kind),+
        }

        impl StopKind {
            /// Generated from the enum declaration so the iterable vocabulary
            /// cannot omit a newly-added stop kind.
            pub(crate) const ALL: &'static [Self] = &[$(Self::$kind),+];
        }
    };
}

define_stop_kinds!(
    Newline,
    Comma,
    Semicolon,
    Colon,
    LeftBrace,
    Elsif,
    Else,
    RightParenthesis,
    RightBracket,
    RightBrace,
    Equal,
    Arrow,
    ArmGuardIf,
    ArmGuardWhere,
    With,
    Derives,
    Via,
    In,
    Impl,
    LeftParenthesis,
    Pipe,
);

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum Delimiter {
    Parenthesis,
    Bracket,
    Brace,
}

/// The expression-list owner that authorizes ML application within one item.
///
/// This is deliberately distinct from the delimiter and stop stacks: callers
/// use those stacks for boundary ownership, while this stack records the
/// expression grammar whose items may themselves contain spaced application.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ExpressionDelimitedOwner {
    Call,
    Index,
    ProjectionTuple,
    ProjectionRecord,
}

/// The type-list owner that authorizes ML type application within one item.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum TypeDelimitedOwner {
    Call,
    ParenthesizedGroup,
    NamedRecord,
    EffectRow,
    BracketRow,
    PolymorphicVariant,
    StructNamedFields,
    VariantNamedPayload,
    VariantTuplePayload,
}

/// Operator-independent regions whose terminators suspend outer layout rules.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum EmbeddedLexicalMode {
    LineComment,
    BlockComment {
        depth: usize,
    },
    NormalString,
    Heredoc {
        quote_count: usize,
    },
    Interpolation {
        delimiter_depth: usize,
    },
    RuleLiteral,
    Yumark {
        mode: YumarkMode,
        quote_depth: usize,
        line_document_continuation: bool,
    },
    Fence {
        kind: FenceKind,
        /// Whether the next source position is a logical fence-line start.
        continuation: bool,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum YumarkMode {
    /// The apostrophe-bracket literal body, `'[...]`.
    Inline,
    /// A `>`-prefixed document line within an apostrophe-brace literal.
    Quoted,
    /// A non-quoted document line within an apostrophe-brace literal, `'{...}`.
    Block,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum FenceKind {
    /// A Yumark code fence whose body is raw text.
    Raw,
    /// A Yumark code fence whose body uses Yulang lexical regions.
    Yulang,
}

/// Placeholder transaction entry; concrete header facts arrive with grammar wiring.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum StagedHeaderFact {
    Import,
    Operator,
}

/// Local metadata for one bounded longest-operator-candidate exploration.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct OperatorCandidateProbe {
    pub(crate) start: usize,
    pub(crate) candidate_end: usize,
}

/// Non-emitting access available to speculative parsers and scanner probes.
///
/// The capability owns chasa's input, rollback-owned [`ParseLocal`], and
/// speculative expectation sink as one value. It deliberately has no route to
/// a direct CST sink, header facts, or committed recovery records.
pub(crate) struct Probe<'parse, 'source, 'local, E: ErrorSink<usize>> {
    input: GrammarInput<'parse, 'source, 'local, E>,
}

impl<'parse, 'source, 'local, E: ErrorSink<usize>> Probe<'parse, 'source, 'local, E> {
    pub(crate) fn new(input: GrammarInput<'parse, 'source, 'local, E>) -> Self {
        Self { input }
    }

    /// Runs scanner and recognition work with the underlying chasa input.
    pub(crate) fn input(&mut self) -> &mut GrammarInput<'parse, 'source, 'local, E> {
        &mut self.input
    }

    /// Transitions an accepted branch to an output-owning continuation.
    pub(crate) fn commit<O: CommitOutput<'source>>(
        self,
        output: O,
    ) -> Committed<'parse, 'source, 'local, E, O> {
        Committed {
            probe: self,
            output,
        }
    }
}

/// The grammar-owned identity of a recovery site.
///
/// This vocabulary deliberately has no string or raw-syntax-kind escape hatch:
/// adding a recovery site must make its causal grammar role explicit.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum GrammarRole {
    Declaration(DeclarationRole),
    ForStatement(ForStatementRole),
    ClosingDelimiter {
        owner: ConstructRole,
        delimiter: Delimiter,
    },
    Statement(StatementRole),
    Expression(ExpressionRole),
    ColonApplication(ColonApplicationRole),
    WithBody(WithBodyRole),
    IfExpression(IfExpressionRole),
    CaseLike(CaseLikeRole),
    BracedStatementBlock(BracedStatementBlockRole),
    Pattern(PatternRole),
    Type(TypeRole),
    Layout(LayoutRole),
    Embedded(EmbeddedRole),
    Yumark(YumarkRole),
    Token(TokenRole),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct YumarkRole {
    pub(crate) owner: YumarkOwner,
    pub(crate) slot: YumarkSlot,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum YumarkOwner {
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

impl YumarkOwner {
    pub(crate) const ALL: &'static [Self] = &[
        Self::DocComment,
        Self::Section,
        Self::List,
        Self::ListItem,
        Self::Quote,
        Self::CodeFence,
        Self::InlineGroup,
        Self::InlineLink,
        Self::InlineImage,
        Self::InlineApply,
        Self::InlineReference,
        Self::Emphasis,
        Self::Strong,
        Self::Command,
        Self::My,
        Self::Use,
        Self::DocArgument,
        Self::DoCapture,
        Self::IfChain,
        Self::IfBranch,
        Self::ElsifBranch,
        Self::ElseBranch,
    ];
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum YumarkSlot {
    Starter,
    Name,
    Head,
    Arguments,
    Condition,
    BodyIntroducer,
    Body,
    Destination,
    BranchPredecessor,
    ClosingDelimiter,
    SectionClose,
    QuoteForm,
    ExpressionBody,
    Route,
    Terminator,
}

impl YumarkSlot {
    pub(crate) const ALL: &'static [Self] = &[
        Self::Starter,
        Self::Name,
        Self::Head,
        Self::Arguments,
        Self::Condition,
        Self::BodyIntroducer,
        Self::Body,
        Self::Destination,
        Self::BranchPredecessor,
        Self::ClosingDelimiter,
        Self::SectionClose,
        Self::QuoteForm,
        Self::ExpressionBody,
        Self::Route,
        Self::Terminator,
    ];
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum DeclarationRole {
    Import(ImportRole),
    OperatorHeader(OperatorHeaderRole),
    Binding(BindingRole),
    Mod(ModRole),
    Struct(StructRole),
    Enum(EnumDeclarationRole),
    Error(ErrorDeclarationRole),
    Type(TypeDeclarationRole),
    Role(RoleDeclarationRole),
    Impl(ImplRole),
    Cast(CastRole),
    Act(ActDeclarationRole),
    Derives(DerivesRole),
    Companion(DeclarationCompanionRole),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum ImportRole {
    Path,
    GroupEntry,
    Alias,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum OperatorHeaderRole {
    Name,
    Fixity,
    LeftBindingPower,
    RightBindingPower,
    DefinitionIntroducer,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum StatementKind {
    UseDeclaration,
    OperatorDefinition,
    BindingDeclaration,
    ModDeclaration,
    StructDeclaration,
    EnumDeclaration,
    ErrorDeclaration,
    TypeDeclaration,
    RoleDeclaration,
    ImplDeclaration,
    CastDeclaration,
    ActDeclaration,
    ForStatement,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum StatementRole {
    Starter,
    Separator,
    TrailingInput { owner: StatementKind },
    OperatorDefinitionBody,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum ForStatementRole {
    Pattern,
    InKeyword,
    Iterable,
    BodyIntroducer,
    Body,
    IndentedStatement,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum BindingRole {
    Target,
    Body,
    IndentedStatement,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum ModRole {
    Name,
    TestName,
    BodyIntroducer,
    Body,
    IndentedStatement,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum StructRole {
    Name,
    BodyIntroducer,
    Field,
    FieldName,
    FieldColon,
    FieldType,
    FieldSeparator,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum EnumDeclarationRole {
    Name,
    BodyIntroducer,
    Variant(VariantDeclarationRole),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum ErrorDeclarationRole {
    Name,
    BodyIntroducer,
    Variant(VariantDeclarationRole),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum VariantDeclarationRole {
    Item,
    Name,
    Separator,
    FromType,
    PositionalPayload,
    NamedField,
    NamedFieldName,
    NamedFieldColon,
    NamedFieldType,
    NamedFieldSeparator,
    TupleFieldType,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum TypeDeclarationRole {
    Name,
    DefinitionIntroducer,
    Rhs,
    AttachedImpl(ImplRole),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum ImplRole {
    Head,
    Description,
    BodyIntroducer,
    Body,
    IndentedStatement,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum RoleDeclarationRole {
    Head,
    BodyIntroducer,
    Body,
    IndentedStatement,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum ActDeclarationRole {
    Head,
    Source,
    BodyIntroducer,
    Body,
    IndentedStatement,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum CastRole {
    PatternIntroducer,
    Pattern,
    TargetIntroducer,
    TargetType,
    BodyIntroducer,
    Body,
    IndentedStatement,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum DerivesRole {
    RoleReference,
    ViaTarget,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum DeclarationCompanionRole {
    Introducer,
    Body,
    Item,
    IndentedItem,
    Separator,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum ConstructRole {
    ImportGroup,
    OperatorName,
    ExpressionGroup,
    ArgumentList,
    IndexTail,
    ProjectionTupleTail,
    ProjectionRecordTail,
    BracedStatementBlockExpression,
    ParenthesizedPattern,
    ListPattern,
    RecordPattern,
    CastPattern,
    TypeCall,
    ParenthesizedTypeGroup,
    NamedRecordType,
    EffectRowType,
    BracketRow,
    PolymorphicVariantType,
    StructNamedFields,
    StructTupleFields,
    DeclarationCompanion,
    EnumBracedVariantBody,
    VariantNamedPayload,
    VariantTuplePayload,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum ExpressionRole {
    Nud,
    ParenthesizedSeparator,
    CallArgument,
    CallArgumentSeparator,
    IndexItem,
    IndexSeparator,
    ProjectionTupleItem,
    ProjectionTupleSeparator,
    ProjectionRecordItem,
    ProjectionRecordSpreadRhs,
    ProjectionRecordSeparator,
    FieldName,
    PathSegment,
    MlArgument,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum ColonApplicationRole {
    Rhs,
    InlineArgument,
    IndentedStatement,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum WithBodyRole {
    Introducer,
    Body,
    IndentedStatement,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum IfExpressionRole {
    Condition,
    BodyIntroducer,
    Body,
    ElseBody,
    IndentedStatement,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum CaseLikeRole {
    Scrutinee,
    Block,
    Arm,
    Pattern,
    Handler,
    Guard,
    Arrow,
    Body,
    Separator,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum BracedStatementBlockRole {
    Statement,
    Separator,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum PatternRole {
    Primary,
    SymbolName,
    AliasBinding,
    AlternationRhs,
    TypeAnnotation,
    ParenthesizedElement,
    ParenthesizedSeparator,
    ListItem,
    ListSpreadRhs,
    ListSeparator,
    RecordItem,
    RecordFieldName,
    RecordNestedPattern,
    RecordDefaultExpression,
    RecordSpreadRhs,
    RecordSeparator,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum TypeRole {
    Primary,
    PathSegment,
    CallArgument,
    CallArgumentSeparator,
    ApplyArgument,
    ArrowRhs,
    ParenthesizedItem,
    ParenthesizedSeparator,
    RecordField,
    RecordFieldName,
    RecordFieldColon,
    RecordFieldType,
    RecordFieldSeparator,
    ForallBinder,
    ForallBinderBoundary,
    ForallColon,
    ForallBody,
    EffectRowItem,
    EffectRowSeparator,
    BracketRowItem,
    BracketRowSeparator,
    LeadingEffectTypeHead,
    BracketRowArrow,
    PolymorphicVariantTag,
    PolymorphicVariantTagName,
    PolymorphicVariantPayload,
    PolymorphicVariantPayloadBoundary,
    PolymorphicVariantTagSeparator,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum LayoutRole {
    InlineTrivia,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum EmbeddedRole {
    Body,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum TokenRole {
    Punctuation,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum RecoveryKind {
    Missing,
    Error,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum UnexpectedSyntax {
    EndOfInput {
        at: usize,
    },
    Token {
        range: Range<usize>,
        category: UnexpectedCategory,
    },
    Root(RootUnexpected),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum UnexpectedCategory {
    Word,
    DecimalInteger,
    OperatorLike,
    Punctuation(PunctuationEvidence),
    OtherCharacter,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum PunctuationEvidence {
    Open(Delimiter),
    Close(Delimiter),
    Comma,
    Semicolon,
    Dot,
    Slash,
    Colon,
    ColonColon,
    Equals,
    Star,
    Apostrophe,
    Backslash,
    Arrow,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum RootUnexpected {
    UnrecognizedStarter {
        range: Range<usize>,
        head: RootUnexpectedHead,
    },
    TrailingInput {
        owner: StatementKind,
        range: Range<usize>,
        head: RootUnexpectedHead,
    },
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum RootUnexpectedHead {
    Word,
    DecimalInteger,
    OperatorLike,
    Punctuation(PunctuationEvidence),
    OtherCharacter,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum ExpectedSyntax {
    Identifier,
    TypePayloadBoundary,
    Path,
    Expression,
    Pattern,
    TypeExpression,
    TypePathSegment,
    ForallTypeBinder,
    TypeBinderBoundary,
    Statement,
    StatementSeparator,
    OperatorName,
    BindingPower,
    InlineTrivia,
    DelimitedSequenceSeparator,
    Keyword(KeywordEvidence),
    Punctuation(PunctuationEvidence),
    Yumark(YumarkSyntaxEvidence),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum YumarkSyntaxEvidence {
    EmphasisMarker,
    StrongMarker,
    FenceMarker,
    QuoteFenceMarker,
    SectionCloseMarker,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum KeywordEvidence {
    Use,
    Mod,
    Struct,
    Type,
    As,
    Without,
    With,
    Lazy,
    Prefix,
    Infix,
    Suffix,
    Nullfix,
    If,
    Elsif,
    Else,
}

#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub(crate) struct ExpectationSources(u8);

impl ExpectationSources {
    pub(crate) const SPECULATIVE: Self = Self(1);
    pub(crate) const COMMITTED_RECOVERY_RULE: Self = Self(1 << 1);

    pub(crate) fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct SyntaxExpectation {
    pub(crate) role: GrammarRole,
    pub(crate) expected: ExpectedSyntax,
    pub(crate) range: Range<usize>,
    pub(crate) sources: ExpectationSources,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct RecoverySiteKey {
    pub(crate) role: GrammarRole,
    pub(crate) range: Range<usize>,
}

/// Revision-local recovery identity. Allocation remains session-owned.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct DiagnosticId(pub(crate) u32);

/// Recovery data is committed only after a recovery path has been selected.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CommittedRecoveryRecord {
    pub(crate) id: DiagnosticId,
    pub(crate) site: RecoverySiteKey,
    pub(crate) kind: RecoveryKind,
    pub(crate) unexpected: Arc<[UnexpectedSyntax]>,
    pub(crate) expectations: Arc<[SyntaxExpectation]>,
    pub(crate) primary_expectation: usize,
}

impl CommittedRecoveryRecord {
    pub(crate) fn new(
        local: &mut ParseLocal,
        site: RecoverySiteKey,
        kind: RecoveryKind,
        unexpected: Arc<[UnexpectedSyntax]>,
        expectations: Arc<[SyntaxExpectation]>,
        primary_expectation: usize,
    ) -> Self {
        assert!(
            !expectations.is_empty(),
            "a committed recovery requires an expectation union"
        );
        assert!(
            primary_expectation < expectations.len(),
            "the primary expectation must index the expectation union"
        );
        match kind {
            RecoveryKind::Missing => assert_eq!(site.range.start, site.range.end),
            RecoveryKind::Error => {
                assert!(site.range.start < site.range.end);
                assert!(unexpected.iter().any(|unexpected| {
                    !matches!(unexpected, UnexpectedSyntax::EndOfInput { .. })
                }));
            }
        }
        if let Some(reused) = local.take_reusable_recovery(&site, kind) {
            // A matching header-origin site owns its diagnostic identity and
            // frozen expectation union. Recheck the full parse's evidence,
            // then carry that record forward unchanged.
            assert_eq!(reused.unexpected, unexpected);
            assert_eq!(reused.expectations, expectations);
            assert_eq!(reused.primary_expectation, primary_expectation);
            return reused;
        }
        Self {
            id: local.next_diagnostic_id(),
            site,
            kind,
            unexpected,
            expectations,
            primary_expectation,
        }
    }
}

/// Operations available to a continuation after its grammar branch commits.
///
/// Header and full outputs implement the same interface, so shared
/// continuations monomorphize without a mode branch for every token.
pub(crate) trait CommitOutput<'source> {
    type Checkpoint: Copy;

    fn checkpoint(&mut self) -> Self::Checkpoint;
    fn start_node(&mut self, kind: SyntaxKind);
    fn start_node_at(&mut self, checkpoint: Self::Checkpoint, kind: SyntaxKind);
    fn token(&mut self, kind: SyntaxKind, range: Range<usize>);
    fn emit_trivia(&mut self, trivia: &TriviaRun);
    fn finish_node(&mut self);
    fn commit_recovery(&mut self, record: CommittedRecoveryRecord);
    fn emit_missing(&mut self, record: CommittedRecoveryRecord);
    fn emit_error(&mut self, record: CommittedRecoveryRecord);
}

mod direct_cst_sink {
    pub(crate) trait Sealed {}
}

/// Sealed direct-emission interface implemented only by the Rowan sink.
///
/// This is intentionally not an empty marker: scanner code cannot gain CST
/// emission merely by adding a trait bound. Only [`FullCstOutput`] exposes
/// these operations through a committed continuation.
pub(crate) trait DirectCstSink: direct_cst_sink::Sealed {
    type Checkpoint: Copy;

    fn checkpoint(&mut self) -> Self::Checkpoint;
    fn start_node(&mut self, kind: SyntaxKind);
    fn start_node_at(&mut self, checkpoint: Self::Checkpoint, kind: SyntaxKind);
    fn token(&mut self, kind: SyntaxKind, range: Range<usize>);
    fn finish_node(&mut self);
}

impl direct_cst_sink::Sealed for RowanSink<'_> {}

impl DirectCstSink for RowanSink<'_> {
    type Checkpoint = rowan::Checkpoint;

    fn checkpoint(&mut self) -> Self::Checkpoint {
        RowanSink::checkpoint(self)
    }

    fn start_node(&mut self, kind: SyntaxKind) {
        RowanSink::start_node(self, kind);
    }

    fn start_node_at(&mut self, checkpoint: Self::Checkpoint, kind: SyntaxKind) {
        RowanSink::start_node_at(self, checkpoint, kind);
    }

    fn token(&mut self, kind: SyntaxKind, range: Range<usize>) {
        RowanSink::token_range(self, kind, range);
    }

    fn finish_node(&mut self) {
        RowanSink::finish_node(self);
    }
}

/// Direct-CST output for a full parse session.
pub(crate) struct FullCstOutput<'source> {
    sink: RowanSink<'source>,
    committed_recoveries: Vec<CommittedRecoveryRecord>,
}

impl<'source> FullCstOutput<'source> {
    pub(crate) fn new(source: &'source str) -> Self {
        Self {
            sink: RowanSink::new(source),
            committed_recoveries: Vec::new(),
        }
    }

    pub(crate) fn finish_complete(self) -> rowan::GreenNode {
        self.sink.finish_complete()
    }

    /// Test-only completion for an isolated sequence shell whose caller-owned
    /// remainder is intentionally not emitted by the shell under test.
    #[cfg(test)]
    pub(crate) fn finish_prefix(self) -> rowan::GreenNode {
        self.sink.finish()
    }

    pub(crate) fn committed_recoveries(&self) -> &[CommittedRecoveryRecord] {
        &self.committed_recoveries
    }
}

impl<'source> CommitOutput<'source> for FullCstOutput<'source> {
    type Checkpoint = <RowanSink<'source> as DirectCstSink>::Checkpoint;

    fn checkpoint(&mut self) -> Self::Checkpoint {
        DirectCstSink::checkpoint(&mut self.sink)
    }

    fn start_node(&mut self, kind: SyntaxKind) {
        DirectCstSink::start_node(&mut self.sink, kind);
    }

    fn start_node_at(&mut self, checkpoint: Self::Checkpoint, kind: SyntaxKind) {
        DirectCstSink::start_node_at(&mut self.sink, checkpoint, kind);
    }

    fn token(&mut self, kind: SyntaxKind, range: Range<usize>) {
        DirectCstSink::token(&mut self.sink, kind, range);
    }

    fn emit_trivia(&mut self, trivia: &TriviaRun) {
        self.sink.emit_trivia(trivia);
    }

    fn finish_node(&mut self) {
        DirectCstSink::finish_node(&mut self.sink);
    }

    fn commit_recovery(&mut self, record: CommittedRecoveryRecord) {
        self.committed_recoveries.push(record);
    }

    fn emit_missing(&mut self, record: CommittedRecoveryRecord) {
        assert_eq!(record.kind, RecoveryKind::Missing);
        DirectCstSink::start_node(&mut self.sink, SyntaxKind::Missing);
        DirectCstSink::finish_node(&mut self.sink);
        self.commit_recovery(record);
    }

    fn emit_error(&mut self, record: CommittedRecoveryRecord) {
        assert_eq!(record.kind, RecoveryKind::Error);
        let range = record.site.range.clone();
        DirectCstSink::start_node(&mut self.sink, SyntaxKind::Error);
        DirectCstSink::token(&mut self.sink, SyntaxKind::Unknown, range);
        DirectCstSink::finish_node(&mut self.sink);
        self.commit_recovery(record);
    }
}

/// Header-mode output keeps continuation control flow without building a CST.
pub(crate) struct HeaderOutput {
    committed_recoveries: Vec<CommittedRecoveryRecord>,
}

impl HeaderOutput {
    pub(crate) fn new() -> Self {
        Self {
            committed_recoveries: Vec::new(),
        }
    }

    pub(crate) fn committed_recoveries(&self) -> &[CommittedRecoveryRecord] {
        &self.committed_recoveries
    }
}

impl<'source> CommitOutput<'source> for HeaderOutput {
    type Checkpoint = ();

    fn checkpoint(&mut self) -> Self::Checkpoint {}

    fn start_node(&mut self, _: SyntaxKind) {}

    fn start_node_at(&mut self, _: Self::Checkpoint, _: SyntaxKind) {}

    fn token(&mut self, _: SyntaxKind, _: Range<usize>) {}

    fn emit_trivia(&mut self, _: &TriviaRun) {}

    fn finish_node(&mut self) {}

    fn commit_recovery(&mut self, record: CommittedRecoveryRecord) {
        self.committed_recoveries.push(record);
    }

    fn emit_missing(&mut self, record: CommittedRecoveryRecord) {
        assert_eq!(record.kind, RecoveryKind::Missing);
        self.commit_recovery(record);
    }

    fn emit_error(&mut self, record: CommittedRecoveryRecord) {
        assert_eq!(record.kind, RecoveryKind::Error);
        self.commit_recovery(record);
    }
}

/// Access available only after a branch or recovery path has been committed.
pub(crate) struct Committed<'parse, 'source, 'local, E: ErrorSink<usize>, O: CommitOutput<'source>>
{
    probe: Probe<'parse, 'source, 'local, E>,
    output: O,
}

impl<'parse, 'source, 'local, E: ErrorSink<usize>, O: CommitOutput<'source>>
    Committed<'parse, 'source, 'local, E, O>
{
    /// Temporarily reborrows the sink-free capability.
    ///
    /// The output stays inaccessible until `recognize` returns, keeping
    /// scanner probes and direct emission in separate phases.
    pub(crate) fn probe<R>(
        &mut self,
        recognize: impl FnOnce(&mut Probe<'parse, 'source, 'local, E>) -> R,
    ) -> R {
        recognize(&mut self.probe)
    }

    pub(crate) fn checkpoint(&mut self) -> O::Checkpoint {
        self.output.checkpoint()
    }

    pub(crate) fn start_node(&mut self, kind: SyntaxKind) {
        self.output.start_node(kind);
    }

    pub(crate) fn start_node_at(&mut self, checkpoint: O::Checkpoint, kind: SyntaxKind) {
        self.output.start_node_at(checkpoint, kind);
    }

    pub(crate) fn token(&mut self, kind: SyntaxKind, range: Range<usize>) {
        self.output.token(kind, range);
    }

    pub(crate) fn emit_trivia(&mut self, trivia: &TriviaRun) {
        self.output.emit_trivia(trivia);
    }

    pub(crate) fn finish_node(&mut self) {
        self.output.finish_node();
    }

    pub(crate) fn commit_recovery(&mut self, record: CommittedRecoveryRecord) {
        self.output.commit_recovery(record);
    }

    pub(crate) fn emit_missing(&mut self, record: CommittedRecoveryRecord) {
        self.output.emit_missing(record);
    }

    pub(crate) fn emit_error(&mut self, record: CommittedRecoveryRecord) {
        self.output.emit_error(record);
    }

    pub(crate) fn emit_canonical_recovery_fact(&mut self, fact: YumarkEmbeddedRecoveryFact) {
        let kind = fact.kind;
        let unexpected = match kind {
            RecoveryKind::Missing => Arc::from([]),
            RecoveryKind::Error => Arc::from([UnexpectedSyntax::Token {
                range: fact.range.clone(),
                category: fact
                    .unexpected
                    .unwrap_or(UnexpectedCategory::OtherCharacter),
            }]),
        };
        let record = self.probe(|probe| {
            CommittedRecoveryRecord::new(
                probe.input().local,
                RecoverySiteKey {
                    role: fact.spec.role,
                    range: fact.range.clone(),
                },
                kind,
                unexpected,
                Arc::from([SyntaxExpectation {
                    role: fact.spec.role,
                    expected: fact.spec.expected,
                    range: fact.range,
                    sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
                }]),
                0,
            )
        });
        match kind {
            RecoveryKind::Missing => self.emit_missing(record),
            RecoveryKind::Error => self.emit_error(record),
        }
    }

    pub(crate) fn into_output(self) -> O {
        self.output
    }
}

/// Stack mutations carry inverse operations; checkpoints copy only two lengths.
struct RollbackStack<T> {
    values: Vec<T>,
    undo: Vec<StackUndo<T>>,
}

impl<T> RollbackStack<T> {
    fn new() -> Self {
        Self {
            values: Vec::new(),
            undo: Vec::new(),
        }
    }

    fn checkpoint(&self) -> StackCheckpoint {
        StackCheckpoint {
            depth: self.values.len(),
            undo_len: self.undo.len(),
        }
    }

    fn push(&mut self, value: T) {
        self.values.push(value);
        self.undo.push(StackUndo::Pop);
    }

    fn last(&self) -> Option<&T> {
        self.values.last()
    }

    fn len(&self) -> usize {
        self.values.len()
    }

    fn values(&self) -> &[T] {
        &self.values
    }
}

impl<T: Clone> RollbackStack<T> {
    fn pop(&mut self) -> Option<T> {
        let value = self.values.pop()?;
        self.undo.push(StackUndo::Push(value.clone()));
        Some(value)
    }

    fn replace_last(&mut self, value: T) {
        let last = self
            .values
            .last_mut()
            .expect("cannot replace the top of an empty rollback stack");
        let old = std::mem::replace(last, value);
        self.undo.push(StackUndo::Replace(old));
    }

    fn rollback(&mut self, checkpoint: StackCheckpoint) {
        while self.undo.len() > checkpoint.undo_len {
            match self.undo.pop().expect("undo length was checked") {
                StackUndo::Pop => {
                    self.values.pop();
                }
                StackUndo::Push(value) => self.values.push(value),
                StackUndo::Replace(value) => {
                    *self
                        .values
                        .last_mut()
                        .expect("rollback replacement requires a stack frame") = value;
                }
            }
        }
        debug_assert_eq!(self.values.len(), checkpoint.depth);
    }
}

enum StackUndo<T> {
    Pop,
    Push(T),
    Replace(T),
}

#[derive(Clone, Copy)]
struct StackCheckpoint {
    depth: usize,
    undo_len: usize,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::input::SourceInput;
    use chasa::Input;
    use std::sync::Arc;

    fn recovery_record(kind: RecoveryKind, range: Range<usize>) -> CommittedRecoveryRecord {
        let mut local = ParseLocal::new();
        let unexpected = match kind {
            RecoveryKind::Missing => Arc::from([]),
            RecoveryKind::Error => Arc::from([UnexpectedSyntax::Token {
                range: range.clone(),
                category: UnexpectedCategory::OtherCharacter,
            }]),
        };
        CommittedRecoveryRecord::new(
            &mut local,
            RecoverySiteKey {
                role: GrammarRole::Statement(StatementRole::Starter),
                range,
            },
            kind,
            unexpected,
            Arc::from([SyntaxExpectation {
                role: GrammarRole::Statement(StatementRole::Starter),
                expected: ExpectedSyntax::Expression,
                range: 0..0,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    }

    #[test]
    fn full_output_emits_recovery_node_shapes_and_commits_their_records() {
        let mut missing = FullCstOutput::new("");
        missing.start_node(SyntaxKind::Root);
        missing.emit_missing(recovery_record(RecoveryKind::Missing, 0..0));
        missing.finish_node();
        assert_eq!(missing.committed_recoveries().len(), 1);
        let green = missing.finish_complete();
        let missing_node = green.children().next().expect("missing child node");
        assert_eq!(missing_node.kind(), SyntaxKind::Missing.into());

        let mut error = FullCstOutput::new("?");
        error.start_node(SyntaxKind::Root);
        error.emit_error(recovery_record(RecoveryKind::Error, 0..1));
        error.finish_node();
        assert_eq!(error.committed_recoveries().len(), 1);
        assert_eq!(error.finish_complete().to_string(), "?");
    }

    #[test]
    #[should_panic(expected = "a committed recovery requires an expectation union")]
    fn recovery_records_reject_an_empty_expectation_union() {
        let mut local = ParseLocal::new();
        let _ = CommittedRecoveryRecord::new(
            &mut local,
            RecoverySiteKey {
                role: GrammarRole::Statement(StatementRole::Starter),
                range: 0..0,
            },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([]),
            0,
        );
    }

    #[test]
    fn parse_environment_separates_header_and_full_mode_inputs() {
        let header_mode = ParseEnv::header("");
        assert_eq!(header_mode.source(), "");
        assert_eq!(header_mode.mode(), ParseMode::Header);
        assert!(header_mode.syntax_environment().is_none());
        assert!(header_mode.operators().is_none());
        assert!(header_mode.header_info().is_none());

        let syntax_environment = SyntaxEnvironment::empty();
        let operators = OperatorTable::empty();
        let header = crate::scan_header(Arc::from(""));
        let full_mode = ParseEnv::full("", &syntax_environment, &operators, &header);
        assert_eq!(full_mode.mode(), ParseMode::Full);
        assert!(full_mode.syntax_environment().is_some());
        assert!(full_mode.operators().is_some());
        assert!(full_mode.header_info().is_some());
    }

    #[test]
    fn stop_set_widening_preserves_existing_bits_and_appends_declaration_vocabulary() {
        let expected = [
            StopKind::Newline,
            StopKind::Comma,
            StopKind::Semicolon,
            StopKind::Colon,
            StopKind::LeftBrace,
            StopKind::Elsif,
            StopKind::Else,
            StopKind::RightParenthesis,
            StopKind::RightBracket,
            StopKind::RightBrace,
            StopKind::Equal,
            StopKind::Arrow,
            StopKind::ArmGuardIf,
            StopKind::ArmGuardWhere,
            StopKind::With,
            StopKind::Derives,
            StopKind::Via,
            StopKind::In,
            StopKind::Impl,
            StopKind::LeftParenthesis,
            StopKind::Pipe,
        ];
        assert_eq!(StopKind::ALL, expected.as_slice());
        for (bit, stop) in StopKind::ALL.iter().copied().enumerate() {
            assert_eq!(stop as u8, bit as u8);
            let singleton = StopSet::default().with(stop);
            assert!(singleton.contains(stop));
            assert_eq!(singleton.without(stop), StopSet::default());
        }

        let existing = StopSet::default()
            .with(StopKind::Newline)
            .with(StopKind::With);
        assert_eq!(existing.0, (1u32 << 0) | (1u32 << 14));
        let extended = existing
            .with(StopKind::Derives)
            .with(StopKind::Via)
            .with(StopKind::In)
            .with(StopKind::Impl)
            .with(StopKind::LeftParenthesis);
        assert_eq!(
            extended.0,
            (1u32 << 0)
                | (1u32 << 14)
                | (1u32 << 15)
                | (1u32 << 16)
                | (1u32 << 17)
                | (1u32 << 18)
                | (1u32 << 19)
        );
        assert_eq!(
            extended.difference(existing),
            StopSet::default()
                .with(StopKind::Derives)
                .with(StopKind::Via)
                .with(StopKind::In)
                .with(StopKind::Impl)
                .with(StopKind::LeftParenthesis)
        );
    }

    #[test]
    fn yumark_recovery_vocabulary_is_closed_and_source_ordered() {
        assert_eq!(
            YumarkOwner::ALL,
            [
                YumarkOwner::DocComment,
                YumarkOwner::Section,
                YumarkOwner::List,
                YumarkOwner::ListItem,
                YumarkOwner::Quote,
                YumarkOwner::CodeFence,
                YumarkOwner::InlineGroup,
                YumarkOwner::InlineLink,
                YumarkOwner::InlineImage,
                YumarkOwner::InlineApply,
                YumarkOwner::InlineReference,
                YumarkOwner::Emphasis,
                YumarkOwner::Strong,
                YumarkOwner::Command,
                YumarkOwner::My,
                YumarkOwner::Use,
                YumarkOwner::DocArgument,
                YumarkOwner::DoCapture,
                YumarkOwner::IfChain,
                YumarkOwner::IfBranch,
                YumarkOwner::ElsifBranch,
                YumarkOwner::ElseBranch,
            ]
        );
        assert_eq!(
            YumarkSlot::ALL,
            [
                YumarkSlot::Starter,
                YumarkSlot::Name,
                YumarkSlot::Head,
                YumarkSlot::Arguments,
                YumarkSlot::Condition,
                YumarkSlot::BodyIntroducer,
                YumarkSlot::Body,
                YumarkSlot::Destination,
                YumarkSlot::BranchPredecessor,
                YumarkSlot::ClosingDelimiter,
                YumarkSlot::SectionClose,
                YumarkSlot::QuoteForm,
                YumarkSlot::ExpressionBody,
                YumarkSlot::Route,
                YumarkSlot::Terminator,
            ]
        );
        assert_eq!(
            GrammarRole::Yumark(YumarkRole {
                owner: YumarkOwner::My,
                slot: YumarkSlot::ExpressionBody,
            }),
            GrammarRole::Yumark(YumarkRole {
                owner: YumarkOwner::My,
                slot: YumarkSlot::ExpressionBody,
            })
        );
    }

    #[test]
    fn yumark_frame_push_mutate_and_pop_roll_back_in_full_snapshot() {
        let mut local = ParseLocal::new();
        local.push_yumark_frame(YumarkFrame::Document {
            base: 0,
            envelope_stop: YumarkEnvelopeStop::BlockDocument,
        });
        let before = local.value_snapshot();
        let checkpoint = local.checkpoint();

        local.replace_yumark_frame(YumarkFrame::IfChain {
            indent: 2,
            seen_else: true,
        });
        local.push_yumark_frame(YumarkFrame::ListItem {
            marker: 8..10,
            indent: 2,
            content_column: 4,
        });
        assert_eq!(
            local.pop_yumark_frame(),
            Some(YumarkFrame::ListItem {
                marker: 8..10,
                indent: 2,
                content_column: 4,
            })
        );
        let delimiter_floor = local.push_yumark_delimiter(Delimiter::Parenthesis);
        local.push_yumark_frame(YumarkFrame::EmbeddedYulang {
            owner: YumarkOwner::Use,
            outer_kind: YumarkEmbeddedOuterKind::RequiredSemicolon,
            delimiter_floor,
        });

        local.rollback(checkpoint);

        assert_eq!(local.value_snapshot(), before);
        assert_eq!(local.yumark_frame_depth(), 1);
        assert_eq!(
            local.yumark_frame(),
            Some(&YumarkFrame::Document {
                base: 0,
                envelope_stop: YumarkEnvelopeStop::BlockDocument,
            })
        );
    }

    #[test]
    fn yumark_nested_checkpoints_restore_and_release_superseded_heads() {
        let mut local = ParseLocal::new();
        local.push_yumark_frame(YumarkFrame::Document {
            base: 0,
            envelope_stop: YumarkEnvelopeStop::BlockDocument,
        });
        let outer_snapshot = local.value_snapshot();
        let outer = local.checkpoint();

        local.push_yumark_frame(YumarkFrame::ImplicitSection { level: 1 });
        let nested_snapshot = local.value_snapshot();
        let nested = local.checkpoint();
        local.replace_yumark_frame(YumarkFrame::IfChain {
            indent: 2,
            seen_else: false,
        });
        local.push_yumark_frame(YumarkFrame::List { indent: 2 });
        local.rollback(nested);
        assert_eq!(local.value_snapshot(), nested_snapshot);

        let retained = local.checkpoint();
        let retained_clone = retained.clone();
        let superseded = Arc::downgrade(
            local
                .yumark_frames
                .head
                .as_ref()
                .expect("the section frame is present"),
        );
        local.replace_yumark_frame(YumarkFrame::RawFence {
            marker: 12..15,
            indent: 0,
        });
        drop(retained);
        assert!(superseded.upgrade().is_some());
        drop(retained_clone);
        assert!(superseded.upgrade().is_none());

        local.rollback(outer);
        assert_eq!(local.value_snapshot(), outer_snapshot);
    }

    #[test]
    fn checkpoint_restores_the_complete_speculative_state_inventory() {
        const IF_WORDS: &[&str] = &["elsif", "else"];

        let mut local = ParseLocal::new();
        local.set_line(LineState {
            last_newline: Some((2, 3)),
            line_start: 3,
            line_indent: 2,
            at_line_start: true,
        });
        local.push_indentation_baseline(IndentationBaseline {
            column: 2,
            kind: IndentationBaselineKind::Block,
        });
        local.push_stop_set(StopSet::default().with(StopKind::Newline));
        local.push_delimiter(Delimiter::Parenthesis);
        local.push_expression_delimited_owner(ExpressionDelimitedOwner::Call);
        let initial_type_episode =
            local.push_type_expression_episode(TypeExpressionEpisodePolicy::default());
        local.push_type_expression_scoped_stop_frame(TypeExpressionScopedStopFrame {
            stops: StopSet::default().with(StopKind::Semicolon),
            visible_episode_depth: initial_type_episode,
        });
        local.push_lexical_mode(EmbeddedLexicalMode::BlockComment { depth: 1 });
        let initial_if = local.push_if_expression_companion(0, IF_WORDS);
        local.push_root_statement_ambient_scope();
        local.stage_header_fact(StagedHeaderFact::Import);
        local.begin_operator_probe(OperatorCandidateProbe {
            start: 4,
            candidate_end: 5,
        });

        let checkpoint = local.checkpoint();

        local.set_line(LineState {
            last_newline: Some((8, 9)),
            line_start: 9,
            line_indent: 6,
            at_line_start: false,
        });
        local.push_indentation_baseline(IndentationBaseline {
            column: 6,
            kind: IndentationBaselineKind::Introducer,
        });
        local.set_inline(true);
        local.set_ml_arg(true);
        local.replace_stop_set(
            StopSet::default()
                .with(StopKind::Comma)
                .with(StopKind::RightBrace),
        );
        assert_eq!(local.pop_delimiter(), Some(Delimiter::Parenthesis));
        local.push_delimiter(Delimiter::Bracket);
        assert_eq!(
            local.pop_expression_delimited_owner(),
            Some(ExpressionDelimitedOwner::Call)
        );
        local.push_expression_delimited_owner(ExpressionDelimitedOwner::Index);
        local.push_type_expression_episode(TypeExpressionEpisodePolicy {
            fresh_primary_locally_owned_stops: StopSet::default().with(StopKind::Comma),
            fresh_primary_owns_adjacent_polymorphic_variant_starter: false,
        });
        local.push_type_expression_scoped_stop_frame(TypeExpressionScopedStopFrame {
            stops: StopSet::default().with(StopKind::Comma),
            visible_episode_depth: local.type_expression_episode_depth(),
        });
        local.replace_lexical_mode(EmbeddedLexicalMode::Interpolation { delimiter_depth: 2 });
        local.push_lexical_mode(EmbeddedLexicalMode::Heredoc { quote_count: 3 });
        let speculative_if = local.push_if_expression_companion(6, IF_WORDS);
        local.push_inline_canonical_statement_ambient_scope(InlineStatementOwnerKind::WithBodyTail);
        local.stage_header_fact(StagedHeaderFact::Operator);
        local.begin_operator_probe(OperatorCandidateProbe {
            start: 4,
            candidate_end: 6,
        });

        local.rollback(checkpoint);

        assert_eq!(
            local.line(),
            LineState {
                last_newline: Some((2, 3)),
                line_start: 3,
                line_indent: 2,
                at_line_start: true,
            }
        );
        assert_eq!(
            local.indentation_baseline(),
            Some(IndentationBaseline {
                column: 2,
                kind: IndentationBaselineKind::Block,
            })
        );
        assert!(!local.inline());
        assert!(!local.ml_arg());
        assert_eq!(
            local.stop_set(),
            Some(StopSet::default().with(StopKind::Newline))
        );
        assert_eq!(local.delimiter(), Some(Delimiter::Parenthesis));
        assert_eq!(
            local.expression_delimited_owner(),
            Some(ExpressionDelimitedOwner::Call)
        );
        assert_eq!(local.type_expression_episode_depth(), initial_type_episode);
        assert_eq!(
            local.type_expression_episode_policy(),
            Some(TypeExpressionEpisodePolicy::default()),
        );
        assert_eq!(
            local
                .type_expression_scoped_stop_frames()
                .copied()
                .collect::<Vec<_>>(),
            vec![TypeExpressionScopedStopFrame {
                stops: StopSet::default().with(StopKind::Semicolon),
                visible_episode_depth: initial_type_episode,
            }],
        );
        assert_eq!(
            local.lexical_mode(),
            Some(EmbeddedLexicalMode::BlockComment { depth: 1 })
        );
        assert_eq!(local.ambient_owner_scope_depth(), 1);
        assert_eq!(
            local.ambient_owner_scope(),
            Some(AmbientOwnerScopeFrame::root_statement())
        );
        assert_eq!(local.if_expression_companion_depth(), 1);
        assert_eq!(
            local.if_expression_companion(),
            Some(IfExpressionCompanionFrame {
                id: initial_if,
                if_base_indent: 0,
                exact_words: IF_WORDS,
            })
        );
        assert_eq!(
            local.push_if_expression_companion(6, IF_WORDS),
            speculative_if,
        );
        assert_eq!(local.staged_header_fact_count(), 1);
        assert_eq!(local.operator_probe_count(), 1);
    }

    #[test]
    fn checkpoint_restores_type_malformed_caller_boundary_fence() {
        let mut local = ParseLocal::new();
        assert_eq!(local.type_malformed_caller_boundary(), None);

        local.set_type_malformed_caller_boundary(Some(TypeMalformedCallerBoundaryFence {
            trivia_start: 3,
        }));
        let checkpoint = local.checkpoint();
        local.set_type_malformed_caller_boundary(Some(TypeMalformedCallerBoundaryFence {
            trivia_start: 8,
        }));

        local.rollback(checkpoint);

        assert_eq!(
            local.type_malformed_caller_boundary(),
            Some(TypeMalformedCallerBoundaryFence { trivia_start: 3 })
        );
    }

    #[test]
    fn chasa_input_checkpoint_rolls_back_input_and_parse_local_together() {
        let mut input = SourceInput::new("あ\n  x");
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let input = chasa::input::In::new(
            &mut input,
            &mut expectations,
            chasa::input::IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        let mut input = input;
        let checkpoint = input.checkpoint();

        assert_eq!(input.input.next(), Some('あ'));
        input.local.set_line(LineState {
            last_newline: Some((3, 4)),
            line_start: 4,
            line_indent: 2,
            at_line_start: true,
        });
        input.local.push_delimiter(Delimiter::Brace);

        input.rollback(checkpoint);

        assert_eq!(input.pos(), 0);
        assert_eq!(input.local.line(), LineState::default());
        assert_eq!(input.local.delimiter(), None);
    }

    #[test]
    fn ambient_owner_queries_are_empty_without_statement_or_if_frames() {
        let mut source = SourceInput::new("\nelse");
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = chasa::input::In::new(
            &mut source,
            &mut expectations,
            chasa::input::IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        assert!(!any_ambient_owner_claims(&mut i));
        assert_eq!(if_continuation_owner(&mut i), None);
        assert_eq!(i.pos(), 0);
        assert_eq!(i.local.line(), LineState::default());
        assert_eq!(i.local.ambient_owner_scope_depth(), 0);
        assert_eq!(i.local.if_expression_companion_depth(), 0);

        drop(i);
        assert!(!is_cut);
    }

    #[test]
    fn ambient_owner_queries_use_the_nearest_visible_baseline_and_barrier() {
        let mut local = ParseLocal::new();
        local.push_root_statement_ambient_scope();
        local.push_inline_canonical_statement_ambient_scope(InlineStatementOwnerKind::ModColonBody);
        local.push_indented_statement_ambient_scope(4);
        assert_eq!(local.nearest_visible_statement_baseline(), Some(4));

        let mut source = SourceInput::new("\n  value");
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = chasa::input::In::new(
            &mut source,
            &mut expectations,
            chasa::input::IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        assert!(any_ambient_owner_claims(&mut i));
        assert_eq!(i.pos(), 0);
        assert_eq!(i.local.line(), LineState::default());
        drop(i);

        local
            .push_braced_ambient_owner_barrier(BracedBarrierOrigin::BracedStatementBlockExpression);
        assert_eq!(local.nearest_visible_statement_baseline(), None);
        let mut source = SourceInput::new("\n  value");
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = chasa::input::In::new(
            &mut source,
            &mut expectations,
            chasa::input::IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        assert!(!any_ambient_owner_claims(&mut i));
        assert_eq!(i.pos(), 0);
        assert_eq!(i.local.line(), LineState::default());
    }

    #[test]
    fn if_continuation_owner_keeps_identity_visibility_and_probe_rollback_exact() {
        const IF_WORDS: &[&str] = &["elsif", "else"];

        let mut local = ParseLocal::new();
        local.push_indentation_baseline(IndentationBaseline {
            column: 3,
            kind: IndentationBaselineKind::Block,
        });
        local.push_stop_set(StopSet::default().with(StopKind::Newline));
        local.push_delimiter(Delimiter::Parenthesis);
        local.push_expression_delimited_owner(ExpressionDelimitedOwner::Call);
        local.push_type_delimited_owner(TypeDelimitedOwner::Call);
        local.push_lexical_mode(EmbeddedLexicalMode::BlockComment { depth: 1 });
        local.push_root_statement_ambient_scope();
        let outer = local.push_if_expression_companion(0, IF_WORDS);
        let inner = local.push_if_expression_companion(5, IF_WORDS);

        let mut source = SourceInput::new("\nelse");
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = chasa::input::In::new(
            &mut source,
            &mut expectations,
            chasa::input::IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        assert_eq!(if_continuation_owner(&mut i), Some(outer));
        assert!(any_ambient_owner_claims(&mut i));
        assert_eq!(i.pos(), 0);
        assert_eq!(i.local.line(), LineState::default());
        assert_eq!(
            i.local
                .indentation_baseline()
                .map(|baseline| baseline.column),
            Some(3)
        );
        assert_eq!(
            i.local.stop_set(),
            Some(StopSet::default().with(StopKind::Newline))
        );
        assert_eq!(i.local.delimiter(), Some(Delimiter::Parenthesis));
        assert_eq!(
            i.local.expression_delimited_owner(),
            Some(ExpressionDelimitedOwner::Call)
        );
        assert_eq!(
            i.local.type_delimited_owner(),
            Some(TypeDelimitedOwner::Call)
        );
        assert_eq!(
            i.local.lexical_mode(),
            Some(EmbeddedLexicalMode::BlockComment { depth: 1 })
        );
        assert_eq!(i.local.ambient_owner_scope_depth(), 1);
        assert_eq!(i.local.if_expression_companion_depth(), 2);
        assert_eq!(
            i.local
                .if_expression_companion()
                .map(IfExpressionCompanionFrame::id),
            Some(inner)
        );
        drop(i);
        assert!(!is_cut);

        local.push_braced_ambient_owner_barrier(BracedBarrierOrigin::CatchBracedArmSequence);
        let mut source = SourceInput::new(" else");
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = chasa::input::In::new(
            &mut source,
            &mut expectations,
            chasa::input::IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        assert_eq!(if_continuation_owner(&mut i), None);
        assert!(!any_ambient_owner_claims(&mut i));
        assert_eq!(i.pos(), 0);
        drop(i);

        let visible_inner = local.push_if_expression_companion(0, IF_WORDS);
        let mut source = SourceInput::new(" else");
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = chasa::input::In::new(
            &mut source,
            &mut expectations,
            chasa::input::IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        assert_eq!(if_continuation_owner(&mut i), Some(visible_inner));
        assert_eq!(i.pos(), 0);
        assert_eq!(i.local.line(), LineState::default());
    }

    #[test]
    fn committed_capability_keeps_probe_sink_free_until_its_closure_returns() {
        use std::{cell::RefCell, rc::Rc};

        #[derive(Clone, Debug, Eq, PartialEq)]
        enum OutputCall {
            Start(SyntaxKind),
            Token(SyntaxKind, Range<usize>),
            Finish,
        }

        struct RecordingOutput {
            calls: Rc<RefCell<Vec<OutputCall>>>,
        }

        impl CommitOutput<'_> for RecordingOutput {
            type Checkpoint = usize;

            fn checkpoint(&mut self) -> Self::Checkpoint {
                self.calls.borrow().len()
            }

            fn start_node(&mut self, kind: SyntaxKind) {
                self.calls.borrow_mut().push(OutputCall::Start(kind));
            }

            fn start_node_at(&mut self, _: Self::Checkpoint, kind: SyntaxKind) {
                self.calls.borrow_mut().push(OutputCall::Start(kind));
            }

            fn token(&mut self, kind: SyntaxKind, range: Range<usize>) {
                self.calls.borrow_mut().push(OutputCall::Token(kind, range));
            }

            fn emit_trivia(&mut self, _: &TriviaRun) {}

            fn finish_node(&mut self) {
                self.calls.borrow_mut().push(OutputCall::Finish);
            }

            fn commit_recovery(&mut self, _: CommittedRecoveryRecord) {}

            fn emit_missing(&mut self, _: CommittedRecoveryRecord) {}

            fn emit_error(&mut self, _: CommittedRecoveryRecord) {}
        }

        let mut input = SourceInput::new("x");
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let i = chasa::input::In::new(
            &mut input,
            &mut expectations,
            chasa::input::IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        let calls = Rc::new(RefCell::new(Vec::new()));
        let probe = Probe::new(i);
        let mut committed = probe.commit(RecordingOutput {
            calls: Rc::clone(&calls),
        });

        committed.probe(|probe| {
            assert_eq!(probe.input().input.next(), Some('x'));
            probe.input().local.set_inline(true);
            assert!(calls.borrow().is_empty());
        });

        let checkpoint = committed.checkpoint();
        committed.start_node(SyntaxKind::Root);
        committed.start_node_at(checkpoint, SyntaxKind::IdentifierExpression);
        committed.token(SyntaxKind::Identifier, 0..1);
        committed.finish_node();

        assert!(local.inline());
        assert_eq!(
            calls.take(),
            vec![
                OutputCall::Start(SyntaxKind::Root),
                OutputCall::Start(SyntaxKind::IdentifierExpression),
                OutputCall::Token(SyntaxKind::Identifier, 0..1),
                OutputCall::Finish,
            ]
        );
    }
}
