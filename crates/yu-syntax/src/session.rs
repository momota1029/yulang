//! Immutable parse context and rollback-owned scanner/layout state.

use std::{ops::Range, sync::Arc};

use chasa::{Back, ErrorSink, prelude::In};

use crate::{
    HeaderInfo, input::SourceInput, operator::OperatorTable, parse::SyntaxEnvironment,
    scan::trivia::TriviaRun, sink::RowanSink, syntax_kind::SyntaxKind,
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
        let base_indent = if trivia_has_physical_newline(trivia) && following_indent > incoming_base {
            following_indent
        } else {
            incoming_base
        };
        Self { base_indent }
    }

    pub(crate) fn inline(incoming_base: usize) -> Self {
        Self { base_indent: incoming_base }
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
    trivia.parts().iter().any(|part| {
        matches!(part.kind(), crate::scan::trivia::TriviaPartKind::Newline)
    })
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

/// All mutable state whose value can affect a scanner or layout decision.
pub(crate) struct ParseLocal {
    line: LineState,
    indentation_baselines: RollbackStack<IndentationBaseline>,
    inline: bool,
    ml_arg: bool,
    type_ml_arg: bool,
    stop_sets: RollbackStack<StopSet>,
    delimiters: RollbackStack<Delimiter>,
    expression_delimited_owners: RollbackStack<ExpressionDelimitedOwner>,
    type_delimited_owners: RollbackStack<TypeDelimitedOwner>,
    lexical_modes: RollbackStack<EmbeddedLexicalMode>,
    staged_header_facts: Vec<StagedHeaderFact>,
    operator_probes: Vec<OperatorCandidateProbe>,
    reusable_recoveries: Vec<CommittedRecoveryRecord>,
    reused_recovery_indices: Vec<usize>,
    next_diagnostic_id: u32,
}

impl ParseLocal {
    pub(crate) fn new() -> Self {
        Self {
            line: LineState::default(),
            indentation_baselines: RollbackStack::new(),
            inline: false,
            ml_arg: false,
            type_ml_arg: false,
            stop_sets: RollbackStack::new(),
            delimiters: RollbackStack::new(),
            expression_delimited_owners: RollbackStack::new(),
            type_delimited_owners: RollbackStack::new(),
            lexical_modes: RollbackStack::new(),
            staged_header_facts: Vec::new(),
            operator_probes: Vec::new(),
            reusable_recoveries: Vec::new(),
            reused_recovery_indices: Vec::new(),
            next_diagnostic_id: 0,
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
            stop_sets: self.stop_sets.checkpoint(),
            delimiters: self.delimiters.checkpoint(),
            expression_delimited_owners: self.expression_delimited_owners.checkpoint(),
            type_delimited_owners: self.type_delimited_owners.checkpoint(),
            lexical_modes: self.lexical_modes.checkpoint(),
            staged_header_facts_len: self.staged_header_facts.len(),
            operator_probes_len: self.operator_probes.len(),
            reused_recovery_indices_len: self.reused_recovery_indices.len(),
            next_diagnostic_id: self.next_diagnostic_id,
        }
    }

    pub(crate) fn rollback(&mut self, checkpoint: ParseLocalCheckpoint) {
        self.line = checkpoint.line;
        self.indentation_baselines
            .rollback(checkpoint.indentation_baselines);
        self.inline = checkpoint.inline;
        self.ml_arg = checkpoint.ml_arg;
        self.type_ml_arg = checkpoint.type_ml_arg;
        self.stop_sets.rollback(checkpoint.stop_sets);
        self.delimiters.rollback(checkpoint.delimiters);
        self.expression_delimited_owners
            .rollback(checkpoint.expression_delimited_owners);
        self.type_delimited_owners
            .rollback(checkpoint.type_delimited_owners);
        self.lexical_modes.rollback(checkpoint.lexical_modes);
        self.staged_header_facts
            .truncate(checkpoint.staged_header_facts_len);
        self.operator_probes
            .truncate(checkpoint.operator_probes_len);
        self.reused_recovery_indices
            .truncate(checkpoint.reused_recovery_indices_len);
        self.next_diagnostic_id = checkpoint.next_diagnostic_id;
    }

    pub(crate) fn line(&self) -> LineState {
        self.line
    }

    pub(crate) fn set_line(&mut self, line: LineState) {
        self.line = line;
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

/// Small scalar/depth snapshot used by chasa together with its input checkpoint.
#[derive(Clone)]
pub(crate) struct ParseLocalCheckpoint {
    line: LineState,
    indentation_baselines: StackCheckpoint,
    inline: bool,
    ml_arg: bool,
    type_ml_arg: bool,
    stop_sets: StackCheckpoint,
    delimiters: StackCheckpoint,
    expression_delimited_owners: StackCheckpoint,
    type_delimited_owners: StackCheckpoint,
    lexical_modes: StackCheckpoint,
    staged_header_facts_len: usize,
    operator_probes_len: usize,
    reused_recovery_indices_len: usize,
    next_diagnostic_id: u32,
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
pub(crate) struct StopSet(u16);

impl StopSet {
    pub(crate) fn with(mut self, stop: StopKind) -> Self {
        self.0 |= 1 << (stop as u8);
        self
    }

    pub(crate) fn without(mut self, stop: StopKind) -> Self {
        self.0 &= !(1 << (stop as u8));
        self
    }

    pub(crate) fn contains(self, stop: StopKind) -> bool {
        self.0 & (1 << (stop as u8)) != 0
    }

    pub(crate) fn difference(self, other: Self) -> Self {
        Self(self.0 & !other.0)
    }
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
    PolymorphicVariant,
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
    Token(TokenRole),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum DeclarationRole {
    Import(ImportRole),
    OperatorHeader(OperatorHeaderRole),
    Binding(BindingRole),
    Mod(ModRole),
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
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum StatementRole {
    Starter,
    Separator,
    TrailingInput { owner: StatementKind },
    OperatorDefinitionBody,
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
    TypeCall,
    ParenthesizedTypeGroup,
    NamedRecordType,
    EffectRowType,
    PolymorphicVariantType,
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
    EndOfInput { at: usize },
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
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum KeywordEvidence {
    Use,
    Mod,
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
    fn checkpoint_restores_the_complete_speculative_state_inventory() {
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
        local.push_lexical_mode(EmbeddedLexicalMode::BlockComment { depth: 1 });
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
        local.replace_lexical_mode(EmbeddedLexicalMode::Interpolation { delimiter_depth: 2 });
        local.push_lexical_mode(EmbeddedLexicalMode::Heredoc { quote_count: 3 });
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
        assert_eq!(
            local.lexical_mode(),
            Some(EmbeddedLexicalMode::BlockComment { depth: 1 })
        );
        assert_eq!(local.staged_header_fact_count(), 1);
        assert_eq!(local.operator_probe_count(), 1);
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
