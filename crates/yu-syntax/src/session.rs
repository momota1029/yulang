//! Immutable parse context and rollback-owned scanner/layout state.

use chasa::{prelude::In, Back};

use crate::{
    HeaderInfo,
    input::SourceInput,
    operator::OperatorTable,
    parse::SyntaxEnvironment,
};

pub(crate) type SynIn<'a, 'source, 'b, E> =
    In<'a, SourceInput<'source>, (), &'b mut ParseLocal, E>;

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
    stop_sets: RollbackStack<StopSet>,
    delimiters: RollbackStack<Delimiter>,
    lexical_modes: RollbackStack<EmbeddedLexicalMode>,
    staged_header_facts: Vec<StagedHeaderFact>,
    operator_probes: Vec<OperatorCandidateProbe>,
}

impl ParseLocal {
    pub(crate) fn new() -> Self {
        Self {
            line: LineState::default(),
            indentation_baselines: RollbackStack::new(),
            inline: false,
            ml_arg: false,
            stop_sets: RollbackStack::new(),
            delimiters: RollbackStack::new(),
            lexical_modes: RollbackStack::new(),
            staged_header_facts: Vec::new(),
            operator_probes: Vec::new(),
        }
    }

    pub(crate) fn checkpoint(&self) -> ParseLocalCheckpoint {
        ParseLocalCheckpoint {
            line: self.line,
            indentation_baselines: self.indentation_baselines.checkpoint(),
            inline: self.inline,
            ml_arg: self.ml_arg,
            stop_sets: self.stop_sets.checkpoint(),
            delimiters: self.delimiters.checkpoint(),
            lexical_modes: self.lexical_modes.checkpoint(),
            staged_header_facts_len: self.staged_header_facts.len(),
            operator_probes_len: self.operator_probes.len(),
        }
    }

    pub(crate) fn rollback(&mut self, checkpoint: ParseLocalCheckpoint) {
        self.line = checkpoint.line;
        self.indentation_baselines
            .rollback(checkpoint.indentation_baselines);
        self.inline = checkpoint.inline;
        self.ml_arg = checkpoint.ml_arg;
        self.stop_sets.rollback(checkpoint.stop_sets);
        self.delimiters.rollback(checkpoint.delimiters);
        self.lexical_modes.rollback(checkpoint.lexical_modes);
        self.staged_header_facts
            .truncate(checkpoint.staged_header_facts_len);
        self.operator_probes
            .truncate(checkpoint.operator_probes_len);
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

    pub(crate) fn push_stop_set(&mut self, stop_set: StopSet) {
        self.stop_sets.push(stop_set);
    }

    pub(crate) fn replace_stop_set(&mut self, stop_set: StopSet) {
        self.stop_sets.replace_last(stop_set);
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
    stop_sets: StackCheckpoint,
    delimiters: StackCheckpoint,
    lexical_modes: StackCheckpoint,
    staged_header_facts_len: usize,
    operator_probes_len: usize,
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

    pub(crate) fn contains(self, stop: StopKind) -> bool {
        self.0 & (1 << (stop as u8)) != 0
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub(crate) enum StopKind {
    Newline,
    Comma,
    RightParenthesis,
    RightBracket,
    RightBrace,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Delimiter {
    Parenthesis,
    Bracket,
    Brace,
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
pub(crate) struct Probe<'parse, I, E> {
    input: &'parse mut I,
    local: &'parse mut ParseLocal,
    expectations: &'parse mut E,
}

impl<'parse, I, E> Probe<'parse, I, E> {
    pub(crate) fn new(
        input: &'parse mut I,
        local: &'parse mut ParseLocal,
        expectations: &'parse mut E,
    ) -> Self {
        Self {
            input,
            local,
            expectations,
        }
    }

    pub(crate) fn input(&mut self) -> &mut I {
        self.input
    }

    pub(crate) fn local(&mut self) -> &mut ParseLocal {
        self.local
    }

    pub(crate) fn expectations(&mut self) -> &mut E {
        self.expectations
    }

    pub(crate) fn commit<S: DirectCstSink>(
        self,
        sink: &'parse mut S,
    ) -> CommittedCst<'parse, I, E, S> {
        CommittedCst { probe: self, sink }
    }
}

/// Marker boundary for the direct Rowan sink supplied by the follow-up slice.
pub(crate) trait DirectCstSink {}

/// Access available only after a branch or recovery path has been committed.
pub(crate) struct CommittedCst<'parse, I, E, S: DirectCstSink> {
    probe: Probe<'parse, I, E>,
    sink: &'parse mut S,
}

impl<'parse, I, E, S: DirectCstSink> CommittedCst<'parse, I, E, S> {
    pub(crate) fn probe(&mut self) -> &mut Probe<'parse, I, E> {
        &mut self.probe
    }

    pub(crate) fn sink(&mut self) -> &mut S {
        self.sink
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
    fn committed_capability_adds_sink_access_only_after_transition() {
        #[derive(Default)]
        struct FakeSink {
            writes: usize,
        }
        impl DirectCstSink for FakeSink {}

        let mut input = SourceInput::new("x");
        let mut local = ParseLocal::new();
        let mut expectations = Vec::<&'static str>::new();
        let mut sink = FakeSink::default();
        let probe = Probe::new(&mut input, &mut local, &mut expectations);
        let mut committed = probe.commit(&mut sink);

        committed.sink().writes += 1;
        committed.probe().expectations().push("accepted");

        assert_eq!(committed.sink().writes, 1);
        assert_eq!(committed.probe().expectations(), &["accepted"]);
    }
}
