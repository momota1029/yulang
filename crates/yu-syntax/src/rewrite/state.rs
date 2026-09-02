use std::{ops::Range, sync::Arc};

use chasa_recover::Recoverable;

use crate::{
    grammar::expression::{OperatorChain, OperatorChainItem},
    session::{
        CanonicalRecoveryContinuation, CommittedRecoveryRecord, DiagnosticId, RecoveryKind,
        RecoverySiteKey, SyntaxExpectation, UnexpectedSyntax,
    },
    sink::RowanSink,
    syntax_kind::SyntaxKind,
};

use super::item::{Delimiter, ItemIdentity, Level, StopKind, TokenKind};

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(super) struct PilotLineState {
    pub(super) last_newline: Option<(usize, usize)>,
    pub(super) line_start: usize,
    pub(super) line_indent: usize,
    pub(super) line_number: usize,
    pub(super) column: usize,
    pub(super) at_line_start: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ProvisionalRecovery {
    pub(super) site: RecoverySiteKey,
    pub(super) kind: RecoveryKind,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PersistentRecovery {
    pub(super) site: RecoverySiteKey,
    pub(super) kind: RecoveryKind,
}

#[derive(Default)]
pub(super) struct PilotRecoverState {
    pub(super) line: PilotLineState,
    pub(super) next_item_ordinal: u64,
    scanned_items: Vec<ItemIdentity>,
    expectations: Vec<SyntaxExpectation>,
    next_diagnostic_id: u32,
    provisional_recoveries: Vec<ProvisionalRecovery>,
    persistent_recoveries: Vec<PersistentRecovery>,
    pub(super) is_cut: bool,
}

#[derive(Clone, Copy)]
pub(super) struct PilotRecoverMark {
    line: PilotLineState,
    next_item_ordinal: u64,
    scanned_items_len: usize,
    expectations_len: usize,
    next_diagnostic_id: u32,
    provisional_recoveries_len: usize,
    persistent_recoveries_len: usize,
    is_cut: bool,
}

impl PilotRecoverState {
    pub(super) fn allocate_item_identity(&mut self, byte_offset: usize) -> ItemIdentity {
        let identity = ItemIdentity {
            ordinal: self.next_item_ordinal,
            byte_offset,
        };
        self.next_item_ordinal = self
            .next_item_ordinal
            .checked_add(1)
            .expect("pilot item identity space exhausted");
        identity
    }

    pub(super) fn record_expectation(&mut self, expectation: SyntaxExpectation) {
        self.expectations.push(expectation);
    }

    pub(super) fn record_scanned_item(&mut self, identity: ItemIdentity) {
        self.scanned_items.push(identity);
    }

    pub(super) fn scanned_items(&self) -> &[ItemIdentity] {
        &self.scanned_items
    }

    pub(super) fn expectations(&self) -> &[SyntaxExpectation] {
        &self.expectations
    }

    pub(super) fn allocate_diagnostic_id(&mut self) -> DiagnosticId {
        let id = DiagnosticId(self.next_diagnostic_id);
        self.next_diagnostic_id = self
            .next_diagnostic_id
            .checked_add(1)
            .expect("diagnostic identity space exhausted");
        id
    }

    pub(super) fn next_diagnostic_id(&self) -> u32 {
        self.next_diagnostic_id
    }

    pub(super) fn record_provisional_recovery(&mut self, recovery: ProvisionalRecovery) {
        self.provisional_recoveries.push(recovery);
    }

    pub(super) fn provisional_recoveries(&self) -> &[ProvisionalRecovery] {
        &self.provisional_recoveries
    }

    pub(super) fn record_persistent_recovery(&mut self, recovery: PersistentRecovery) {
        self.persistent_recoveries.push(recovery);
    }

    pub(super) fn persistent_recoveries(&self) -> &[PersistentRecovery] {
        &self.persistent_recoveries
    }
}

impl Recoverable for PilotRecoverState {
    type Mark = PilotRecoverMark;

    fn mark(&self) -> Self::Mark {
        PilotRecoverMark {
            line: self.line,
            next_item_ordinal: self.next_item_ordinal,
            scanned_items_len: self.scanned_items.len(),
            expectations_len: self.expectations.len(),
            next_diagnostic_id: self.next_diagnostic_id,
            provisional_recoveries_len: self.provisional_recoveries.len(),
            persistent_recoveries_len: self.persistent_recoveries.len(),
            is_cut: self.is_cut,
        }
    }

    fn rollback(&mut self, mark: Self::Mark) {
        self.line = mark.line;
        self.next_item_ordinal = mark.next_item_ordinal;
        self.scanned_items.truncate(mark.scanned_items_len);
        self.expectations.truncate(mark.expectations_len);
        self.next_diagnostic_id = mark.next_diagnostic_id;
        self.provisional_recoveries
            .truncate(mark.provisional_recoveries_len);
        self.persistent_recoveries
            .truncate(mark.persistent_recoveries_len);
        self.is_cut = mark.is_cut;
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct PilotFrame {
    pub(super) layout_baseline: usize,
    pub(super) allow_same_level_newline: bool,
    pub(super) delimiter: Option<Delimiter>,
    pub(super) stop: Option<StopKind>,
}

impl Default for PilotFrame {
    fn default() -> Self {
        Self {
            layout_baseline: 0,
            allow_same_level_newline: false,
            delimiter: None,
            stop: None,
        }
    }
}

pub(super) struct RecoveryDraft {
    pub(super) site: RecoverySiteKey,
    pub(super) kind: RecoveryKind,
    pub(super) unexpected: Arc<[UnexpectedSyntax]>,
    pub(super) expectations: Arc<[SyntaxExpectation]>,
    pub(super) primary_expectation: usize,
    pub(super) continuation: CanonicalRecoveryContinuation,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PublishedRecovery {
    pub(super) record: CommittedRecoveryRecord,
    pub(super) continuation: CanonicalRecoveryContinuation,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum RecoveryChainItem {
    None,
    MissingOperand,
    Error,
}

struct ChainBuild<'source> {
    start: usize,
    end: usize,
    items: Vec<OperatorChainItem<'source>>,
}

/// Direct committed capability. Rowan tokens and existing `OperatorChain`
/// items are appended by the accepting owner; there is no action replay.
pub(super) struct PilotOutput<'source> {
    sink: RowanSink<'source>,
    recoveries: Vec<PublishedRecovery>,
    chains: Vec<ChainBuild<'source>>,
    root_chain: Option<OperatorChain<'source>>,
}

impl<'source> PilotOutput<'source> {
    pub(super) fn new(source: &'source str) -> Self {
        Self {
            sink: RowanSink::new(source),
            recoveries: Vec::new(),
            chains: Vec::new(),
            root_chain: None,
        }
    }

    pub(super) fn start_node(&mut self, kind: SyntaxKind) {
        self.sink.start_node(kind);
    }

    pub(super) fn token_range(&mut self, kind: SyntaxKind, range: Range<usize>) {
        self.sink.token_range(kind, range);
    }

    pub(super) fn finish_node(&mut self) {
        self.sink.finish_node();
    }

    pub(super) fn begin_chain(&mut self, start: usize) {
        self.chains.push(ChainBuild {
            start,
            end: start,
            items: Vec::new(),
        });
    }

    pub(super) fn push_chain_item(
        &mut self,
        item: OperatorChainItem<'source>,
        range: Range<usize>,
    ) {
        let chain = self.chains.last_mut().expect("an expression chain is open");
        chain.end = chain.end.max(range.end);
        chain.items.push(item);
    }

    pub(super) fn finish_chain(&mut self) -> OperatorChain<'source> {
        let chain = self.chains.pop().expect("an expression chain is open");
        OperatorChain::new(chain.items, chain.start..chain.end)
    }

    pub(super) fn set_root_chain(&mut self, chain: OperatorChain<'source>) {
        assert!(self.root_chain.replace(chain).is_none());
    }

    pub(super) fn root_chain(&self) -> Option<&OperatorChain<'source>> {
        self.root_chain.as_ref()
    }

    /// Publishes the generic CST node and its committed recovery record in one
    /// owner operation, and appends the matching existing AST recovery item.
    pub(super) fn publish_recovery(
        &mut self,
        id: DiagnosticId,
        draft: RecoveryDraft,
        range: Range<usize>,
        chain_item: RecoveryChainItem,
    ) {
        assert!(!draft.expectations.is_empty());
        assert!(draft.primary_expectation < draft.expectations.len());
        match draft.kind {
            RecoveryKind::Missing => assert_eq!(draft.site.range.start, draft.site.range.end),
            RecoveryKind::Error => assert!(draft.site.range.start < draft.site.range.end),
        }
        self.start_node(match draft.kind {
            RecoveryKind::Missing => SyntaxKind::Missing,
            RecoveryKind::Error => SyntaxKind::Error,
        });
        if draft.kind == RecoveryKind::Error {
            self.token_range(SyntaxKind::Unknown, range.clone());
        }
        self.finish_node();
        match chain_item {
            RecoveryChainItem::None => {}
            RecoveryChainItem::MissingOperand => self.push_chain_item(
                OperatorChainItem::MissingOperand {
                    range: range.clone(),
                },
                range,
            ),
            RecoveryChainItem::Error => self.push_chain_item(
                OperatorChainItem::Error {
                    range: range.clone(),
                },
                range,
            ),
        }
        self.recoveries.push(PublishedRecovery {
            record: CommittedRecoveryRecord {
                id,
                site: draft.site,
                kind: draft.kind,
                unexpected: draft.unexpected,
                expectations: draft.expectations,
                primary_expectation: draft.primary_expectation,
            },
            continuation: draft.continuation,
        });
    }

    pub(super) fn recoveries(&self) -> &[PublishedRecovery] {
        &self.recoveries
    }

    pub(super) fn finish_complete(self) -> rowan::GreenNode {
        assert!(self.chains.is_empty());
        self.sink.finish_complete()
    }

    pub(super) fn finish_prefix(self) -> rowan::GreenNode {
        assert!(self.chains.is_empty());
        self.sink.finish()
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) enum LegacyParseLocalField {
    Line,
    IndentationBaselines,
    Inline,
    MlArg,
    TypeMlArg,
    TypeExpressionEpisodeDepth,
    TypeExpressionEpisodePolicies,
    TypeExpressionScopedStopFrames,
    StopSets,
    Delimiters,
    ExpressionDelimitedOwners,
    TypeDelimitedOwners,
    LexicalModes,
    AmbientOwnerScopes,
    IfExpressionCompanions,
    YumarkFrames,
    StagedHeaderFacts,
    OperatorProbes,
    ReusableRecoveries,
    ReusedRecoveryIndices,
    NextDiagnosticId,
    NextIfExpressionCompanionId,
    TypeMalformedCallerBoundary,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum FieldDestination {
    ExplicitFrame,
    RecoverableState,
    NoPilotReader,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum PilotReader {
    TriviaScanner,
    LayoutFrame,
    ExpressionMode,
    StopOwner,
    DelimiterOwner,
    RecoveryPublisher,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct FieldConeEntry {
    pub(super) field: LegacyParseLocalField,
    pub(super) destination: FieldDestination,
    pub(super) reader: Option<PilotReader>,
    pub(super) retained_gate: Option<u8>,
}

/// Exhaustive field cone for the selected Gate-2 readers. A `NoPilotReader`
/// entry is a local witness only; it does not eliminate the field globally.
pub(super) const PILOT_FIELD_CONE: &[FieldConeEntry] = &[
    entry(
        LegacyParseLocalField::Line,
        FieldDestination::RecoverableState,
        Some(PilotReader::TriviaScanner),
        None,
    ),
    entry(
        LegacyParseLocalField::IndentationBaselines,
        FieldDestination::ExplicitFrame,
        Some(PilotReader::LayoutFrame),
        None,
    ),
    entry(
        LegacyParseLocalField::Inline,
        FieldDestination::ExplicitFrame,
        Some(PilotReader::LayoutFrame),
        None,
    ),
    entry(
        LegacyParseLocalField::MlArg,
        FieldDestination::ExplicitFrame,
        Some(PilotReader::ExpressionMode),
        None,
    ),
    no_reader(LegacyParseLocalField::TypeMlArg, 5),
    no_reader(LegacyParseLocalField::TypeExpressionEpisodeDepth, 5),
    no_reader(LegacyParseLocalField::TypeExpressionEpisodePolicies, 5),
    no_reader(LegacyParseLocalField::TypeExpressionScopedStopFrames, 5),
    entry(
        LegacyParseLocalField::StopSets,
        FieldDestination::ExplicitFrame,
        Some(PilotReader::StopOwner),
        None,
    ),
    entry(
        LegacyParseLocalField::Delimiters,
        FieldDestination::ExplicitFrame,
        Some(PilotReader::DelimiterOwner),
        None,
    ),
    no_reader(LegacyParseLocalField::ExpressionDelimitedOwners, 4),
    no_reader(LegacyParseLocalField::TypeDelimitedOwners, 5),
    no_reader(LegacyParseLocalField::LexicalModes, 8),
    no_reader(LegacyParseLocalField::AmbientOwnerScopes, 6),
    no_reader(LegacyParseLocalField::IfExpressionCompanions, 4),
    no_reader(LegacyParseLocalField::YumarkFrames, 8),
    no_reader(LegacyParseLocalField::StagedHeaderFacts, 9),
    no_reader(LegacyParseLocalField::OperatorProbes, 4),
    no_reader(LegacyParseLocalField::ReusableRecoveries, 7),
    no_reader(LegacyParseLocalField::ReusedRecoveryIndices, 7),
    entry(
        LegacyParseLocalField::NextDiagnosticId,
        FieldDestination::RecoverableState,
        Some(PilotReader::RecoveryPublisher),
        None,
    ),
    no_reader(LegacyParseLocalField::NextIfExpressionCompanionId, 4),
    no_reader(LegacyParseLocalField::TypeMalformedCallerBoundary, 5),
];

const fn entry(
    field: LegacyParseLocalField,
    destination: FieldDestination,
    reader: Option<PilotReader>,
    retained_gate: Option<u8>,
) -> FieldConeEntry {
    FieldConeEntry {
        field,
        destination,
        reader,
        retained_gate,
    }
}

const fn no_reader(field: LegacyParseLocalField, retained_gate: u8) -> FieldConeEntry {
    entry(
        field,
        FieldDestination::NoPilotReader,
        None,
        Some(retained_gate),
    )
}

pub(super) fn syntax_kind_for_token(kind: TokenKind) -> SyntaxKind {
    match kind {
        TokenKind::Identifier => SyntaxKind::Identifier,
        TokenKind::Integer => SyntaxKind::Integer,
        TokenKind::PrefixOperator | TokenKind::InfixOperator(_) | TokenKind::Unknown => {
            SyntaxKind::Operator
        }
        TokenKind::LeftParenthesis => SyntaxKind::LParen,
        TokenKind::RightParenthesis => SyntaxKind::RParen,
        TokenKind::Dot => SyntaxKind::Dot,
        TokenKind::ColonColon => SyntaxKind::ColonColon,
    }
}

pub(super) fn level_is_readable(level: Level, operator_level: Level) -> bool {
    operator_level >= level
}
