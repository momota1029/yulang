//! Single committed Rowan and typed-recovery output owned by the direct parser.

use std::sync::Arc;

use reborrow_generic::Reborrow as _;
#[cfg(test)]
use rowan::Checkpoint;
use rowan::{GreenNode, GreenNodeBuilder, SyntaxKind as RowanSyntaxKind};

use crate::{
    session::{
        CommittedRecoveryRecord, DiagnosticId, ExpectationSources, ExpectedSyntax, GrammarRole,
        RecoveryKind, RecoverySiteKey, SyntaxExpectation, UnexpectedCategory, UnexpectedSyntax,
    },
    syntax_kind::SyntaxKind,
};

use crate::parser::{ParserIn, input::item::Item};

pub(super) mod emit;

/// Complete recovery evidence before its diagnostic identity is assigned.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct RecoveryDraft {
    site: RecoverySiteKey,
    kind: RecoveryKind,
    unexpected: Arc<[UnexpectedSyntax]>,
    expectations: Arc<[SyntaxExpectation]>,
    primary_expectation: usize,
}

impl RecoveryDraft {
    pub(super) fn new(
        site: RecoverySiteKey,
        kind: RecoveryKind,
        unexpected: Arc<[UnexpectedSyntax]>,
        expectations: Arc<[SyntaxExpectation]>,
        primary_expectation: usize,
    ) -> Self {
        validate_recovery(&site, kind, &unexpected, &expectations, primary_expectation);
        Self {
            site,
            kind,
            unexpected,
            expectations,
            primary_expectation,
        }
    }

    fn into_record(self, id: DiagnosticId) -> CommittedRecoveryRecord {
        CommittedRecoveryRecord {
            id,
            site: self.site,
            kind: self.kind,
            unexpected: self.unexpected,
            expectations: self.expectations,
            primary_expectation: self.primary_expectation,
        }
    }

    pub(super) fn assert_emission(
        &self,
        kind: RecoveryKind,
        range: &std::ops::Range<usize>,
        unexpected: &[UnexpectedSyntax],
    ) {
        assert_eq!(self.kind, kind);
        assert_eq!(&self.site.range, range);
        assert_eq!(&*self.unexpected, unexpected);
    }
}

/// Fields known before a structured Error enters its total nested body.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct StructuredRecoverySpec {
    role: GrammarRole,
    unexpected: UnexpectedCategory,
    expected: ExpectedSyntax,
    sources: ExpectationSources,
    primary_expectation: usize,
}

impl StructuredRecoverySpec {
    pub(super) fn new(
        role: GrammarRole,
        unexpected: UnexpectedCategory,
        expected: ExpectedSyntax,
        sources: ExpectationSources,
        primary_expectation: usize,
    ) -> Self {
        assert_eq!(
            primary_expectation, 0,
            "the structured singleton expectation is primary"
        );
        Self {
            role,
            unexpected,
            expected,
            sources,
            primary_expectation,
        }
    }

    fn draft(self, start: usize, end: usize) -> RecoveryDraft {
        assert!(start < end, "a structured Error range is nonempty");
        let range = start..end;
        RecoveryDraft::new(
            RecoverySiteKey {
                role: self.role,
                range: range.clone(),
            },
            RecoveryKind::Error,
            Arc::from([UnexpectedSyntax::Token {
                range: range.clone(),
                category: self.unexpected,
            }]),
            Arc::from([SyntaxExpectation {
                role: self.role,
                expected: self.expected,
                range,
                sources: self.sources,
            }]),
            self.primary_expectation,
        )
    }

    fn assert_frozen_prefix(self, start: usize, frozen: &CommittedRecoveryRecord) {
        assert_eq!(frozen.site.role, self.role, "frozen recovery role mismatch");
        assert_eq!(
            frozen.kind,
            RecoveryKind::Error,
            "frozen recovery kind mismatch"
        );
        assert_eq!(
            frozen.site.range.start, start,
            "frozen recovery start mismatch"
        );
        let [UnexpectedSyntax::Token { range, category }] = &*frozen.unexpected else {
            panic!("a structured frozen Error requires one Token unexpected fact")
        };
        assert_eq!(range.start, start, "frozen unexpected start mismatch");
        assert_eq!(
            *category, self.unexpected,
            "frozen unexpected category mismatch"
        );
        let [expectation] = &*frozen.expectations else {
            panic!("a structured frozen Error requires one expectation")
        };
        assert_eq!(
            expectation.role, self.role,
            "frozen expectation role mismatch"
        );
        assert_eq!(
            expectation.range.start, start,
            "frozen expectation start mismatch"
        );
        assert_eq!(
            expectation.expected, self.expected,
            "frozen expected syntax mismatch"
        );
        assert_eq!(
            expectation.sources, self.sources,
            "frozen expectation sources mismatch"
        );
        assert_eq!(
            frozen.primary_expectation, self.primary_expectation,
            "frozen primary expectation mismatch"
        );
    }
}

enum RecoverySlot<'frozen> {
    Reserved(StructuredReservation<'frozen>),
    Complete(CommittedRecoveryRecord),
}

struct StructuredReservation<'frozen> {
    id: DiagnosticId,
    frozen: Option<&'frozen CommittedRecoveryRecord>,
    spec: StructuredRecoverySpec,
    start: usize,
    emitted_token_bytes: usize,
    previous_active: Option<usize>,
}

/// Private affine identity retained inside the structured output helper.
struct StructuredReservationToken {
    slot: usize,
}

enum DiagnosticSequence<'frozen> {
    Fresh {
        next_id: Option<u32>,
    },
    Reconcile {
        frozen: &'frozen [CommittedRecoveryRecord],
        cursor: usize,
        next_id: Option<u32>,
        consume_frozen: bool,
    },
}

impl DiagnosticSequence<'_> {
    fn fresh() -> Self {
        Self::Fresh { next_id: Some(0) }
    }

    fn publish(&mut self, draft: RecoveryDraft) -> CommittedRecoveryRecord {
        // Sequential lookup is O(1); exact record comparison is O(E_record).
        if let Self::Reconcile {
            frozen,
            cursor,
            consume_frozen: true,
            ..
        } = self
            && let Some(expected) = frozen.get(*cursor)
        {
            assert_draft_matches_record(&draft, expected);
            let id = expected.id;
            *cursor += 1;
            return draft.into_record(id);
        }

        draft.into_record(self.allocate_fresh())
    }

    fn allocate_fresh(&mut self) -> DiagnosticId {
        let next_id = match self {
            Self::Fresh { next_id } | Self::Reconcile { next_id, .. } => next_id,
        };
        let raw = next_id.expect("diagnostic ID overflow");
        *next_id = raw.checked_add(1);
        DiagnosticId(raw)
    }

    fn finish(&self) {
        if let Self::Reconcile { frozen, cursor, .. } = self {
            assert_eq!(
                *cursor,
                frozen.len(),
                "all frozen recovery records must be reconciled"
            );
        }
    }

    #[cfg(test)]
    fn position(&self) -> (Option<u32>, usize) {
        match self {
            Self::Fresh { next_id } => (*next_id, 0),
            Self::Reconcile {
                cursor, next_id, ..
            } => (*next_id, *cursor),
        }
    }
}

impl<'frozen> DiagnosticSequence<'frozen> {
    fn reconcile(frozen: &'frozen [CommittedRecoveryRecord]) -> Self {
        // One O(F + E_frozen) validation/max scan; publication never rescans.
        let mut maximum = None;
        for record in frozen {
            validate_recovery(
                &record.site,
                record.kind,
                &record.unexpected,
                &record.expectations,
                record.primary_expectation,
            );
            maximum = Some(maximum.map_or(record.id.0, |current: u32| current.max(record.id.0)));
        }
        Self::Reconcile {
            frozen,
            cursor: 0,
            next_id: maximum.map_or(Some(0), |id| id.checked_add(1)),
            consume_frozen: true,
        }
    }

    fn reserve_structured(
        &mut self,
        start: usize,
        spec: StructuredRecoverySpec,
    ) -> (DiagnosticId, Option<&'frozen CommittedRecoveryRecord>) {
        if let Self::Reconcile {
            frozen,
            cursor,
            consume_frozen: true,
            ..
        } = self
            && let Some(expected) = frozen.get(*cursor)
        {
            spec.assert_frozen_prefix(start, expected);
            let id = expected.id;
            *cursor += 1;
            return (id, Some(expected));
        }
        (self.allocate_fresh(), None)
    }
}

/// The sole mutable CST and committed-recovery output carried by `ParserIn`.
///
/// Grammar owners receive only this forwarding surface. Construction and
/// finalization remain responsibilities of the enclosing parser harness.
pub(super) struct ParserOutput<'frozen> {
    builder: GreenNodeBuilder<'static>,
    recoveries: Vec<RecoverySlot<'frozen>>,
    diagnostics: DiagnosticSequence<'frozen>,
    active_structured: Option<usize>,
    emitted_token_bytes: usize,
}

impl ParserOutput<'_> {
    pub(super) fn new() -> Self {
        Self {
            builder: GreenNodeBuilder::new(),
            recoveries: Vec::new(),
            diagnostics: DiagnosticSequence::fresh(),
            active_structured: None,
            emitted_token_bytes: 0,
        }
    }

    #[inline]
    #[cfg(test)]
    pub(super) fn checkpoint(&self) -> Checkpoint {
        self.builder.checkpoint()
    }

    #[inline]
    pub(super) fn start_node(&mut self, kind: RowanSyntaxKind) {
        self.builder.start_node(kind);
    }

    #[inline]
    #[cfg(test)]
    pub(super) fn start_node_at(&mut self, checkpoint: Checkpoint, kind: RowanSyntaxKind) {
        self.builder.start_node_at(checkpoint, kind);
    }

    #[inline]
    pub(super) fn token(&mut self, kind: RowanSyntaxKind, text: &str) {
        self.emitted_token_bytes = self
            .emitted_token_bytes
            .checked_add(text.len())
            .expect("emitted token byte count overflow");
        self.builder.token(kind, text);
    }

    #[inline]
    pub(super) fn finish_node(&mut self) {
        self.builder.finish_node();
    }

    pub(super) fn commit_recovery(&mut self, draft: RecoveryDraft) {
        let record = self.diagnostics.publish(draft);
        self.recoveries.push(RecoverySlot::Complete(record));
    }

    #[cfg(test)]
    pub(super) fn finish(self) -> GreenNode {
        let (green, recoveries) = self.finish_with_recoveries();
        assert!(
            recoveries.is_empty(),
            "typed recovery output must be retained by its harness"
        );
        green
    }

    pub(super) fn finish_with_recoveries(self) -> (GreenNode, Vec<CommittedRecoveryRecord>) {
        self.diagnostics.finish();
        assert!(
            self.active_structured.is_none(),
            "all structured recovery reservations must be completed"
        );
        let mut records = if self.recoveries.is_empty() {
            Vec::new()
        } else {
            Vec::with_capacity(self.recoveries.len())
        };
        for slot in self.recoveries {
            let RecoverySlot::Complete(record) = slot else {
                panic!("a reserved recovery slot reached final output")
            };
            records.push(record);
        }
        (self.builder.finish(), records)
    }

    #[cfg(test)]
    pub(super) fn recovery_slot_count(&self) -> usize {
        self.recoveries.len()
    }

    #[cfg(test)]
    pub(super) fn recovery_capacity(&self) -> usize {
        self.recoveries.capacity()
    }

    #[cfg(test)]
    pub(super) fn diagnostic_position(&self) -> (Option<u32>, usize) {
        self.diagnostics.position()
    }
}

impl<'frozen> ParserOutput<'frozen> {
    /// Full-root records are fresh unless publication enters the shared header scope.
    pub(super) fn reconcile_scoped(frozen: &'frozen [CommittedRecoveryRecord]) -> Self {
        let mut output = Self::reconcile(frozen);
        if let DiagnosticSequence::Reconcile { consume_frozen, .. } = &mut output.diagnostics {
            *consume_frozen = false;
        }
        output
    }

    pub(super) fn header_reconciliation_scope(&mut self) -> HeaderReconciliationScope<'_, 'frozen> {
        let previous = match &mut self.diagnostics {
            DiagnosticSequence::Fresh { .. } => None,
            DiagnosticSequence::Reconcile { consume_frozen, .. } => {
                Some(std::mem::replace(consume_frozen, true))
            }
        };
        HeaderReconciliationScope {
            output: self,
            previous,
        }
    }

    pub(super) fn reconcile(frozen: &'frozen [CommittedRecoveryRecord]) -> Self {
        Self {
            builder: GreenNodeBuilder::new(),
            recoveries: Vec::new(),
            diagnostics: DiagnosticSequence::reconcile(frozen),
            active_structured: None,
            emitted_token_bytes: 0,
        }
    }
}

/// Restores publication mode on normal return, early return and unwinding.
pub(super) struct HeaderReconciliationScope<'output, 'frozen> {
    output: &'output mut ParserOutput<'frozen>,
    previous: Option<bool>,
}

impl<'frozen> std::ops::Deref for HeaderReconciliationScope<'_, 'frozen> {
    type Target = ParserOutput<'frozen>;

    fn deref(&self) -> &Self::Target {
        self.output
    }
}

impl std::ops::DerefMut for HeaderReconciliationScope<'_, '_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.output
    }
}

impl Drop for HeaderReconciliationScope<'_, '_> {
    fn drop(&mut self) {
        if let Some(previous) = self.previous
            && let DiagnosticSequence::Reconcile { consume_frozen, .. } =
                &mut self.output.diagnostics
        {
            *consume_frozen = previous;
        }
    }
}

impl<'frozen> ParserOutput<'frozen> {
    fn begin_structured_recovery(
        &mut self,
        start: usize,
        spec: StructuredRecoverySpec,
    ) -> StructuredReservationToken {
        let (id, frozen) = self.diagnostics.reserve_structured(start, spec);
        let slot = self.recoveries.len();
        self.recoveries
            .push(RecoverySlot::Reserved(StructuredReservation {
                id,
                frozen,
                spec,
                start,
                emitted_token_bytes: self.emitted_token_bytes,
                previous_active: self.active_structured,
            }));
        self.active_structured = Some(slot);
        StructuredReservationToken { slot }
    }

    fn complete_structured_recovery(&mut self, token: StructuredReservationToken, end: usize) {
        assert_eq!(
            self.active_structured,
            Some(token.slot),
            "structured recovery reservations complete in LIFO order"
        );
        let RecoverySlot::Reserved(reservation) = &self.recoveries[token.slot] else {
            panic!("a structured recovery reservation completes exactly once")
        };
        let range_bytes = end
            .checked_sub(reservation.start)
            .filter(|bytes| *bytes > 0)
            .expect("a structured Error range is nonempty");
        let emitted_bytes = self
            .emitted_token_bytes
            .checked_sub(reservation.emitted_token_bytes)
            .expect("structured Error token byte count moved backwards");
        assert_eq!(
            emitted_bytes, range_bytes,
            "structured Error range must equal its emitted token bytes"
        );
        let draft = reservation.spec.draft(reservation.start, end);
        if let Some(frozen) = reservation.frozen {
            assert_draft_matches_record(&draft, frozen);
        }
        let record = draft.into_record(reservation.id);
        let previous_active = reservation.previous_active;
        self.recoveries[token.slot] = RecoverySlot::Complete(record);
        self.active_structured = previous_active;
    }

    #[cfg(test)]
    pub(super) fn leave_structured_unfinished_for_test(
        &mut self,
        primary: Item,
        successor_origin: usize,
        spec: StructuredRecoverySpec,
    ) {
        let start = structured_start_from_item(&primary, successor_origin);
        let _ = self.begin_structured_recovery(start, spec);
    }

    #[cfg(test)]
    pub(super) fn violate_structured_lifo_for_test(
        &mut self,
        outer_primary: Item,
        outer_successor_origin: usize,
        outer_spec: StructuredRecoverySpec,
        inner_primary: Item,
        inner_successor_origin: usize,
        inner_spec: StructuredRecoverySpec,
        outer_end: usize,
    ) {
        let outer_start = structured_start_from_item(&outer_primary, outer_successor_origin);
        let inner_start = structured_start_from_item(&inner_primary, inner_successor_origin);
        let outer = self.begin_structured_recovery(outer_start, outer_spec);
        let _inner = self.begin_structured_recovery(inner_start, inner_spec);
        self.complete_structured_recovery(outer, outer_end);
    }
}

/// Reserves one ordered structured Error before running its total nested body.
///
/// The affine reservation token never leaves this output-owning helper. A
/// panic invalidates the output; a normal return pairs exactly one Error node
/// with the completed record in its original reserved slot.
pub(super) fn emit_structured_recovery_error_from_item<R>(
    mut i: ParserIn,
    primary: Item,
    successor_origin: usize,
    spec: StructuredRecoverySpec,
    body: impl FnOnce(ParserIn, Item) -> (R, usize),
) -> R {
    let start = structured_start_from_item(&primary, successor_origin);
    let reservation = i.state.begin_structured_recovery(start, spec);
    i.state.start_node(SyntaxKind::Error.into());
    let (result, end) = body(i.rb(), primary);
    i.state.finish_node();
    i.state.complete_structured_recovery(reservation, end);
    result
}

fn structured_start_from_item(primary: &Item, successor_origin: usize) -> usize {
    assert_eq!(
        primary.leading_view().remaining_physical_parts(),
        0,
        "structured recovery requires its direct leading to be pre-emitted"
    );
    let range = primary.extent(successor_origin).recovery_range();
    assert!(
        range.start < range.end,
        "a structured primary Item is nonempty"
    );
    range.start
}

fn validate_recovery(
    site: &RecoverySiteKey,
    kind: RecoveryKind,
    unexpected: &[UnexpectedSyntax],
    expectations: &[SyntaxExpectation],
    primary_expectation: usize,
) {
    assert!(
        !expectations.is_empty(),
        "a committed recovery requires an expectation union"
    );
    assert!(
        primary_expectation < expectations.len(),
        "the primary expectation must index the expectation union"
    );
    match kind {
        RecoveryKind::Missing => {
            assert_eq!(site.range.start, site.range.end, "Missing is zero-width")
        }
        RecoveryKind::Error => {
            assert!(site.range.start < site.range.end, "Error is nonempty");
            assert!(
                unexpected.iter().any(|unexpected| {
                    !matches!(unexpected, UnexpectedSyntax::EndOfInput { .. })
                }),
                "Error requires non-EOF unexpected evidence"
            );
        }
    }
}

fn assert_draft_matches_record(draft: &RecoveryDraft, record: &CommittedRecoveryRecord) {
    assert_eq!(draft.site, record.site, "frozen recovery site mismatch");
    assert_eq!(draft.kind, record.kind, "frozen recovery kind mismatch");
    assert_eq!(
        draft.unexpected, record.unexpected,
        "frozen unexpected evidence mismatch"
    );
    assert_eq!(
        draft.expectations, record.expectations,
        "frozen expectation union mismatch"
    );
    assert_eq!(
        draft.primary_expectation, record.primary_expectation,
        "frozen primary expectation mismatch"
    );
}

#[cfg(test)]
mod scoped_tests {
    use super::*;
    use crate::session::ExpressionRole;

    fn missing(at: usize) -> RecoveryDraft {
        let role = GrammarRole::Expression(ExpressionRole::Nud);
        RecoveryDraft::new(
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
    }

    #[test]
    fn scoped_reconciliation_preserves_interleaved_encounter_order() {
        let frozen = [
            missing(2).into_record(DiagnosticId(4)),
            missing(6).into_record(DiagnosticId(8)),
        ];
        let mut output = ParserOutput::reconcile_scoped(&frozen);
        output.start_node(SyntaxKind::Root.into());
        output.commit_recovery(missing(0));
        output
            .header_reconciliation_scope()
            .commit_recovery(missing(2));
        output.commit_recovery(missing(4));
        output
            .header_reconciliation_scope()
            .commit_recovery(missing(6));
        output.commit_recovery(missing(8));
        output.finish_node();
        let (_, records) = output.finish_with_recoveries();
        assert_eq!(
            records.iter().map(|r| r.id.0).collect::<Vec<_>>(),
            [9, 4, 10, 8, 11]
        );
        assert_eq!(records[1], frozen[0]);
        assert_eq!(records[3], frozen[1]);
    }

    #[test]
    fn scoped_reconciliation_restores_mode_on_unwind_and_nested_exit() {
        let frozen = [
            missing(2).into_record(DiagnosticId(4)),
            missing(4).into_record(DiagnosticId(6)),
        ];
        let mut output = ParserOutput::reconcile_scoped(&frozen);
        output.start_node(SyntaxKind::Root.into());
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let mut scope = output.header_reconciliation_scope();
                {
                    let _nested = scope.header_reconciliation_scope();
                }
                scope.commit_recovery(missing(2));
                panic!("leave scope");
            }))
            .is_err()
        );
        output.commit_recovery(missing(3));
        output
            .header_reconciliation_scope()
            .commit_recovery(missing(4));
        output.finish_node();
        let (_, records) = output.finish_with_recoveries();
        assert_eq!(
            records.iter().map(|r| r.id.0).collect::<Vec<_>>(),
            [4, 7, 6]
        );
    }

    #[test]
    fn scoped_reconciliation_applies_to_structured_reservations() {
        let spec = StructuredRecoverySpec::new(
            GrammarRole::Expression(ExpressionRole::Nud),
            UnexpectedCategory::OtherCharacter,
            ExpectedSyntax::Expression,
            ExpectationSources::COMMITTED_RECOVERY_RULE,
            0,
        );
        let frozen = [spec.draft(1, 2).into_record(DiagnosticId(5))];
        let mut output = ParserOutput::reconcile_scoped(&frozen);
        output.start_node(SyntaxKind::Root.into());
        let first = output.begin_structured_recovery(0, spec);
        output.token(SyntaxKind::Error.into(), "@");
        output.complete_structured_recovery(first, 1);
        {
            let mut scope = output.header_reconciliation_scope();
            let shared = scope.begin_structured_recovery(1, spec);
            scope.token(SyntaxKind::Error.into(), "@");
            scope.complete_structured_recovery(shared, 2);
        }
        output.finish_node();
        let (_, records) = output.finish_with_recoveries();
        assert_eq!(records[0].id, DiagnosticId(6));
        assert_eq!(records[1], frozen[0]);
    }
}
