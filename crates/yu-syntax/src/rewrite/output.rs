//! Single committed Rowan and typed-recovery output owned by the direct rewrite.

use std::sync::Arc;

use reborrow_generic::Reborrow as _;
use rowan::{Checkpoint, GreenNode, GreenNodeBuilder, SyntaxKind as RowanSyntaxKind};

use crate::{
    session::{
        CommittedRecoveryRecord, DiagnosticId, ExpectationSources, ExpectedSyntax, GrammarRole,
        RecoveryKind, RecoverySiteKey, SyntaxExpectation, UnexpectedCategory, UnexpectedSyntax,
    },
    syntax_kind::SyntaxKind,
};

use super::{RewriteIn, item::Item};

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
    },
}

impl DiagnosticSequence<'_> {
    fn fresh() -> Self {
        Self::Fresh { next_id: Some(0) }
    }

    fn publish(&mut self, draft: RecoveryDraft) -> CommittedRecoveryRecord {
        // Sequential lookup is O(1); exact record comparison is O(E_record).
        if let Self::Reconcile { frozen, cursor, .. } = self
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
        }
    }

    fn reserve_structured(
        &mut self,
        start: usize,
        spec: StructuredRecoverySpec,
    ) -> (DiagnosticId, Option<&'frozen CommittedRecoveryRecord>) {
        if let Self::Reconcile { frozen, cursor, .. } = self
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

/// The sole mutable CST and committed-recovery output carried by `RewriteIn`.
///
/// Grammar owners receive only this forwarding surface. Construction and
/// finalization remain responsibilities of the enclosing rewrite harness.
pub(super) struct RewriteOutput<'frozen> {
    builder: GreenNodeBuilder<'static>,
    recoveries: Vec<RecoverySlot<'frozen>>,
    diagnostics: DiagnosticSequence<'frozen>,
    active_structured: Option<usize>,
    emitted_token_bytes: usize,
}

impl RewriteOutput<'_> {
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
    pub(super) fn checkpoint(&self) -> Checkpoint {
        self.builder.checkpoint()
    }

    #[inline]
    pub(super) fn start_node(&mut self, kind: RowanSyntaxKind) {
        self.builder.start_node(kind);
    }

    #[inline]
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

impl<'frozen> RewriteOutput<'frozen> {
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

impl<'frozen> RewriteOutput<'frozen> {
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
    mut i: RewriteIn,
    primary: Item,
    successor_origin: usize,
    spec: StructuredRecoverySpec,
    body: impl FnOnce(RewriteIn, Item) -> (R, usize),
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
