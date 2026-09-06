//! Single committed Rowan and typed-recovery output owned by the direct rewrite.

use std::sync::Arc;

use rowan::{Checkpoint, GreenNode, GreenNodeBuilder, SyntaxKind as RowanSyntaxKind};

use crate::session::{
    CommittedRecoveryRecord, DiagnosticId, RecoveryKind, RecoverySiteKey, SyntaxExpectation,
    UnexpectedSyntax,
};

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

        let next_id = match self {
            Self::Fresh { next_id } | Self::Reconcile { next_id, .. } => next_id,
        };
        let raw = next_id.expect("diagnostic ID overflow");
        *next_id = raw.checked_add(1);
        draft.into_record(DiagnosticId(raw))
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
}

/// The sole mutable CST and committed-recovery output carried by `RewriteIn`.
///
/// Grammar owners receive only this forwarding surface. Construction and
/// finalization remain responsibilities of the enclosing rewrite harness.
pub(super) struct RewriteOutput<'frozen> {
    builder: GreenNodeBuilder<'static>,
    recoveries: Vec<CommittedRecoveryRecord>,
    diagnostics: DiagnosticSequence<'frozen>,
}

impl RewriteOutput<'_> {
    pub(super) fn new() -> Self {
        Self {
            builder: GreenNodeBuilder::new(),
            recoveries: Vec::new(),
            diagnostics: DiagnosticSequence::fresh(),
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
        self.builder.token(kind, text);
    }

    #[inline]
    pub(super) fn finish_node(&mut self) {
        self.builder.finish_node();
    }

    pub(super) fn commit_recovery(&mut self, draft: RecoveryDraft) {
        let record = self.diagnostics.publish(draft);
        self.recoveries.push(record);
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
        (self.builder.finish(), self.recoveries)
    }

    #[cfg(test)]
    pub(super) fn recoveries(&self) -> &[CommittedRecoveryRecord] {
        &self.recoveries
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
        }
    }
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
