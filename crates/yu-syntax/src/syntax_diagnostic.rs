//! Structured diagnostics emitted by the syntax phase.

use std::ops::Range;

use crate::{
    OperatorFixity, operator_table::OperatorOrigin, recovery_record::CommittedRecoveryRecord,
};

/// Structured syntax diagnostic owned by the syntax phase.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SyntaxDiagnostic {
    id: u32,
    primary: Range<usize>,
    cause: SyntaxDiagnosticCause,
}

impl SyntaxDiagnostic {
    pub(crate) fn recovery(record: CommittedRecoveryRecord) -> Self {
        Self {
            id: record.id.0,
            primary: record.site.range.clone(),
            cause: SyntaxDiagnosticCause::Recovery(RecoveryDiagnostic { record }),
        }
    }

    pub(crate) fn conflicting_operator_fixity(
        id: u32,
        conflict: crate::operator_compilation::RejectedOperatorFixity,
    ) -> Self {
        let primary = conflict.second_range.clone();
        Self {
            id,
            primary,
            cause: SyntaxDiagnosticCause::ConflictingOperatorFixity(OperatorConflictDiagnostic {
                spelling: conflict.spelling,
                fixity: conflict.fixity,
                first_origin: conflict.first_origin,
                first_range: conflict.first_range,
                second_origin: conflict.second_origin,
                second_range: conflict.second_range,
            }),
        }
    }

    pub fn id(&self) -> u32 {
        self.id
    }

    pub fn primary(&self) -> &Range<usize> {
        &self.primary
    }

    pub fn cause(&self) -> &SyntaxDiagnosticCause {
        &self.cause
    }
}

/// The typed cause of a syntax diagnostic.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SyntaxDiagnosticCause {
    /// A committed grammar recovery, distinct from semantic table construction.
    Recovery(RecoveryDiagnostic),
    ConflictingOperatorFixity(OperatorConflictDiagnostic),
}

/// The committed recovery record behind a recovery diagnostic.
///
/// Its typed site, unexpected evidence, and expectation union remain an
/// internal grammar vocabulary until the diagnostic presentation API is
/// versioned, but no information is collapsed into a message string here.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RecoveryDiagnostic {
    record: CommittedRecoveryRecord,
}

impl RecoveryDiagnostic {
    #[cfg(test)]
    pub(crate) fn record(&self) -> &CommittedRecoveryRecord {
        &self.record
    }
}

/// One rejected operator capability and the already-accepted conflicting site.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OperatorConflictDiagnostic {
    spelling: Box<str>,
    fixity: OperatorFixity,
    first_origin: OperatorOrigin,
    first_range: Range<usize>,
    second_origin: OperatorOrigin,
    second_range: Range<usize>,
}

impl OperatorConflictDiagnostic {
    pub fn spelling(&self) -> &str {
        &self.spelling
    }

    pub fn fixity(&self) -> OperatorFixity {
        self.fixity
    }

    pub fn first_origin(&self) -> OperatorOrigin {
        self.first_origin
    }

    pub fn first_range(&self) -> &Range<usize> {
        &self.first_range
    }

    pub fn second_origin(&self) -> OperatorOrigin {
        self.second_origin
    }

    pub fn second_range(&self) -> &Range<usize> {
        &self.second_range
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    use crate::recovery_record::{
        DiagnosticId, ExpectationSources, ExpectedSyntax, GrammarRole, RecoveryKind,
        RecoverySiteKey, StatementRole, SyntaxExpectation,
    };

    #[test]
    fn recovery_diagnostic_keeps_the_committed_record_distinct_from_construction() {
        let record = CommittedRecoveryRecord {
            id: DiagnosticId(9),
            site: RecoverySiteKey {
                role: GrammarRole::Statement(StatementRole::Starter),
                range: 4..4,
            },
            kind: RecoveryKind::Missing,
            unexpected: Arc::from([]),
            expectations: Arc::from([SyntaxExpectation {
                role: GrammarRole::Statement(StatementRole::Starter),
                expected: ExpectedSyntax::Expression,
                range: 4..4,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            primary_expectation: 0,
        };
        let diagnostic = SyntaxDiagnostic::recovery(record.clone());

        assert_eq!(diagnostic.id(), 9);
        assert_eq!(diagnostic.primary(), &(4..4));
        let SyntaxDiagnosticCause::Recovery(recovery) = diagnostic.cause() else {
            panic!("a recovery record must not be a construction conflict");
        };
        assert_eq!(recovery.record(), &record);
    }
}
