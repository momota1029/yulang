//! CST/environment-derived syntax diagnostics.

use std::ops::Range;

use crate::{
    OperatorFixity, SyntaxDiagnosticIdentity, operator_table::OperatorOrigin,
    structural_diagnostic::StructuralDiagnostic,
};

/// One diagnostic emitted by the current CST/environment analysis walk.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SyntaxDiagnostic {
    identity: SyntaxDiagnosticIdentity,
    primary: Range<usize>,
    cause: SyntaxDiagnosticCause,
}

impl SyntaxDiagnostic {
    pub(crate) fn structural(occurrence: StructuralDiagnostic) -> Self {
        Self {
            identity: occurrence.identity(),
            primary: occurrence.range().clone(),
            cause: SyntaxDiagnosticCause::Structural(occurrence),
        }
    }

    pub(crate) fn conflicting_operator_fixity(
        identity: SyntaxDiagnosticIdentity,
        conflict: crate::operator_compilation::RejectedOperatorFixity,
    ) -> Self {
        Self {
            identity,
            primary: conflict.second_range.clone(),
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

    pub fn primary(&self) -> &Range<usize> {
        &self.primary
    }

    pub fn identity(&self) -> &SyntaxDiagnosticIdentity {
        &self.identity
    }

    pub fn cause(&self) -> &SyntaxDiagnosticCause {
        &self.cause
    }
}

/// The CST or selected-environment fact that caused a syntax diagnostic.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SyntaxDiagnosticCause {
    Structural(StructuralDiagnostic),
    ConflictingOperatorFixity(OperatorConflictDiagnostic),
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
