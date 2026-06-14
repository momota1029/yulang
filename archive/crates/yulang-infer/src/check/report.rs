use std::collections::BTreeSet;

use rowan::TextRange;

use crate::lower::FileSpan;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct CheckReport {
    pub diagnostics: Vec<CheckDiagnostic>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckDiagnostic {
    pub code: DiagnosticCode,
    pub severity: DiagnosticSeverity,
    pub message: String,
    pub primary: Option<DiagnosticSpan>,
    pub related: Vec<RelatedDiagnostic>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DiagnosticCode {
    UndefinedPath,
    UnresolvedSelection,
    AmbiguousSelection,
    TypeMismatch,
    TupleArityMismatch,
    MissingRecordField,
    UnknownRecordField,
    ExpectedShape,
    MissingImpl,
    AmbiguousImpl,
    MissingImplMember,
    UnknownImplMember,
    MissingImplPrerequisite,
    AmbiguousImplPrerequisite,
    AmbiguousEffectMethod,
    NonExhaustivePattern,
    UnreachablePattern,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DiagnosticSeverity {
    Error,
    Warning,
    Info,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DiagnosticSpan {
    pub range: TextRange,
    pub file_span: Option<FileSpan>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RelatedDiagnostic {
    pub message: String,
    pub span: Option<TextRange>,
    pub file_span: Option<FileSpan>,
}

impl CheckReport {
    pub fn new() -> Self {
        Self {
            diagnostics: Vec::new(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.diagnostics.is_empty()
    }
}

impl DiagnosticCode {
    pub fn as_str(self) -> &'static str {
        match self {
            DiagnosticCode::UndefinedPath => "name.undefined",
            DiagnosticCode::UnresolvedSelection => "selection.unresolved",
            DiagnosticCode::AmbiguousSelection => "selection.ambiguous",
            DiagnosticCode::TypeMismatch => "type.mismatch",
            DiagnosticCode::TupleArityMismatch => "type.tuple_arity_mismatch",
            DiagnosticCode::MissingRecordField => "type.record.missing_field",
            DiagnosticCode::UnknownRecordField => "type.record.unknown_field",
            DiagnosticCode::ExpectedShape => "type.expected_shape",
            DiagnosticCode::MissingImpl => "role.impl.missing",
            DiagnosticCode::AmbiguousImpl => "role.impl.ambiguous",
            DiagnosticCode::MissingImplMember => "role.impl.missing_member",
            DiagnosticCode::UnknownImplMember => "role.impl.unknown_member",
            DiagnosticCode::MissingImplPrerequisite => "role.impl.missing_prerequisite",
            DiagnosticCode::AmbiguousImplPrerequisite => "role.impl.ambiguous_prerequisite",
            DiagnosticCode::AmbiguousEffectMethod => "effect.method.ambiguous",
            DiagnosticCode::NonExhaustivePattern => "pattern.non_exhaustive",
            DiagnosticCode::UnreachablePattern => "pattern.unreachable_arm",
        }
    }
}

impl DiagnosticSpan {
    pub fn source(range: TextRange) -> Self {
        Self {
            range,
            file_span: None,
        }
    }
}

#[derive(Debug, Default)]
pub(crate) struct CheckReportBuilder {
    report: CheckReport,
    seen: BTreeSet<(String, Option<u32>, Option<u32>)>,
}

impl CheckReportBuilder {
    pub(crate) fn push(
        &mut self,
        code: DiagnosticCode,
        message: String,
        span: Option<TextRange>,
        related: Vec<RelatedDiagnostic>,
    ) {
        self.push_with_file_span(code, message, span, None, related);
    }

    pub(crate) fn push_with_file_span(
        &mut self,
        code: DiagnosticCode,
        message: String,
        span: Option<TextRange>,
        file_span: Option<FileSpan>,
        related: Vec<RelatedDiagnostic>,
    ) {
        let key = (
            message.clone(),
            span.map(|span| u32::from(span.start())),
            file_span.map(|span| span.file.0),
        );
        if self.seen.insert(key) {
            self.report.diagnostics.push(CheckDiagnostic {
                code,
                severity: DiagnosticSeverity::Error,
                message,
                primary: span.map(|range| DiagnosticSpan { range, file_span }),
                related,
            });
        }
    }

    pub(crate) fn finish(self) -> CheckReport {
        self.report
    }
}
