use rowan::TextRange;

use crate::check::{CheckDiagnostic, RelatedDiagnostic, check_lowered, collect_check_type_errors};
use crate::diagnostic::TypeError;
use crate::lower::{FileSpan, LowerState};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SurfaceDiagnostic {
    pub message: String,
    pub span: Option<TextRange>,
    pub related: Vec<SurfaceRelatedDiagnostic>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SurfaceRelatedDiagnostic {
    pub message: String,
    pub span: Option<TextRange>,
    pub file_span: Option<FileSpan>,
}

pub fn collect_surface_diagnostics(state: &LowerState) -> Vec<SurfaceDiagnostic> {
    check_lowered(state)
        .diagnostics
        .into_iter()
        .map(surface_diagnostic_from_check)
        .collect()
}

pub fn collect_surface_type_errors(state: &LowerState) -> Vec<TypeError> {
    collect_check_type_errors(state)
}

fn surface_diagnostic_from_check(diagnostic: CheckDiagnostic) -> SurfaceDiagnostic {
    SurfaceDiagnostic {
        message: diagnostic.message,
        span: diagnostic.primary.map(|span| span.range),
        related: diagnostic
            .related
            .into_iter()
            .map(surface_related_from_check)
            .collect(),
    }
}

fn surface_related_from_check(related: RelatedDiagnostic) -> SurfaceRelatedDiagnostic {
    SurfaceRelatedDiagnostic {
        message: related.message,
        span: related.span,
        file_span: related.file_span,
    }
}
