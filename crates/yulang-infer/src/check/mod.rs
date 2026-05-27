mod exhaustiveness;
mod report;
mod type_mismatch;

pub use report::{
    CheckDiagnostic, CheckReport, DiagnosticCode, DiagnosticSeverity, DiagnosticSpan,
    RelatedDiagnostic,
};
pub use type_mismatch::collect_check_type_errors;

use crate::lower::LowerState;
use crate::symbols::Path;

use exhaustiveness::push_case_exhaustiveness;
use report::CheckReportBuilder;
use type_mismatch::push_type_error;

pub fn check_lowered(state: &LowerState) -> CheckReport {
    state.infer.resolve_final_structural_record_selections();

    let mut builder = CheckReportBuilder::default();

    for (_, unresolved) in state.ctx.refs.unresolved() {
        builder.push(
            DiagnosticCode::UndefinedPath,
            unresolved_path_message(&unresolved.path),
            None,
            Vec::new(),
        );
    }

    for selections in state.infer.deferred_selections.borrow().values() {
        for selection in selections {
            let (code, message) = if selection.structural_record_allowed
                && state
                    .infer
                    .selection_name_has_non_record_candidate_from(selection.module, &selection.name)
            {
                (
                    DiagnosticCode::AmbiguousSelection,
                    ambiguous_selection_message(selection.name.0.as_str()),
                )
            } else {
                (
                    DiagnosticCode::UnresolvedSelection,
                    unresolved_selection_message(selection.name.0.as_str()),
                )
            };
            builder.push(code, message, selection.cause.span, Vec::new());
        }
    }

    for error in collect_check_type_errors(state) {
        push_type_error(&mut builder, state, &error);
    }

    push_case_exhaustiveness(&mut builder, state);

    builder.finish()
}
fn unresolved_path_message(path: &Path) -> String {
    let path = format_path(path);
    if path.contains("::") {
        format!("undefined path `{path}`")
    } else {
        format!("undefined name `{path}`")
    }
}

fn unresolved_selection_message(name: &str) -> String {
    match name {
        "index" => "cannot index this value; no matching index operation was found".to_string(),
        _ => format!("no field or method named `.{name}` could be resolved"),
    }
}

fn ambiguous_selection_message(name: &str) -> String {
    format!(
        "could not resolve `.{name}` because the receiver type is not specific enough to choose a method; add a receiver type annotation"
    )
}

fn format_path(path: &Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}
