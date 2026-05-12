use std::collections::BTreeSet;

use rowan::TextRange;

use crate::lower::LowerState;
use crate::symbols::Path;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SurfaceDiagnostic {
    pub message: String,
    pub span: Option<TextRange>,
}

pub fn collect_surface_diagnostics(state: &LowerState) -> Vec<SurfaceDiagnostic> {
    state.infer.resolve_final_structural_record_selections();

    let mut diagnostics = Vec::new();
    let mut seen = BTreeSet::new();

    for (_, unresolved) in state.ctx.refs.unresolved() {
        let message = unresolved_path_message(&unresolved.path);
        push_unique(&mut diagnostics, &mut seen, message, None);
    }

    for selections in state.infer.deferred_selections.borrow().values() {
        for selection in selections {
            let message = if selection.structural_record_allowed
                && state
                    .infer
                    .selection_name_has_non_record_candidate_from(selection.module, &selection.name)
            {
                ambiguous_selection_message(selection.name.0.as_str())
            } else {
                unresolved_selection_message(selection.name.0.as_str())
            };
            push_unique(&mut diagnostics, &mut seen, message, selection.cause.span);
        }
    }

    diagnostics
}

fn push_unique(
    diagnostics: &mut Vec<SurfaceDiagnostic>,
    seen: &mut BTreeSet<(String, Option<u32>)>,
    message: String,
    span: Option<TextRange>,
) {
    let key = (message.clone(), span.map(|span| u32::from(span.start())));
    if seen.insert(key) {
        diagnostics.push(SurfaceDiagnostic { message, span });
    }
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
