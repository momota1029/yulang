use std::collections::BTreeSet;

use rowan::TextRange;

use crate::diagnostic::{ExpectedShape, TypeError, TypeErrorKind, TypeOrigin, TypeOriginKind};
use crate::lower::LowerState;
use crate::symbols::Path;

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
}

pub fn collect_surface_diagnostics(state: &LowerState) -> Vec<SurfaceDiagnostic> {
    state.infer.resolve_final_structural_record_selections();

    let mut diagnostics = Vec::new();
    let mut seen = BTreeSet::new();

    for (_, unresolved) in state.ctx.refs.unresolved() {
        let message = unresolved_path_message(&unresolved.path);
        push_unique(&mut diagnostics, &mut seen, message, None, Vec::new());
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
            push_unique(
                &mut diagnostics,
                &mut seen,
                message,
                selection.cause.span,
                Vec::new(),
            );
        }
    }

    for error in state.infer.type_errors() {
        push_type_error(&mut diagnostics, &mut seen, &error);
    }

    diagnostics
}

fn push_unique(
    diagnostics: &mut Vec<SurfaceDiagnostic>,
    seen: &mut BTreeSet<(String, Option<u32>)>,
    message: String,
    span: Option<TextRange>,
    related: Vec<SurfaceRelatedDiagnostic>,
) {
    let key = (message.clone(), span.map(|span| u32::from(span.start())));
    if seen.insert(key) {
        diagnostics.push(SurfaceDiagnostic {
            message,
            span,
            related,
        });
    }
}

fn push_type_error(
    diagnostics: &mut Vec<SurfaceDiagnostic>,
    seen: &mut BTreeSet<(String, Option<u32>)>,
    error: &TypeError,
) {
    push_unique(
        diagnostics,
        seen,
        type_error_message(error),
        error.cause.span,
        type_error_related(error),
    );
}

fn type_error_message(error: &TypeError) -> String {
    match &error.kind {
        TypeErrorKind::ConstructorMismatch => "type mismatch".to_string(),
        TypeErrorKind::TupleArityMismatch { pos_len, neg_len } => {
            format!("tuple arity mismatch: expected {neg_len}, found {pos_len}")
        }
        TypeErrorKind::MissingRecordField { name } => {
            format!("missing required record field `{name}`")
        }
        TypeErrorKind::UnknownRecordField { name } => {
            format!("unknown record field `{name}`")
        }
        TypeErrorKind::ExpectedShape { expected } => match expected {
            ExpectedShape::Function => "expected function".to_string(),
            ExpectedShape::Tuple => "expected tuple".to_string(),
            ExpectedShape::Record => "expected record".to_string(),
            ExpectedShape::Constructor => "expected constructor".to_string(),
        },
        TypeErrorKind::MissingImpl { role, args } => {
            if role.ends_with("Cast") && args.len() >= 2 {
                return format!("no implicit cast from {} to {}", args[0], args[1]);
            }
            format!("no impl for {}<{}>", role, args.join(", "))
        }
        TypeErrorKind::MissingImplMember { role, member } => {
            format!("impl {role} is missing required member `{member}`")
        }
        TypeErrorKind::UnknownImplMember { role, member } => {
            format!("impl {role} defines unknown member `{member}`")
        }
        TypeErrorKind::AmbiguousImpl {
            role,
            args,
            candidates,
            previews,
        } => {
            if role.ends_with("Cast") && args.len() >= 2 {
                return format!(
                    "ambiguous implicit cast from {} to {} ({} candidates)",
                    args[0], args[1], candidates
                );
            }
            let preview_suffix = impl_preview_suffix(previews);
            format!(
                "ambiguous impl for {}<{}> ({} candidates{})",
                role,
                args.join(", "),
                candidates,
                preview_suffix,
            )
        }
        TypeErrorKind::MissingImplPrerequisite {
            role,
            args,
            prerequisite_role,
            prerequisite_args,
        } => {
            format!(
                "impl {}<{}> requires {}<{}>",
                role,
                args.join(", "),
                prerequisite_role,
                prerequisite_args.join(", "),
            )
        }
        TypeErrorKind::AmbiguousImplPrerequisite {
            role,
            args,
            prerequisite_role,
            prerequisite_args,
            candidates,
            previews,
        } => {
            let preview_suffix = impl_preview_suffix(previews);
            format!(
                "impl {}<{}> requires ambiguous {}<{}> ({} candidates{})",
                role,
                args.join(", "),
                prerequisite_role,
                prerequisite_args.join(", "),
                candidates,
                preview_suffix,
            )
        }
        TypeErrorKind::AmbiguousEffectMethod { method, effects } => {
            format!(
                "ambiguous effect method `{}` from effects {}",
                method,
                effects.join(", ")
            )
        }
    }
}

fn impl_preview_suffix(previews: &[String]) -> String {
    if previews.is_empty() {
        String::new()
    } else {
        format!(
            ": {}",
            previews
                .iter()
                .take(2)
                .cloned()
                .collect::<Vec<_>>()
                .join(" vs ")
        )
    }
}

fn type_error_related(error: &TypeError) -> Vec<SurfaceRelatedDiagnostic> {
    let mut related = Vec::new();
    for origin in &error.origins {
        let Some(span) = origin.span else {
            continue;
        };
        let message = type_origin_message(origin);
        if related.iter().any(|existing: &SurfaceRelatedDiagnostic| {
            existing.span == Some(span) && existing.message == message
        }) {
            continue;
        }
        related.push(SurfaceRelatedDiagnostic {
            message,
            span: Some(span),
        });
    }
    related
}

fn type_origin_message(origin: &TypeOrigin) -> String {
    match origin.kind {
        TypeOriginKind::Literal => match origin.label.as_deref() {
            Some(label) => format!("literal `{label}` contributes this type"),
            None => "literal contributes this type".to_string(),
        },
        TypeOriginKind::Binding => match origin.label.as_deref() {
            Some(label) => format!("binding `{label}` contributes this type"),
            None => "binding contributes this type".to_string(),
        },
        TypeOriginKind::Param => match origin.label.as_deref() {
            Some(label) => format!("parameter `{label}` contributes this type"),
            None => "parameter contributes this type".to_string(),
        },
        TypeOriginKind::Annotation => "type annotation contributes this expectation".to_string(),
        TypeOriginKind::ApplicationResult => "application result is required here".to_string(),
        TypeOriginKind::EffectOperation => "effect operation contributes this type".to_string(),
        TypeOriginKind::FieldSelection => "field selection contributes this type".to_string(),
        TypeOriginKind::Synthetic => origin
            .label
            .clone()
            .unwrap_or_else(|| "compiler-generated type contributes here".to_string()),
        TypeOriginKind::Unknown => "type comes from here".to_string(),
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
