use crate::diagnostic::{
    ConstraintReason, ExpectedEdge, ExpectedEdgeKind, ExpectedShape, TypeError, TypeErrorKind,
    TypeOrigin, TypeOriginKind,
};
use crate::lower::{FileSpan, LowerState};
use crate::solve::CastMethodResolution;

use super::report::CheckReportBuilder;
use super::{DiagnosticCode, RelatedDiagnostic};

pub fn collect_check_type_errors(state: &LowerState) -> Vec<TypeError> {
    state
        .infer
        .type_errors()
        .into_iter()
        .filter(|error| !should_defer_type_error_to_cast_boundary(state, error))
        .collect()
}

pub(crate) fn push_type_error(
    builder: &mut CheckReportBuilder,
    state: &LowerState,
    error: &TypeError,
) {
    builder.push(
        type_error_code(error),
        type_error_message(state, error),
        error.cause.span,
        type_error_related(error),
    );
}

fn should_defer_type_error_to_cast_boundary(state: &LowerState, error: &TypeError) -> bool {
    if error.kind != TypeErrorKind::ConstructorMismatch {
        return false;
    }
    state
        .expected_edges
        .iter()
        .any(|edge| edge_matches_deferred_cast_boundary(state, edge, error))
}

fn edge_matches_deferred_cast_boundary(
    state: &LowerState,
    edge: &ExpectedEdge,
    error: &TypeError,
) -> bool {
    edge.cause == error.cause
        && expected_edge_can_defer_constructor_mismatch(edge.kind)
        && matches!(
            state
                .infer
                .resolve_cast_method_from_pos_neg(error.pos, error.neg),
            CastMethodResolution::Concrete(_)
        )
}

fn expected_edge_can_defer_constructor_mismatch(kind: ExpectedEdgeKind) -> bool {
    matches!(
        kind,
        ExpectedEdgeKind::Annotation
            | ExpectedEdgeKind::ApplicationArgument
            | ExpectedEdgeKind::IfBranch
            | ExpectedEdgeKind::MatchBranch
            | ExpectedEdgeKind::CatchBranch
    )
}

fn type_error_code(error: &TypeError) -> DiagnosticCode {
    match error.kind {
        TypeErrorKind::ConstructorMismatch => DiagnosticCode::TypeMismatch,
        TypeErrorKind::TupleArityMismatch { .. } => DiagnosticCode::TupleArityMismatch,
        TypeErrorKind::MissingRecordField { .. } => DiagnosticCode::MissingRecordField,
        TypeErrorKind::UnknownRecordField { .. } => DiagnosticCode::UnknownRecordField,
        TypeErrorKind::ExpectedShape { .. } => DiagnosticCode::ExpectedShape,
        TypeErrorKind::MissingImpl { .. } => DiagnosticCode::MissingImpl,
        TypeErrorKind::MissingImplMember { .. } => DiagnosticCode::MissingImplMember,
        TypeErrorKind::UnknownImplMember { .. } => DiagnosticCode::UnknownImplMember,
        TypeErrorKind::AmbiguousImpl { .. } => DiagnosticCode::AmbiguousImpl,
        TypeErrorKind::MissingImplPrerequisite { .. } => DiagnosticCode::MissingImplPrerequisite,
        TypeErrorKind::AmbiguousImplPrerequisite { .. } => {
            DiagnosticCode::AmbiguousImplPrerequisite
        }
        TypeErrorKind::AmbiguousEffectMethod { .. } => DiagnosticCode::AmbiguousEffectMethod,
    }
}

fn type_error_message(state: &LowerState, error: &TypeError) -> String {
    match &error.kind {
        TypeErrorKind::ConstructorMismatch => format!(
            "expected {}, found {}",
            crate::display::dump::format_neg_for_diagnostic(&state.infer, error.neg),
            crate::display::dump::format_pos_for_diagnostic(&state.infer, error.pos),
        ),
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

fn type_error_related(error: &TypeError) -> Vec<RelatedDiagnostic> {
    let mut related = Vec::new();
    if let Some(message) = type_error_cause_message(error) {
        push_related(&mut related, message, error.cause.span, None);
    }
    for origin in &error.origins {
        let Some(span) = origin.span else {
            continue;
        };
        push_related(
            &mut related,
            type_origin_message(origin),
            Some(span),
            origin.file_span,
        );
    }
    related
}

fn push_related(
    related: &mut Vec<RelatedDiagnostic>,
    message: String,
    span: Option<rowan::TextRange>,
    file_span: Option<FileSpan>,
) {
    if related.iter().any(|existing| {
        existing.span == span && existing.file_span == file_span && existing.message == message
    }) {
        return;
    }
    related.push(RelatedDiagnostic {
        message,
        span,
        file_span,
    });
}

fn type_error_cause_message(error: &TypeError) -> Option<String> {
    match error.cause.reason {
        ConstraintReason::Annotation => {
            Some("type annotation contributes this expectation".to_string())
        }
        _ => None,
    }
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
