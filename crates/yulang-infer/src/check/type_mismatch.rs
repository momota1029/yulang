use std::cmp::Reverse;

use crate::diagnostic::{
    ConstraintReason, ExpectedEdge, ExpectedEdgeKind, ExpectedShape, TypeError, TypeErrorKind,
    TypeOrigin, TypeOriginKind, type_error_vars,
};
use crate::ids::TypeVar;
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
        type_error_related(state, error),
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

fn type_error_related(state: &LowerState, error: &TypeError) -> Vec<RelatedDiagnostic> {
    let mut related = Vec::new();
    if let Some(edge) = best_expected_edge_for_error(state, error) {
        push_related(
            &mut related,
            expected_edge_context_message(edge),
            edge.cause.span,
            None,
        );
        push_expected_edge_origin_related(state, edge, &mut related);
    }
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

fn best_expected_edge_for_error<'a>(
    state: &'a LowerState,
    error: &TypeError,
) -> Option<&'a ExpectedEdge> {
    let error_vars = type_error_vars(&state.infer, error);
    state
        .expected_edges
        .iter()
        .filter(|edge| expected_edge_is_diagnostic_context(edge.kind))
        .filter_map(|edge| {
            let rank = expected_edge_error_rank(edge, error, &error_vars);
            (rank.score > 0).then_some((rank, edge))
        })
        .max_by_key(|(rank, _)| *rank)
        .map(|(_, edge)| edge)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct ExpectedEdgeRank {
    score: u8,
    span_match: bool,
    reason_match: bool,
    kind_priority: u8,
    shorter_span: Reverse<u32>,
}

fn expected_edge_error_rank(
    edge: &ExpectedEdge,
    error: &TypeError,
    error_vars: &[TypeVar],
) -> ExpectedEdgeRank {
    let mut score = 0;
    if error_vars.contains(&edge.actual_tv) {
        score += 3;
    }
    if error_vars.contains(&edge.expected_tv) {
        score += 3;
    }
    if edge
        .actual_eff
        .is_some_and(|actual_eff| error_vars.contains(&actual_eff))
    {
        score += 3;
    }
    if edge
        .expected_eff
        .is_some_and(|expected_eff| error_vars.contains(&expected_eff))
    {
        score += 3;
    }
    let span_match = edge.cause.span == error.cause.span;
    if span_match {
        score += 2;
    }
    let reason_match = edge.cause.reason == error.cause.reason;
    if reason_match {
        score += 1;
    }
    ExpectedEdgeRank {
        score,
        span_match,
        reason_match,
        kind_priority: expected_edge_kind_priority(edge.kind),
        shorter_span: Reverse(expected_edge_span_len(edge)),
    }
}

fn expected_edge_is_diagnostic_context(kind: ExpectedEdgeKind) -> bool {
    matches!(
        kind,
        ExpectedEdgeKind::Annotation
            | ExpectedEdgeKind::ApplicationCallee
            | ExpectedEdgeKind::ApplicationArgument
            | ExpectedEdgeKind::IfCondition
            | ExpectedEdgeKind::IfBranch
            | ExpectedEdgeKind::MatchGuard
            | ExpectedEdgeKind::MatchBranch
            | ExpectedEdgeKind::CatchGuard
            | ExpectedEdgeKind::CatchBranch
            | ExpectedEdgeKind::RecordField
            | ExpectedEdgeKind::VariantPayload
            | ExpectedEdgeKind::AssignmentValue
    )
}

fn expected_edge_kind_priority(kind: ExpectedEdgeKind) -> u8 {
    match kind {
        ExpectedEdgeKind::Annotation
        | ExpectedEdgeKind::ApplicationArgument
        | ExpectedEdgeKind::AssignmentValue => 4,
        ExpectedEdgeKind::IfBranch
        | ExpectedEdgeKind::MatchBranch
        | ExpectedEdgeKind::CatchBranch
        | ExpectedEdgeKind::RecordField
        | ExpectedEdgeKind::VariantPayload => 3,
        ExpectedEdgeKind::ApplicationCallee
        | ExpectedEdgeKind::IfCondition
        | ExpectedEdgeKind::MatchGuard
        | ExpectedEdgeKind::CatchGuard => 2,
        ExpectedEdgeKind::RepresentationCoerce => 1,
    }
}

fn expected_edge_span_len(edge: &ExpectedEdge) -> u32 {
    edge.cause
        .span
        .map(|span| u32::from(span.end()) - u32::from(span.start()))
        .unwrap_or(u32::MAX)
}

fn expected_edge_context_message(edge: &ExpectedEdge) -> String {
    format!(
        "{} compares {} with {}",
        expected_edge_context_label(edge.kind),
        expected_edge_actual_label(edge.kind),
        expected_edge_expected_label(edge.kind),
    )
}

fn expected_edge_context_label(kind: ExpectedEdgeKind) -> &'static str {
    match kind {
        ExpectedEdgeKind::IfCondition => "if condition",
        ExpectedEdgeKind::IfBranch => "if branch",
        ExpectedEdgeKind::MatchGuard => "match guard",
        ExpectedEdgeKind::MatchBranch => "match branch",
        ExpectedEdgeKind::CatchGuard => "catch guard",
        ExpectedEdgeKind::CatchBranch => "catch branch",
        ExpectedEdgeKind::ApplicationCallee => "function callee",
        ExpectedEdgeKind::ApplicationArgument => "function argument",
        ExpectedEdgeKind::Annotation => "type annotation",
        ExpectedEdgeKind::RecordField => "record field",
        ExpectedEdgeKind::VariantPayload => "variant payload",
        ExpectedEdgeKind::AssignmentValue => "assignment value",
        ExpectedEdgeKind::RepresentationCoerce => "representation coercion",
    }
}

fn expected_edge_actual_label(kind: ExpectedEdgeKind) -> &'static str {
    match kind {
        ExpectedEdgeKind::ApplicationCallee => "callee actual type",
        ExpectedEdgeKind::ApplicationArgument => "argument actual type",
        ExpectedEdgeKind::Annotation => "expression actual type",
        ExpectedEdgeKind::AssignmentValue => "assigned value type",
        ExpectedEdgeKind::IfCondition
        | ExpectedEdgeKind::MatchGuard
        | ExpectedEdgeKind::CatchGuard => "condition type",
        ExpectedEdgeKind::IfBranch
        | ExpectedEdgeKind::MatchBranch
        | ExpectedEdgeKind::CatchBranch => "branch result type",
        ExpectedEdgeKind::RecordField => "field value type",
        ExpectedEdgeKind::VariantPayload => "payload type",
        ExpectedEdgeKind::RepresentationCoerce => "representation type",
    }
}

fn expected_edge_expected_label(kind: ExpectedEdgeKind) -> &'static str {
    match kind {
        ExpectedEdgeKind::ApplicationCallee => "callable type",
        ExpectedEdgeKind::ApplicationArgument => "parameter type",
        ExpectedEdgeKind::Annotation => "annotation type",
        ExpectedEdgeKind::AssignmentValue => "reference slot type",
        ExpectedEdgeKind::IfCondition
        | ExpectedEdgeKind::MatchGuard
        | ExpectedEdgeKind::CatchGuard => "bool",
        ExpectedEdgeKind::IfBranch
        | ExpectedEdgeKind::MatchBranch
        | ExpectedEdgeKind::CatchBranch => "expected branch result type",
        ExpectedEdgeKind::RecordField => "declared field type",
        ExpectedEdgeKind::VariantPayload => "declared payload type",
        ExpectedEdgeKind::RepresentationCoerce => "surface type",
    }
}

fn push_expected_edge_origin_related(
    state: &LowerState,
    edge: &ExpectedEdge,
    related: &mut Vec<RelatedDiagnostic>,
) {
    if let Some(origin) = state.infer.origin_of(edge.actual_tv) {
        push_type_origin_related(
            related,
            format!("{} comes from here", expected_edge_actual_label(edge.kind)),
            &origin,
        );
    } else {
        push_edge_fallback_related(
            related,
            format!("{} comes from here", expected_edge_actual_label(edge.kind)),
            edge,
        );
    }
    if let Some(origin) = state.infer.origin_of(edge.expected_tv) {
        push_type_origin_related(
            related,
            format!(
                "{} comes from here",
                expected_edge_expected_label(edge.kind)
            ),
            &origin,
        );
    } else {
        push_edge_fallback_related(
            related,
            format!(
                "{} comes from here",
                expected_edge_expected_label(edge.kind)
            ),
            edge,
        );
    }
}

fn push_type_origin_related(
    related: &mut Vec<RelatedDiagnostic>,
    message: String,
    origin: &TypeOrigin,
) {
    let Some(span) = origin.span else {
        return;
    };
    push_related(related, message, Some(span), origin.file_span);
}

fn push_edge_fallback_related(
    related: &mut Vec<RelatedDiagnostic>,
    message: String,
    edge: &ExpectedEdge,
) {
    let Some(span) = edge.cause.span else {
        return;
    };
    push_related(related, message, Some(span), None);
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
