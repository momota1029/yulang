//! Structured errors produced while lowering CST bodies into `poly`.
//!
//! Formatting stays outside lowering; this enum carries the syntax kind or
//! structured annotation/signature error needed by diagnostics.

use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LoweringError {
    UnsupportedSyntax {
        kind: SyntaxKind,
    },
    UnsupportedPatternSyntax {
        kind: SyntaxKind,
    },
    UnsupportedRuleLazyQuantifier {
        kind: SyntaxKind,
        source_range: SourceRange,
    },
    UnresolvedName {
        name: Name,
        source_range: Option<SourceRange>,
    },
    InvalidNumber {
        text: String,
    },
    MissingLambdaBody,
    MissingIfCondition,
    MissingIfBody,
    MissingCaseScrutinee,
    MissingCaseArmPattern,
    MissingCaseArmBody,
    MissingCatchScrutinee {
        source_range: SourceRange,
    },
    MissingCatchArmPattern {
        source_range: SourceRange,
    },
    MissingCatchArmBody {
        source_range: SourceRange,
    },
    MissingFieldName,
    MissingOpName,
    MissingOpOperand,
    MissingRecordFieldName,
    MissingRecordFieldValue,
    MissingIndexArgument,
    MissingLocalBindingName,
    MissingLocalBindingBody,
    UnsupportedTopLevelVarBinding {
        name: Name,
        source_range: Option<SourceRange>,
    },
    MissingLocalVarAct {
        name: Name,
    },
    MissingSubLabelAct {
        label: Name,
    },
    AnnotationBuild {
        error: AnnBuildError,
        source_range: Option<SourceRange>,
    },
    AnnotationConstraint {
        error: AnnConstraintError,
    },
    NegSignatureBuild {
        error: NegSignatureBuildError,
    },
    SignatureConstraint {
        error: SignatureConstraintError,
    },
    SignatureShapeMismatch {
        expected: SignatureShape,
    },
    SignatureTypeMismatch {
        expected: SignatureShape,
    },
    TypeMismatch {
        actual: String,
        expected: String,
        actual_range: Option<SourceRange>,
        expected_range: Option<SourceRange>,
    },
}

impl LoweringError {
    pub(in crate::lowering) fn annotation_build(error: AnnBuildError, type_expr: &Cst) -> Self {
        let source_range = annotation_build_source_range(&error, type_expr);
        Self::annotation_build_at(error, Some(source_range))
    }

    pub(in crate::lowering) fn annotation_build_for_stored_signature(
        error: AnnBuildError,
        signature: &StoredSignature,
    ) -> Self {
        let source_range = match signature {
            StoredSignature::Source(type_expr) => Some(crate::node_source_range(type_expr)),
            StoredSignature::Lowered(_) => None,
        };
        Self::annotation_build_at(error, source_range)
    }

    pub(in crate::lowering) fn annotation_build_at(
        error: AnnBuildError,
        source_range: Option<SourceRange>,
    ) -> Self {
        Self::AnnotationBuild {
            error,
            source_range,
        }
    }
}

fn annotation_build_source_range(error: &AnnBuildError, type_expr: &Cst) -> SourceRange {
    match error {
        AnnBuildError::UnresolvedTypeName { path } => path
            .last()
            .and_then(|name| crate::source_range_for_name(type_expr, name))
            .unwrap_or_else(|| crate::node_source_range(type_expr)),
        _ => crate::node_source_range(type_expr),
    }
}
