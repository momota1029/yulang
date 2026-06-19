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
    MissingCatchScrutinee,
    MissingCatchArmPattern,
    MissingCatchArmBody,
    MissingFieldName,
    MissingOpName,
    MissingOpOperand,
    MissingRecordFieldName,
    MissingRecordFieldValue,
    MissingIndexArgument,
    MissingLocalBindingName,
    MissingLocalBindingBody,
    MissingLocalVarAct {
        name: Name,
    },
    MissingSubLabelAct {
        label: Name,
    },
    AnnotationBuild {
        error: AnnBuildError,
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
    },
}
