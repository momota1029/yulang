//! Runtime lowering and validation for Yulang.
//!
//! This crate accepts the principal types and local evidence produced by the
//! infer pipeline, then lowers the program to a runtime tree where every
//! expression has an execution-facing type witness. The runtime IR data
//! structures themselves live in `yulang-runtime-ir`; type representation and
//! type-system helpers live in `yulang-runtime-types`. Monomorphization lives
//! in `yulang-monomorphize`.

pub mod hygiene;
pub mod invariant;
pub mod lower;
pub mod refine;
mod runtime_intrinsic;
pub mod validate;

// Re-export of types-crate items so existing callers can keep saying
// `yulang_runtime::types::...` / `yulang_runtime::diagnostic::...`.
pub(crate) use yulang_runtime_types as types_crate;
pub mod types {
    pub use super::types_crate::types::*;
}
pub mod diagnostic {
    pub use super::types_crate::diagnostic::*;
}
pub use yulang_runtime_types::{
    Binding, EffectIdRef, EffectIdVar, Expr, ExprKind, HandleArm, HandleEffect, JoinEvidence,
    MatchArm, Module, Pattern, RecordExprField, RecordPatternField, RecordSpreadExpr,
    RecordSpreadPattern, ResumeBinding, Root, RuntimeError, RuntimeResult, Stmt, Type,
    TypeInstantiation, TypeSource, TypeSubstitution, ir,
};
pub use hygiene::{format_hygiene_expr, format_hygiene_module};
pub use invariant::{
    RuntimeStage, check_runtime_invariants, check_strict_runtime_type_surfaces,
    check_strict_runtime_value_types,
};
pub use lower::{
    CoreShapeProfile, DerivedExpectedEvidenceProfile, ExpectedAdapterEvidenceProfile,
    ExpectedArgEvidenceProfile, ObservedAdapterEvidence, ObservedAdapterEvidenceKind,
    RuntimeAdapterEvent, RuntimeAdapterEventKind, RuntimeAdapterProfile, RuntimeApplyAdapterPhase,
    RuntimeLowerOutput, RuntimeLowerProfile, lower_core_program, lower_core_program_profiled,
    lower_principal_module,
};
pub use refine::refine_module_types;
pub use runtime_intrinsic::binding_is_parametric_runtime_intrinsic;
pub use validate::validate_module;
