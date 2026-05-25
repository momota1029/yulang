//! Runtime lowering for Yulang.
//!
//! This crate accepts the principal types and local evidence produced by the
//! infer pipeline, then lowers the program to a runtime tree where every
//! expression has an execution-facing type witness. The runtime IR data
//! structures themselves live in `yulang-runtime-ir`; type representation and
//! type-system helpers live in `yulang-runtime-types`; refine / validate /
//! invariant / hygiene live in `yulang-runtime-refine`; monomorphization
//! lives in `yulang-monomorphize`.

pub mod lower;

// Re-exports so existing callers can keep saying
// `yulang_runtime::types::...` / `yulang_runtime::diagnostic::...` /
// `yulang_runtime::refine::...` etc.
pub use yulang_runtime_types::{
    Binding, EffectIdRef, EffectIdVar, Expr, ExprKind, HandleArm, HandleEffect, JoinEvidence,
    MatchArm, Module, Pattern, RecordExprField, RecordPatternField, RecordSpreadExpr,
    RecordSpreadPattern, ResumeBinding, Root, RuntimeError, RuntimeResult, Stmt, Type,
    TypeInstantiation, TypeSource, TypeSubstitution, binding_is_parametric_runtime_intrinsic,
    diagnostic, ir, types,
};
pub use yulang_runtime_refine::{
    RuntimeStage, check_runtime_invariants, check_strict_runtime_type_surfaces,
    check_strict_runtime_value_types, format_hygiene_expr, format_hygiene_module, hygiene,
    invariant, refine, refine_module_types, validate, validate_module,
};
pub use lower::{
    CoreShapeProfile, DerivedExpectedEvidenceProfile, ExpectedAdapterEvidenceProfile,
    ExpectedArgEvidenceProfile, ObservedAdapterEvidence, ObservedAdapterEvidenceKind,
    RuntimeAdapterEvent, RuntimeAdapterEventKind, RuntimeAdapterProfile, RuntimeApplyAdapterPhase,
    RuntimeLowerOutput, RuntimeLowerProfile, lower_core_program, lower_core_program_profiled,
    lower_principal_module,
};
