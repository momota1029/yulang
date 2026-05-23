//! Runtime lowering, validation, and monomorphization for Yulang.
//!
//! This crate accepts the principal types and local evidence produced by the
//! infer pipeline, then builds and finalizes a runtime tree where every
//! expression has an execution-facing type witness. The runtime IR data
//! structures themselves live in `yulang-runtime-ir` and are re-exported here
//! for compatibility.

pub mod diagnostic;
pub mod hygiene;
pub mod invariant;
pub mod lower;
pub mod monomorphize;
pub mod refine;
mod runtime_intrinsic;
pub mod types;
pub mod validate;

pub mod ir {
    pub use yulang_runtime_ir::*;
}

pub use diagnostic::{RuntimeError, RuntimeResult, TypeSource};
pub use hygiene::{format_hygiene_expr, format_hygiene_module};
pub use invariant::{
    RuntimeStage, check_runtime_invariants, check_strict_runtime_type_surfaces,
    check_strict_runtime_value_types,
};
pub use ir::{
    Binding, EffectIdRef, EffectIdVar, Expr, ExprKind, HandleArm, HandleEffect, JoinEvidence,
    MatchArm, Module, Pattern, RecordExprField, RecordPatternField, RecordSpreadExpr,
    RecordSpreadPattern, ResumeBinding, Root, Stmt, Type, TypeInstantiation, TypeSubstitution,
};
pub use lower::{
    CoreShapeProfile, DerivedExpectedEvidenceProfile, ExpectedAdapterEvidenceProfile,
    ExpectedArgEvidenceProfile, ObservedAdapterEvidence, ObservedAdapterEvidenceKind,
    RuntimeAdapterEvent, RuntimeAdapterEventKind, RuntimeAdapterProfile, RuntimeApplyAdapterPhase,
    RuntimeLowerOutput, RuntimeLowerProfile, lower_core_program, lower_core_program_profiled,
    lower_principal_module,
};
pub use monomorphize::{
    DemandEvidenceProfile, DemandQueueProfile, MonomorphizePassProfile, MonomorphizeProfile,
    MonomorphizeProgress, SubstitutionSpecializeInferenceCount,
    SubstitutionSpecializeMissingVarCount, SubstitutionSpecializeProfile,
    SubstitutionSpecializeRewriteContextCount, SubstitutionSpecializeRewriteExprKindTiming,
    SubstitutionSpecializeRewritePhaseTiming, SubstitutionSpecializeSkipCount,
    SubstitutionSpecializeTargetInferences, SubstitutionSpecializeTargetRewrites,
    SubstitutionSpecializeTargetSkips, monomorphize_module, monomorphize_module_profiled,
};
pub use refine::refine_module_types;
pub use runtime_intrinsic::binding_is_parametric_runtime_intrinsic;
pub use validate::validate_module;
