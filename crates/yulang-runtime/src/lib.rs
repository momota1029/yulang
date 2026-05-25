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
mod runtime_type;
pub mod types;
pub mod validate;

pub mod ir {
    pub use crate::runtime_type::Type;
    pub use yulang_runtime_ir::{
        EffectIdRef, EffectIdVar, FinalizedBinding, FinalizedExpr, FinalizedExprKind,
        FinalizedHandleArm, FinalizedMatchArm, FinalizedModule, FinalizedPattern,
        FinalizedRecordExprField, FinalizedRecordPatternField, FinalizedRecordSpreadExpr,
        FinalizedRecordSpreadPattern, FinalizedResumeBinding, FinalizedStmt, FinalizedType,
        HandleEffect, JoinEvidence, LoweredBinding, LoweredExpr, LoweredExprKind, LoweredHandleArm,
        LoweredMatchArm, LoweredModule, LoweredPattern, LoweredRecordExprField,
        LoweredRecordPatternField, LoweredRecordSpreadExpr, LoweredRecordSpreadPattern,
        LoweredResumeBinding, LoweredStmt, Root, TypeInstantiation, TypeSubstitution,
    };

    pub type Module = yulang_runtime_ir::Module<Type>;
    pub type Binding = yulang_runtime_ir::Binding<Type>;
    pub type Expr = yulang_runtime_ir::Expr<Type>;
    pub type ExprKind = yulang_runtime_ir::ExprKind<Type>;
    pub type Stmt = yulang_runtime_ir::Stmt<Type>;
    pub type Pattern = yulang_runtime_ir::Pattern<Type>;
    pub type RecordExprField = yulang_runtime_ir::RecordExprField<Type>;
    pub type RecordSpreadExpr = yulang_runtime_ir::RecordSpreadExpr<Type>;
    pub type RecordPatternField = yulang_runtime_ir::RecordPatternField<Type>;
    pub type RecordSpreadPattern = yulang_runtime_ir::RecordSpreadPattern<Type>;
    pub type MatchArm = yulang_runtime_ir::MatchArm<Type>;
    pub type HandleArm = yulang_runtime_ir::HandleArm<Type>;
    pub type ResumeBinding = yulang_runtime_ir::ResumeBinding<Type>;
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
