//! Runtime lowering and validation for Yulang.
//!
//! This crate accepts the principal types and local evidence produced by the
//! infer pipeline, then lowers the program to a runtime tree where every
//! expression has an execution-facing type witness. The runtime IR data
//! structures themselves live in `yulang-runtime-ir` and are re-exported here
//! for compatibility. Monomorphization lives in `yulang-monomorphize`.

pub mod diagnostic;
pub mod hygiene;
pub mod invariant;
pub mod lower;
pub mod refine;
mod runtime_intrinsic;
pub mod types;
pub mod validate;

pub mod ir {
    // `Type` is the runtime-IR type stage: same shape as `FinalizedModule<RuntimeType>`,
    // re-exported here so existing call sites can keep saying `runtime::Type`.
    pub use yulang_runtime_ir::RuntimeType as Type;
    pub use yulang_runtime_ir::{
        EffectIdRef, EffectIdVar, FinalizedBinding, FinalizedExpr, FinalizedExprKind,
        FinalizedHandleArm, FinalizedMatchArm, FinalizedModule, FinalizedPattern,
        FinalizedRecordExprField, FinalizedRecordPatternField, FinalizedRecordSpreadExpr,
        FinalizedRecordSpreadPattern, FinalizedResumeBinding, FinalizedStmt, RuntimeType,
        HandleEffect, JoinEvidence, LoweredBinding, LoweredExpr, LoweredExprKind, LoweredHandleArm,
        LoweredMatchArm, LoweredModule, LoweredPattern, LoweredRecordExprField,
        LoweredRecordPatternField, LoweredRecordSpreadExpr, LoweredRecordSpreadPattern,
        LoweredResumeBinding, LoweredStmt, Root, TypeInstantiation, TypeSubstitution,
    };

    pub type Module = yulang_runtime_ir::Module<RuntimeType>;
    pub type Binding = yulang_runtime_ir::Binding<RuntimeType>;
    pub type Expr = yulang_runtime_ir::Expr<RuntimeType>;
    pub type ExprKind = yulang_runtime_ir::ExprKind<RuntimeType>;
    pub type Stmt = yulang_runtime_ir::Stmt<RuntimeType>;
    pub type Pattern = yulang_runtime_ir::Pattern<RuntimeType>;
    pub type RecordExprField = yulang_runtime_ir::RecordExprField<RuntimeType>;
    pub type RecordSpreadExpr = yulang_runtime_ir::RecordSpreadExpr<RuntimeType>;
    pub type RecordPatternField = yulang_runtime_ir::RecordPatternField<RuntimeType>;
    pub type RecordSpreadPattern = yulang_runtime_ir::RecordSpreadPattern<RuntimeType>;
    pub type MatchArm = yulang_runtime_ir::MatchArm<RuntimeType>;
    pub type HandleArm = yulang_runtime_ir::HandleArm<RuntimeType>;
    pub type ResumeBinding = yulang_runtime_ir::ResumeBinding<RuntimeType>;
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
pub use refine::refine_module_types;
pub use runtime_intrinsic::binding_is_parametric_runtime_intrinsic;
pub use validate::validate_module;
