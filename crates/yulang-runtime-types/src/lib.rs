//! Runtime type representation and helpers shared between lower and refine.
//!
//! The `Type` re-export aliases `yulang_runtime_ir::RuntimeType`. Helpers in
//! `types::*` operate on the runtime IR (`yulang_runtime_ir::Module<Type>`
//! and friends) and provide substitution, projection, compatibility, and
//! effect-row utilities used by the lower and refine passes.

pub mod diagnostic;
pub mod types;

pub mod ir {
    pub use yulang_runtime_ir::RuntimeType as Type;
    pub use yulang_runtime_ir::{
        EffectIdRef, EffectIdVar, FinalizedBinding, FinalizedExpr, FinalizedExprKind,
        FinalizedHandleArm, FinalizedMatchArm, FinalizedModule, FinalizedPattern,
        FinalizedRecordExprField, FinalizedRecordPatternField, FinalizedRecordSpreadExpr,
        FinalizedRecordSpreadPattern, FinalizedResumeBinding, FinalizedStmt, HandleEffect,
        JoinEvidence, LoweredBinding, LoweredExpr, LoweredExprKind, LoweredHandleArm,
        LoweredMatchArm, LoweredModule, LoweredPattern, LoweredRecordExprField,
        LoweredRecordPatternField, LoweredRecordSpreadExpr, LoweredRecordSpreadPattern,
        LoweredResumeBinding, LoweredStmt, Root, RuntimeType, TypeInstantiation, TypeSubstitution,
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
pub use ir::{
    Binding, EffectIdRef, EffectIdVar, Expr, ExprKind, HandleArm, HandleEffect, JoinEvidence,
    MatchArm, Module, Pattern, RecordExprField, RecordPatternField, RecordSpreadExpr,
    RecordSpreadPattern, ResumeBinding, Root, Stmt, Type, TypeInstantiation, TypeSubstitution,
};
