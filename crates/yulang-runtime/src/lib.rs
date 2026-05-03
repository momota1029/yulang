//! Typed runtime IR for Yulang.
//!
//! Runtime IR is intentionally not a second type inference engine. It accepts
//! the principal types and local evidence produced by the infer pipeline, then
//! builds a runtime tree where every expression has a VM-facing type witness. Polymorphic
//! variables that appear in a principal type are kept as `forall` parameters;
//! observation-only variables are erased before validation.

pub mod diagnostic;
pub mod hygiene;
pub mod invariant;
pub mod ir;
pub mod lower;
pub mod monomorphize;
pub mod refine;
pub mod runtime;
pub mod types;
pub mod validate;
pub mod vm;

pub use diagnostic::{RuntimeError, RuntimeResult, TypeSource};
pub use hygiene::{format_hygiene_expr, format_hygiene_module};
pub use invariant::{RuntimeStage, check_runtime_invariants, check_strict_runtime_value_types};
pub use ir::{
    Binding, EffectIdRef, EffectIdVar, Expr, ExprKind, HandleArm, HandleEffect, JoinEvidence,
    MatchArm, Module, Pattern, RecordExprField, RecordPatternField, RecordSpreadExpr,
    RecordSpreadPattern, ResumeBinding, Root, Stmt, Type, TypeInstantiation, TypeSubstitution,
};
pub use lower::{
    ExpectedArgEvidenceProfile, RuntimeAdapterProfile, RuntimeLowerOutput, RuntimeLowerProfile,
    lower_core_program, lower_core_program_profiled, lower_principal_module,
};
pub use monomorphize::{
    DemandEvidenceProfile, DemandQueueProfile, MonomorphizePassProfile, MonomorphizeProfile,
    MonomorphizeProgress, monomorphize_module, monomorphize_module_profiled,
};
pub use refine::refine_module_types;
pub use validate::validate_module;
pub use vm::{VmError, VmModule, VmRequest, VmResult, VmValue, compile_vm_module};
