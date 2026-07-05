//! `mono` から軽量 control 表現へ下げて実行する VM crate。
//!
//! `mono-runtime` は oracle として tree をそのまま読む。この crate は同じ契約を、`ExprId`
//! で参照する軽量表現へ機械的に lowering してから読む。

#![forbid(unsafe_code)]

mod boundary;
mod effect_profile;
mod evidence_ir;
mod format;
mod ir;
mod lower;
mod runtime;
mod validate;

pub use evidence_ir::{
    ControlAdapterEvidence, ControlDelayedBoundary, ControlDelayedBoundaryKind,
    ControlEffectEvidence, ControlEffectUseKind, ControlEvidenceInstance, ControlEvidenceProgram,
    ControlEvidenceRoute, ControlFallbackEvidence, ControlFallbackKind, ControlHandlerArmEvidence,
    ControlHandlerEvidence, ControlTypeEvidence, ControlTypeEvidenceOwner, ControlTypedExprSlot,
    format_control_evidence_program,
};
pub use format::format_values;
pub use ir::{
    Block, CaseArm, CatchArm, DefId, Expr, ExprId, Instance, InstanceId, Pat, Program, RecordField,
    RecordSpread, Root, SelectResolution, Stmt,
};
pub use lower::{LowerError, lower};
pub use runtime::{
    CapturedEnv, Closure, ContinuationId, FunctionAdapter, GuardId, RunError, RuntimeError,
    RuntimeStats, RuntimeTimings, Thunk, Value, ValueField, ValueMarker, run_mono_program,
    run_program, run_program_with_host, run_program_with_host_and_stats,
    run_program_with_host_stats_and_timings,
};
pub use validate::{ValidateError, validate};

#[cfg(test)]
mod tests;
