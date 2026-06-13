//! `mono` から軽量 control 表現へ下げて実行する VM crate。
//!
//! `mono-runtime` は oracle として tree をそのまま読む。この crate は同じ契約を、`ExprId`
//! で参照する軽量表現へ機械的に lowering してから読む。

#![forbid(unsafe_code)]

mod format;
mod ir;
mod lower;
mod runtime;

pub use format::format_values;
pub use ir::{
    Block, CaseArm, CatchArm, DefId, Expr, ExprId, Instance, InstanceId, Pat, Program, RecordField,
    RecordSpread, Root, SelectResolution, Stmt,
};
pub use lower::{LowerError, lower};
pub use runtime::{
    CapturedEnv, Closure, ContinuationId, FunctionAdapter, GuardId, RunError, RuntimeError, Thunk,
    Value, ValueField, ValueMarker, run_mono_program, run_program,
};

#[cfg(test)]
mod tests;
