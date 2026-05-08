//! Native backend skeleton for Yulang.
//!
//! This crate starts with a small control IR boundary.  Cranelift codegen will
//! sit behind this boundary later; for now the important behavior is that
//! supported runtime IR lowers explicitly and unsupported runtime IR fails with
//! a structured reason.

pub mod compare;
pub mod control_ir;
pub mod eval;
pub mod lower;

pub use compare::{NativeCompareError, compare_module};
pub use control_ir::{
    BlockId, NativeBlock, NativeFunction, NativeLiteral, NativeModule, NativeStmt,
    NativeTerminator, ValueId,
};
pub use eval::{NativeEvalError, eval_module};
pub use lower::{NativeLowerError, NativeLowerResult, lower_module};
