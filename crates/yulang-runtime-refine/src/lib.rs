//! Runtime type refinement, validation, invariant checks, and hygiene printing.
//!
//! All four passes operate on the runtime IR produced by `yulang-runtime` and
//! share the same type-system helpers from `yulang-runtime-types`. They sit
//! between lower and monomorphize (or after either) depending on the caller.

pub mod hygiene;
pub mod invariant;
pub mod refine;
pub mod validate;

pub use hygiene::{format_hygiene_expr, format_hygiene_module};
pub use invariant::{
    RuntimeStage, check_runtime_invariants, check_strict_runtime_type_surfaces,
    check_strict_runtime_value_types,
};
pub use refine::refine_module_types;
pub use validate::validate_module;
