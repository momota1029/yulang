//! Runtime finalization for Yulang.
//!
//! This crate is the new home for runtime type closure, monomorphic instance
//! planning, cast insertion, and final hole policy.  It is still experimental:
//! the public surface is intentionally small while the principal and body graph
//! responsibilities are separated.

mod body;
mod diagnostic;
mod output;
mod principal;
mod types;

pub use body::{BodyGraph, BodySolution, NestedInstancePlan};
pub use diagnostic::{
    BodyIncompleteReason, FinalizeDiagnostic, FinalizeError, FinalizeResult,
    PrincipalIncompleteReason,
};
pub use output::{FinalizeOutput, FinalizeReport, TopLevelDemand, TopLevelRoot, finalize_module};
pub use principal::{InstanceKey, PrincipalGraph, PrincipalSolution};
