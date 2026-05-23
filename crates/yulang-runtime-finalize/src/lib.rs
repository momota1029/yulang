//! Runtime finalization for Yulang.
//!
//! This crate is the new home for runtime type closure, monomorphic instance
//! planning, cast insertion, and final hole policy.  It is still experimental:
//! the public surface is intentionally small while the principal and body graph
//! responsibilities are separated.

mod body;
mod diagnostic;
mod effect;
mod emit;
mod module;
mod output;
mod planner;
mod principal;
mod role;
mod types;

pub use body::{BodyGraph, BodySolution, NestedInstancePlan};
pub use diagnostic::{
    BodyIncompleteReason, FinalizeDiagnostic, FinalizeError, FinalizeResult,
    PrincipalIncompleteReason,
};
pub use emit::{InstanceAliases, emit_instance_bindings, emit_instance_bindings_with_aliases};
pub use module::{RootBindingRequest, finalize_root_bindings, finalize_simple_root_exprs};
pub use output::{
    FinalizeOutput, FinalizeReport, RootInstance, TopLevelDemand, TopLevelRoot, finalize_module,
};
pub use planner::{FinalizedInstance, InstancePlan, InstancePlanner, InstanceState};
pub use principal::{InstanceKey, PrincipalGraph, PrincipalSolution};
pub use role::{AssociatedProjection, RoleContext, RoleProjectionStatus};
