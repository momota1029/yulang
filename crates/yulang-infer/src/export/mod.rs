//! Export principal inference results into core IR.
//!
//! This stage is the boundary between source-oriented inference data and the
//! runtime pipeline.  It should preserve principal schemes, role evidence,
//! join evidence, and effect annotations that later stages cannot safely
//! rediscover from syntax.  It should not perform VM-oriented thunk repair or
//! monomorphization.

mod complete_principal;
pub mod expr;
pub mod names;
pub(crate) mod paths;
pub mod principal;
mod roles;
mod spine;
pub mod types;

pub use complete_principal::{
    DerivedExpectedEdgeEvidence, DerivedExpectedEdgeKind, EdgePathSegment, EdgePolarity,
    ExpectedEdgeEvidence, collect_derived_expected_edge_evidence, collect_expected_edge_evidence,
};
pub use principal::{export_core_program, export_principal_bindings, export_principal_module};
pub use types::export_scheme_body;
