//! Runtime finalization for Yulang.
//!
//! The active rewrite starts from a fresh type graph.  A polymorphic principal
//! type is first instantiated into that graph, then expression evidence is
//! collected as lower/upper bounds.  Solving prefers lower bounds and returns a
//! fully materializable monomorphic view of the graph.
//!
//! The previous implementation is archived under
//! `archive/2026-05-23-pre-rewrite`.

mod cache;
mod diagnostic;
mod graph;
mod output;
mod solver;

pub use cache::{
    CachedFinalizeInstance, FINALIZE_INSTANCE_CACHE_FORMAT_VERSION, FinalizeInstanceArtifactCache,
    FinalizeInstanceArtifactCacheError, FinalizeInstanceArtifactCacheKey, FinalizeInstanceCache,
    FinalizeInstanceCachePolicy, FinalizeInstanceCacheProfile, FinalizeInstanceCacheSurface,
    FinalizeInstanceKey,
};
pub use diagnostic::{FinalizeDiagnostic, FinalizeMonomorphizeError, FinalizeResult};
pub use graph::ResolvedTypeVar;
pub use graph::{
    GraphSolution, PrincipalInstance, PrincipalTypeParam, RuntimeBounds, TypeGraph, TypeVarBounds,
    materialize_core_type, materialize_runtime_type,
};
pub use output::{
    FinalizeOutput, FinalizeReport, RootGraphInput, RootGraphRoot, RootGraphSolution,
};
pub use solver::{
    collect_root_graph_inputs, finalize_module, finalize_module_with_cache,
    finalize_monomorphize_legacy_runtime_module, finalize_monomorphize_module,
    finalize_monomorphize_module_with_report,
};
