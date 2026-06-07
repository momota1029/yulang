//! Runtime finalization for Yulang.
//!
//! The active rewrite starts from a fresh type graph.  A polymorphic principal
//! type is first instantiated into that graph, then each apply spine is solved
//! from the outside in: unify the current callee with the observed argument,
//! substitute through the callee return, and repeat.  Expression evidence is
//! collected as lower/upper bounds, and solving prefers lower bounds to return
//! a materializable monomorphic view of the graph.  When a solved body still
//! belongs to an outer generic binding, free outer variables are treated as
//! open runtime structure, not as graph slots owned by the inner instance.

mod cache;
mod diagnostic;
mod graph;
mod output;
mod solver;

pub use cache::{
    CachedMonomorphizeInstance, MONOMORPHIZE_INSTANCE_CACHE_FORMAT_VERSION,
    MonomorphizeInstanceArtifactCache, MonomorphizeInstanceArtifactCacheError,
    MonomorphizeInstanceArtifactCacheKey, MonomorphizeInstanceCache,
    MonomorphizeInstanceCachePolicy, MonomorphizeInstanceCacheProfile,
    MonomorphizeInstanceCacheSurface, MonomorphizeInstanceKey,
};
pub use diagnostic::{MonomorphizeDiagnostic, MonomorphizeError, MonomorphizeResult};
pub use graph::ResolvedTypeVar;
pub use graph::{
    GraphSolution, PrincipalInstance, PrincipalTypeParam, RuntimeBounds, TypeGraph, TypeVarBounds,
    materialize_core_type, materialize_runtime_type,
};
pub use output::{
    MonomorphizeOutput, MonomorphizeReport, RootGraphInput, RootGraphRoot, RootGraphSolution,
};
pub use solver::{
    collect_root_graph_inputs, finalize_module, finalize_module_with_cache, monomorphize_module,
    monomorphize_module_with_report, monomorphize_to_legacy_runtime_module,
};
