pub mod artifact_cache;
pub mod ast;
pub mod diagnostic;
pub mod display;
pub mod export;
pub mod ids;
pub(crate) mod lower;
pub(crate) mod profile;
pub mod ref_table;
pub mod scc;
pub mod scheme;
pub mod simplify;
pub mod solve;
pub mod source;
pub(crate) mod std_flow_paths;
pub(crate) mod std_ref_paths;
pub mod surface_diagnostic;
pub mod symbols;
pub mod types;

pub use artifact_cache::{
    CompiledUnitArtifactCache, CompiledUnitArtifactCacheError, CompiledUnitArtifactCacheKey,
};
pub use ast::{
    ExprKind, Lit, TypedBlock, TypedCatchArm, TypedExpr, TypedMatchArm, TypedPat, TypedStmt,
};
pub use diagnostic::{
    ConstraintCause, ConstraintReason, ExpectedAdapterEdge, ExpectedAdapterEdgeId,
    ExpectedAdapterEdgeKind, ExpectedEdge, ExpectedEdgeId, ExpectedEdgeKind, ExpectedShape,
    TypeError, TypeErrorKind, TypeOrigin, TypeOriginKind,
};
pub use display::{
    collect_compact_results, collect_compact_results_for_paths,
    collect_compact_results_for_paths_in_scope, collect_expected_edges, format_coalesced_scheme,
    format_coalesced_scheme_in_scope, format_compact_scheme, render_compact_results,
    render_exported_compact_results,
};
pub use export::{
    DerivedExpectedEdgeEvidence, DerivedExpectedEdgeKind, EdgePathSegment, EdgePolarity,
    ExpectedAdapterEdgeEvidence, ExpectedEdgeEvidence, collect_derived_expected_edge_evidence,
    collect_expected_adapter_edge_evidence, collect_expected_edge_evidence, export_core_program,
    export_core_program_for_binding_paths, export_principal_bindings, export_principal_module,
    export_scheme_body,
};
pub use ids::{DefId, RefId, TypeVar, fresh_def_id, fresh_ref_id, fresh_type_var};
pub use lower::ctx::LowerCtx;
pub use lower::stmt::{finish_lowering, lower_root, lower_root_in_module};
pub use lower::{
    FileId, FileInfo, FileSpan, FinalizeCompactProfile, FinalizeCompactResults,
    LowerDetailProfile, LowerState,
};
pub use profile::with_profile_enabled;
pub use ref_table::{RefTable, UnresolvedRef};
pub use scc::*;
pub use scheme::FrozenScheme;
pub use simplify::compact::{CompactBounds, CompactType, CompactTypeScheme};
pub use solve::{
    DeferredSelection, ExtensionMethodInfo, Infer, RoleArgInfo, RoleConstraint, RoleConstraintArg,
    RoleMethodInfo,
};
pub use source::{
    CompiledRuntimeBundle, CompiledRuntimeMergeError, CompiledRuntimeSurface, CompiledUnitArtifact,
    CompiledUnitArtifactsImport, CompiledUnitArtifactsImportError,
    CompiledUnitProfiledLoweredSources, LoweredSources, ProfiledLoweredSources,
    STD_INFER_SNAPSHOT_FORMAT_VERSION, SourceLowerCache, SourceLowerProfile, SourceStdCacheProfile,
    StdCoreSnapshotData, StdInferSnapshot, StdInferSnapshotData, StdInferSnapshotDataError,
    StdInferSnapshotEffect, StdInferSnapshotEffectMethod, StdInferSnapshotEffectOperation,
    StdInferSnapshotImport, StdInferSnapshotImportCoverage, StdInferSnapshotImportError,
    StdInferSnapshotImportMissing, StdInferSnapshotImportRefs, StdInferSnapshotManifest,
    StdInferSnapshotMissingPath, StdInferSnapshotModule, StdInferSnapshotModuleChild,
    StdInferSnapshotModuleOperator, StdInferSnapshotModuleType, StdInferSnapshotModuleValue,
    StdInferSnapshotNamespace, StdInferSnapshotOperatorFixity, StdInferSnapshotReexport,
    StdInferSnapshotRole, StdInferSnapshotRoleArg, StdInferSnapshotRoleImpl,
    StdInferSnapshotRoleImplMember, StdInferSnapshotRoleMethod, StdInferSnapshotScheme,
    StdInferSnapshotSymbol, StdInferSnapshotVisibility, StdSourceCacheKey,
    build_compiled_unit_artifacts, build_std_core_snapshot_data, build_std_infer_snapshot,
    build_std_infer_snapshot_data, import_compiled_unit_artifacts, import_std_infer_snapshot_data,
    lower_entry_with_options, lower_entry_with_options_profiled, lower_source_file,
    lower_source_file_profiled, lower_source_set, lower_source_set_profiled,
    lower_source_set_with_compiled_unit_artifacts_profiled, lower_source_set_with_std_cache,
    lower_source_set_with_std_cache_profiled, lower_source_set_with_std_snapshot,
    lower_virtual_source_with_options, lower_virtual_source_with_options_profiled,
    warm_std_source_cache,
};
pub use surface_diagnostic::{SurfaceDiagnostic, collect_surface_diagnostics};
pub use symbols::{
    ModuleId, ModuleNode, ModuleTable, Name, Namespace, OperatorFixity, Path, Reexport, Visibility,
};
pub use types::arena::TypeArena;
pub use types::{EffectAtom, Neg, Pos, RecordField, Variance};
pub use yulang_sources::{
    SourceLoadError, SourceOptions, SourceOrigin, SourceSet,
    collect_virtual_source_files_with_options,
};

#[cfg(test)]
mod tests;
