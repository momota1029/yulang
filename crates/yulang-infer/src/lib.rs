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
pub mod surface_diagnostic;
pub mod symbols;
pub mod types;

pub use ast::{
    ExprKind, Lit, TypedBlock, TypedCatchArm, TypedExpr, TypedMatchArm, TypedPat, TypedStmt,
};
pub use diagnostic::{
    ConstraintCause, ConstraintReason, ExpectedShape, TypeError, TypeErrorKind, TypeOrigin,
    TypeOriginKind,
};
pub use display::{
    collect_compact_results, collect_compact_results_for_paths, format_coalesced_scheme,
    format_compact_scheme, render_compact_results, render_exported_compact_results,
};
pub use export::{
    export_core_program, export_principal_bindings, export_principal_module, export_scheme_body,
};
pub use ids::{DefId, RefId, TypeVar, fresh_def_id, fresh_ref_id, fresh_type_var};
pub use lower::stmt::{finish_lowering, lower_root, lower_root_in_module};
pub use lower::{FinalizeCompactProfile, FinalizeCompactResults, LowerDetailProfile, LowerState};
pub use ref_table::{RefTable, UnresolvedRef};
pub use scc::*;
pub use scheme::FrozenScheme;
pub use simplify::compact::{CompactBounds, CompactType, CompactTypeScheme};
pub use solve::{
    DeferredSelection, ExtensionMethodInfo, Infer, RoleArgInfo, RoleConstraint, RoleConstraintArg,
    RoleMethodInfo,
};
pub use source::{
    LoweredSources, ProfiledLoweredSources, SourceLowerProfile, lower_entry_with_options,
    lower_entry_with_options_profiled, lower_source_file, lower_source_file_profiled,
    lower_source_set, lower_source_set_profiled, lower_virtual_source_with_options,
    lower_virtual_source_with_options_profiled,
};
pub use surface_diagnostic::{SurfaceDiagnostic, collect_surface_diagnostics};
pub use symbols::{
    ModuleId, ModuleNode, ModuleTable, Name, Namespace, OperatorFixity, Path, Reexport, Visibility,
};
pub use types::arena::TypeArena;
pub use types::{EffectAtom, Neg, Pos, RecordField, Variance};
pub use yulang_source::{
    SourceLoadError, SourceOptions, SourceSet, collect_virtual_source_files_with_options,
};

#[cfg(test)]
mod tests;
