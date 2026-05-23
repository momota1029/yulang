use std::collections::{HashMap, HashSet};
use std::path::{Path as FsPath, PathBuf};
use std::time::{Duration, Instant};

use rowan::SyntaxNode;
use serde::{Deserialize, Serialize};
use yulang_parser::lex::SyntaxKind;
use yulang_parser::parse_module_to_green_with_ops;
use yulang_parser::sink::YulangLanguage;
use yulang_sources::{
    CompiledSyntaxSurface, CompiledUnitManifest, SourceCompilationUnitOrigin, SourceFile,
    SourceLoadError, SourceOptions, SourceOrigin, SourceSet, collect_source_files_with_options,
    collect_virtual_module_source_files_with_options, collect_virtual_source_files_with_options,
};

use crate::ids::TypeVar;
use crate::lower::primitives::install_builtin_primitives;
use crate::lower::stmt::{finish_lowering, lower_root_in_module};
use crate::lower::{LowerDetailProfile, LowerState};
use crate::profile::{ProfileClock, with_profile_enabled};
use crate::simplify::compact::{CompactBounds, CompactType, CompactTypeScheme};
use crate::simplify::cooccur::CompactRoleConstraint;
use crate::symbols::{ModuleId, Name, Namespace, OperatorFixity, Path, Visibility};
use yulang_typed_ir as typed_ir;
use yulang_typed_ir::CoreProgram;

pub struct LoweredSources {
    pub state: LowerState,
    pub diagnostic_source: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledUnitNamespaceArtifact {
    pub manifest: CompiledUnitManifest,
    pub namespace: CompiledNamespaceSurface,
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct CompiledNamespaceSurface {
    pub modules: Vec<CompiledNamespaceModule>,
    pub values: Vec<CompiledNamespaceSymbol>,
    pub types: Vec<CompiledNamespaceSymbol>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledNamespaceModule {
    pub path: Vec<String>,
    pub values: Vec<CompiledNamespaceModuleValue>,
    pub operators: Vec<CompiledNamespaceModuleOperator>,
    pub types: Vec<CompiledNamespaceModuleType>,
    pub modules: Vec<CompiledNamespaceModuleChild>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledNamespaceModuleValue {
    pub name: String,
    pub symbol: u32,
    pub visibility: StdInferSnapshotVisibility,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledNamespaceModuleOperator {
    pub name: String,
    pub fixity: StdInferSnapshotOperatorFixity,
    pub symbol: u32,
    pub visibility: StdInferSnapshotVisibility,
    #[serde(default)]
    pub lazy: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledNamespaceModuleType {
    pub name: String,
    pub symbol: u32,
    pub visibility: StdInferSnapshotVisibility,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledNamespaceModuleChild {
    pub name: String,
    pub module_path: Vec<String>,
    pub visibility: StdInferSnapshotVisibility,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledNamespaceSymbol {
    pub path: Vec<String>,
    pub unit_id: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct CompiledNamespaceBundle {
    pub surface: CompiledNamespaceSurface,
}

impl CompiledNamespaceBundle {
    pub fn from_artifacts(artifacts: &[CompiledUnitNamespaceArtifact]) -> Self {
        Self {
            surface: merge_compiled_namespace_surfaces(
                artifacts.iter().map(|artifact| &artifact.namespace),
            ),
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CompiledNamespaceValidation {
    pub modules: usize,
    pub values: usize,
    pub types: usize,
    pub operators: usize,
    pub missing_value_symbols: Vec<CompiledNamespaceMissingSymbol>,
    pub missing_type_symbols: Vec<CompiledNamespaceMissingSymbol>,
}

impl CompiledNamespaceValidation {
    pub fn is_complete(&self) -> bool {
        self.missing_value_symbols.is_empty() && self.missing_type_symbols.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompiledNamespaceMissingSymbol {
    pub module_path: Vec<String>,
    pub name: String,
    pub symbol: u32,
}

impl CompiledNamespaceSurface {
    pub fn validate(&self) -> CompiledNamespaceValidation {
        validate_compiled_namespace_surface(self)
    }
}

pub struct CompiledNamespaceImport {
    pub state: LowerState,
    pub values: Vec<Option<crate::ids::DefId>>,
    pub types: Vec<Option<crate::ids::DefId>>,
    pub validation: CompiledNamespaceValidation,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompiledNamespaceImportError {
    InvalidNamespace(CompiledNamespaceValidation),
}

pub struct CompiledTypedImport {
    pub namespace: CompiledNamespaceImport,
    pub refs: CompiledTypedImportRefs,
    pub coverage: CompiledTypedImportCoverage,
    pub validation: CompiledTypedValidation,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CompiledTypedImportRefs {
    pub schemes: Vec<Option<crate::ids::DefId>>,
    pub role_methods: Vec<Option<crate::ids::DefId>>,
    pub role_impl_members: Vec<Vec<Option<crate::ids::DefId>>>,
    pub effect_methods: Vec<Option<crate::ids::DefId>>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledTypedImportCoverage {
    pub namespace_values_total: usize,
    pub namespace_values_resolved: usize,
    pub namespace_types_total: usize,
    pub namespace_types_resolved: usize,
    pub schemes_total: usize,
    pub schemes_resolved: usize,
    pub role_methods_total: usize,
    pub role_methods_resolved: usize,
    pub effect_methods_total: usize,
    pub effect_methods_resolved: usize,
}

impl CompiledTypedImportCoverage {
    pub fn has_complete_ref_resolution(&self) -> bool {
        self.namespace_values_total == self.namespace_values_resolved
            && self.namespace_types_total == self.namespace_types_resolved
            && self.schemes_total == self.schemes_resolved
            && self.role_methods_total == self.role_methods_resolved
            && self.effect_methods_total == self.effect_methods_resolved
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompiledTypedImportError {
    InvalidNamespace(CompiledNamespaceValidation),
    InvalidTyped(CompiledTypedValidation),
}

pub struct CompiledUnitImport {
    pub syntax: CompiledSyntaxSurface,
    pub typed: CompiledTypedImport,
    pub runtime: CompiledRuntimeSurface,
}

pub struct CompiledUnitArtifactsImport {
    pub manifests: Vec<CompiledUnitManifest>,
    pub typed: CompiledTypedImport,
    pub runtime: CompiledRuntimeBundle,
}

pub struct CompiledUnitSemanticImport {
    pub manifests: Vec<CompiledUnitManifest>,
    pub typed: CompiledTypedImport,
}

pub struct CompiledUnitProfiledLoweredSources {
    pub lowered: ProfiledLoweredSources,
    pub runtime: CompiledRuntimeBundle,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct CompiledUnitImportProfile {
    pub reserve_type_vars: Duration,
    pub namespace_builtin: Duration,
    pub namespace_skeletons: Duration,
    pub namespace_module_map: Duration,
    pub namespace_values: Duration,
    pub namespace_types: Duration,
    pub namespace_entries: Duration,
    pub namespace_validation: Duration,
    pub typed_refs: Duration,
    pub compact_schemes: Duration,
    pub lookup_tables: Duration,
    pub typed_coverage: Duration,
    pub typed_validation: Duration,
    pub manifests_clone: Duration,
    pub runtime_clone: Duration,
    pub cached_state_lower: Duration,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompiledUnitImportError {
    InvalidTyped(CompiledTypedImportError),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompiledUnitArtifactsImportError {
    InvalidTyped(CompiledTypedImportError),
    InvalidRuntime(CompiledRuntimeMergeError),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledUnitTypedArtifact {
    pub manifest: CompiledUnitManifest,
    pub namespace: CompiledNamespaceSurface,
    pub typed: CompiledTypedSurface,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledUnitArtifact {
    pub manifest: CompiledUnitManifest,
    pub syntax: CompiledSyntaxSurface,
    pub namespace: CompiledNamespaceSurface,
    pub typed: CompiledTypedSurface,
    pub runtime: CompiledRuntimeSurface,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledUnitArtifactBundle {
    pub manifests: Vec<CompiledUnitManifest>,
    pub namespace: CompiledNamespaceSurface,
    pub typed: CompiledTypedSurface,
    pub runtime: CompiledRuntimeBundle,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledUnitSemanticArtifactBundle {
    pub manifests: Vec<CompiledUnitManifest>,
    pub namespace: CompiledNamespaceSurface,
    pub typed: CompiledTypedSurface,
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct CompiledTypedSurface {
    pub schemes: Vec<StdInferSnapshotScheme>,
    pub roles: Vec<StdInferSnapshotRole>,
    pub role_methods: Vec<StdInferSnapshotRoleMethod>,
    pub role_impls: Vec<StdInferSnapshotRoleImpl>,
    pub effects: Vec<StdInferSnapshotEffect>,
    pub effect_methods: Vec<StdInferSnapshotEffectMethod>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct CompiledRuntimeSurface {
    pub program: CoreProgram,
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct CompiledRuntimeBundle {
    pub surface: CompiledRuntimeSurface,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompiledRuntimeMergeError {
    ConflictingBinding {
        path: typed_ir::Path,
    },
    ConflictingGraphBinding {
        path: typed_ir::Path,
    },
    ConflictingRuntimeSymbol {
        path: typed_ir::Path,
    },
    ConflictingPrimitiveType {
        family: typed_ir::PrimitiveTypeFamily,
    },
}

impl CompiledRuntimeBundle {
    pub fn from_surfaces<'a>(
        surfaces: impl IntoIterator<Item = &'a CompiledRuntimeSurface>,
    ) -> Result<Self, CompiledRuntimeMergeError> {
        merge_compiled_runtime_surfaces(surfaces).map(|surface| Self { surface })
    }

    pub fn merge_with_user_program(
        &self,
        user_program: CoreProgram,
    ) -> Result<CoreProgram, CompiledRuntimeMergeError> {
        merge_runtime_bundle_with_user_program(&self.surface, user_program)
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CompiledTypedValidation {
    pub schemes: usize,
    pub roles: usize,
    pub role_methods: usize,
    pub role_impls: usize,
    pub effects: usize,
    pub effect_methods: usize,
    pub missing_scheme_symbols: Vec<u32>,
    pub missing_role_method_symbols: Vec<u32>,
    pub missing_role_impl_member_symbols: Vec<u32>,
    pub missing_effect_method_symbols: Vec<u32>,
}

impl CompiledTypedValidation {
    pub fn is_complete(&self) -> bool {
        self.missing_scheme_symbols.is_empty()
            && self.missing_role_method_symbols.is_empty()
            && self.missing_role_impl_member_symbols.is_empty()
            && self.missing_effect_method_symbols.is_empty()
    }
}

impl CompiledTypedSurface {
    pub fn validate(&self, namespace: &CompiledNamespaceSurface) -> CompiledTypedValidation {
        validate_compiled_typed_surface(self, namespace)
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SourceLowerProfile {
    pub collect: Duration,
    pub parse: Duration,
    pub lower_roots: Duration,
    pub finish: Duration,
    pub detail: LowerDetailProfile,
    pub files: usize,
    pub entry_files: usize,
    pub std_files: usize,
    pub user_files: usize,
    pub entry: SourceOriginLowerProfile,
    pub std: SourceOriginLowerProfile,
    pub user: SourceOriginLowerProfile,
    pub std_cache: SourceStdCacheProfile,
}

impl SourceLowerProfile {
    pub fn total(&self) -> Duration {
        self.collect + self.parse + self.lower_roots + self.finish
    }

    pub fn infer_lower(&self) -> Duration {
        self.lower_roots + self.finish
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SourceOriginLowerProfile {
    pub files: usize,
    pub parse: Duration,
    pub lower_roots: Duration,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SourceStdCacheProfile {
    pub hits: usize,
    pub misses: usize,
    pub disabled: usize,
    pub clone: Duration,
    pub build: Duration,
}

pub struct ProfiledLoweredSources {
    pub lowered: LoweredSources,
    pub profile: SourceLowerProfile,
}

#[derive(Default)]
pub struct SourceLowerCache {
    std_snapshots: HashMap<StdSourceCacheKey, StdInferSnapshot>,
}

#[derive(Clone)]
pub struct StdInferSnapshot {
    key: StdSourceCacheKey,
    state: LowerState,
    data: StdInferSnapshotData,
}

pub const STD_INFER_SNAPSHOT_FORMAT_VERSION: u32 = 4;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StdInferSnapshotManifest {
    pub format_version: u32,
    pub key: StdSourceCacheKey,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StdInferSnapshotData {
    pub manifest: StdInferSnapshotManifest,
    pub modules: Vec<StdInferSnapshotModule>,
    pub values: Vec<StdInferSnapshotSymbol>,
    pub types: Vec<StdInferSnapshotSymbol>,
    pub schemes: Vec<StdInferSnapshotScheme>,
    pub roles: Vec<StdInferSnapshotRole>,
    pub role_methods: Vec<StdInferSnapshotRoleMethod>,
    pub role_impls: Vec<StdInferSnapshotRoleImpl>,
    pub effects: Vec<StdInferSnapshotEffect>,
    pub effect_methods: Vec<StdInferSnapshotEffectMethod>,
    pub effect_operations: Vec<StdInferSnapshotEffectOperation>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StdCoreSnapshotData {
    pub manifest: StdInferSnapshotManifest,
    pub program: CoreProgram,
}

pub struct StdInferSnapshotImport {
    pub state: LowerState,
    pub modules: Vec<Option<ModuleId>>,
    pub values: Vec<Option<crate::ids::DefId>>,
    pub types: Vec<Option<crate::ids::DefId>>,
    pub refs: StdInferSnapshotImportRefs,
    pub missing: StdInferSnapshotImportMissing,
    pub coverage: StdInferSnapshotImportCoverage,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct StdInferSnapshotImportRefs {
    pub schemes: Vec<Option<crate::ids::DefId>>,
    pub role_methods: Vec<Option<crate::ids::DefId>>,
    pub role_impl_members: Vec<Vec<Option<crate::ids::DefId>>>,
    pub effect_methods: Vec<Option<crate::ids::DefId>>,
    pub effect_method_modules: Vec<Option<ModuleId>>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct StdInferSnapshotImportCoverage {
    pub modules_total: usize,
    pub modules_resolved: usize,
    pub values_total: usize,
    pub values_resolved: usize,
    pub types_total: usize,
    pub types_resolved: usize,
    pub schemes_total: usize,
    pub schemes_resolved: usize,
    pub role_methods_total: usize,
    pub role_methods_resolved: usize,
    pub effect_methods_total: usize,
    pub effect_methods_resolved: usize,
}

impl StdInferSnapshotImportCoverage {
    pub fn can_replace_std_lowering(&self) -> bool {
        self.modules_total == self.modules_resolved
            && self.values_total == self.values_resolved
            && self.types_total == self.types_resolved
            && self.schemes_total == self.schemes_resolved
            && self.role_methods_total == self.role_methods_resolved
            && self.effect_methods_total == self.effect_methods_resolved
    }

    pub fn has_partial_value_or_type_import(&self) -> bool {
        self.values_resolved < self.values_total || self.types_resolved < self.types_total
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct StdInferSnapshotImportMissing {
    pub modules: Vec<StdInferSnapshotMissingPath>,
    pub values: Vec<StdInferSnapshotMissingPath>,
    pub types: Vec<StdInferSnapshotMissingPath>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StdInferSnapshotMissingPath {
    pub snapshot_id: u32,
    pub path: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StdInferSnapshotImportError {
    InvalidData(StdInferSnapshotDataError),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StdInferSnapshotModule {
    pub path: Vec<String>,
    pub snapshot_id: u32,
    pub parent: Option<u32>,
    pub values: Vec<StdInferSnapshotModuleValue>,
    pub operators: Vec<StdInferSnapshotModuleOperator>,
    pub types: Vec<StdInferSnapshotModuleType>,
    pub modules: Vec<StdInferSnapshotModuleChild>,
    pub reexports: Vec<StdInferSnapshotReexport>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StdInferSnapshotModuleValue {
    pub name: String,
    pub symbol: u32,
    pub visibility: StdInferSnapshotVisibility,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StdInferSnapshotModuleOperator {
    pub name: String,
    pub fixity: StdInferSnapshotOperatorFixity,
    pub symbol: u32,
    pub visibility: StdInferSnapshotVisibility,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StdInferSnapshotModuleType {
    pub name: String,
    pub symbol: u32,
    pub visibility: StdInferSnapshotVisibility,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StdInferSnapshotModuleChild {
    pub name: String,
    pub module: u32,
    pub visibility: StdInferSnapshotVisibility,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StdInferSnapshotReexport {
    pub name: String,
    pub path: Vec<String>,
    pub namespace: StdInferSnapshotNamespace,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum StdInferSnapshotNamespace {
    Value,
    Type,
    Module,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum StdInferSnapshotVisibility {
    My,
    Our,
    Pub,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum StdInferSnapshotOperatorFixity {
    Prefix,
    Infix,
    Suffix,
    Nullfix,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StdInferSnapshotSymbol {
    pub path: Vec<String>,
    pub snapshot_id: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StdInferSnapshotScheme {
    pub symbol: u32,
    pub rendered: String,
    pub compact: Option<CompactTypeScheme>,
    #[serde(default)]
    pub role_constraints: Vec<CompactRoleConstraint>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StdInferSnapshotRole {
    pub path: Vec<String>,
    pub args: Vec<StdInferSnapshotRoleArg>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StdInferSnapshotRoleArg {
    pub name: String,
    pub is_input: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StdInferSnapshotRoleMethod {
    pub role: Vec<String>,
    pub name: String,
    pub symbol: u32,
    #[serde(default)]
    pub input_names: Vec<Option<String>>,
    #[serde(default)]
    pub output_name: Option<String>,
    pub has_receiver: bool,
    pub has_default_body: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StdInferSnapshotRoleImpl {
    pub role: Vec<String>,
    pub args: Vec<String>,
    pub compact_args: Vec<CompactType>,
    pub prerequisites: Vec<crate::simplify::cooccur::CompactRoleConstraint>,
    pub members: Vec<StdInferSnapshotRoleImplMember>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StdInferSnapshotRoleImplMember {
    pub name: String,
    pub symbol: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StdInferSnapshotEffect {
    pub path: Vec<String>,
    pub arity: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StdInferSnapshotEffectMethod {
    pub name: String,
    pub effect: Vec<String>,
    pub symbol: u32,
    pub module: u32,
    pub module_path: Vec<String>,
    pub visibility: StdInferSnapshotVisibility,
    pub receiver_expects_computation: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StdInferSnapshotEffectOperation {
    pub snapshot_id: u32,
    pub effect_path: Vec<String>,
}

pub fn lower_entry_with_options(
    entry: impl AsRef<FsPath>,
    options: SourceOptions,
) -> Result<LoweredSources, SourceLoadError> {
    let source_set = collect_source_files_with_options(entry, options)?;
    Ok(lower_source_set(&source_set))
}

pub fn lower_entry_with_options_profiled(
    entry: impl AsRef<FsPath>,
    options: SourceOptions,
) -> Result<ProfiledLoweredSources, SourceLoadError> {
    with_profile_enabled(true, || {
        let collect_start = ProfileClock::now();
        let source_set = collect_source_files_with_options(entry, options)?;
        let collect = collect_start.elapsed();
        let mut lowered = lower_source_set_profiled(&source_set);
        lowered.profile.collect = collect;
        Ok(lowered)
    })
}

pub fn lower_virtual_source_with_options(
    source: &str,
    base_dir: Option<PathBuf>,
    options: SourceOptions,
) -> Result<LoweredSources, SourceLoadError> {
    let source_set = collect_virtual_source_files_with_options(source, base_dir, options)?;
    Ok(lower_source_set(&source_set))
}

pub fn lower_virtual_module_source_with_options(
    source: &str,
    base_dir: Option<PathBuf>,
    module_path: Path,
    options: SourceOptions,
) -> Result<LoweredSources, SourceLoadError> {
    let module_path = typed_ir::Path {
        segments: module_path
            .segments
            .into_iter()
            .map(|name| typed_ir::Name(name.0))
            .collect(),
    };
    let source_set =
        collect_virtual_module_source_files_with_options(source, base_dir, module_path, options)?;
    Ok(lower_source_set(&source_set))
}

pub fn lower_virtual_source_with_options_profiled(
    source: &str,
    base_dir: Option<PathBuf>,
    options: SourceOptions,
) -> Result<ProfiledLoweredSources, SourceLoadError> {
    with_profile_enabled(true, || {
        let collect_start = ProfileClock::now();
        let source_set = collect_virtual_source_files_with_options(source, base_dir, options)?;
        let collect = collect_start.elapsed();
        let mut lowered = lower_source_set_profiled(&source_set);
        lowered.profile.collect = collect;
        Ok(lowered)
    })
}

pub fn lower_source_set(source_set: &SourceSet) -> LoweredSources {
    lower_source_set_with_profile(source_set, false).lowered
}

pub fn lower_source_set_with_std_cache(
    source_set: &SourceSet,
    cache: &mut SourceLowerCache,
) -> LoweredSources {
    lower_source_set_with_std_cache_profiled(source_set, cache).lowered
}

pub fn lower_source_set_with_std_cache_profiled(
    source_set: &SourceSet,
    cache: &mut SourceLowerCache,
) -> ProfiledLoweredSources {
    with_profile_enabled(true, || lower_source_set_cached_inner(source_set, cache))
}

pub fn warm_std_source_cache(
    source_set: &SourceSet,
    cache: &mut SourceLowerCache,
) -> SourceStdCacheProfile {
    with_profile_enabled(true, || {
        let mut profile = SourceLowerProfile::default();
        if source_set.std_files().next().is_none() {
            profile.std_cache.disabled += 1;
        } else {
            let _ = cache.std_state(source_set, &mut profile);
        }
        profile.std_cache
    })
}

pub fn build_std_infer_snapshot(source_set: &SourceSet) -> Option<StdInferSnapshot> {
    with_profile_enabled(false, || build_std_infer_snapshot_inner(source_set, None))
}

pub fn build_std_infer_snapshot_data(source_set: &SourceSet) -> Option<StdInferSnapshotData> {
    with_profile_enabled(false, || build_std_infer_snapshot_data_inner(source_set))
}

pub fn build_std_core_snapshot_data(source_set: &SourceSet) -> Option<StdCoreSnapshotData> {
    with_profile_enabled(false, || build_std_core_snapshot_data_inner(source_set))
}

pub fn build_compiled_namespace_artifacts(
    source_set: &SourceSet,
    state: &LowerState,
) -> Vec<CompiledUnitNamespaceArtifact> {
    let syntax_artifacts = source_set.compiled_unit_syntax_artifacts();
    let units = source_set.compilation_units();
    let value_paths = state.ctx.collect_all_binding_paths();
    let type_paths = state.ctx.collect_all_type_paths();

    units
        .units
        .iter()
        .enumerate()
        .map(|(unit_idx, unit)| {
            let module_paths = unit
                .files
                .iter()
                .map(|&file_idx| source_set.files[file_idx].module_path.clone())
                .collect::<Vec<_>>();
            let namespace = compiled_namespace_surface_for_modules(
                state,
                &module_paths,
                &value_paths,
                &type_paths,
            );
            CompiledUnitNamespaceArtifact {
                manifest: syntax_artifacts[unit_idx].manifest.clone(),
                namespace,
            }
        })
        .collect()
}

pub fn import_compiled_namespace_surface(
    surface: &CompiledNamespaceSurface,
) -> Result<CompiledNamespaceImport, CompiledNamespaceImportError> {
    let validation = surface.validate();
    if !validation.is_complete() {
        return Err(CompiledNamespaceImportError::InvalidNamespace(validation));
    }

    let mut state = LowerState::new();
    install_builtin_primitives(&mut state);
    import_compiled_namespace_module_skeletons(&mut state, &surface.modules);
    let modules = import_compiled_namespace_module_map(&state, &surface.modules);
    let values = import_compiled_namespace_values(&mut state, surface, &modules);
    let types = import_compiled_namespace_types(&mut state, surface, &modules);
    import_compiled_namespace_module_entries(&mut state, surface, &modules, &values, &types);

    Ok(CompiledNamespaceImport {
        state,
        values,
        types,
        validation,
    })
}

pub fn import_trusted_compiled_namespace_surface(
    surface: &CompiledNamespaceSurface,
) -> CompiledNamespaceImport {
    let mut state = LowerState::new();
    install_builtin_primitives(&mut state);
    import_compiled_namespace_module_skeletons(&mut state, &surface.modules);
    let modules = import_compiled_namespace_module_map(&state, &surface.modules);
    let values = import_compiled_namespace_values(&mut state, surface, &modules);
    let types = import_compiled_namespace_types(&mut state, surface, &modules);
    import_compiled_namespace_module_entries(&mut state, surface, &modules, &values, &types);

    CompiledNamespaceImport {
        state,
        values,
        types,
        validation: trusted_compiled_namespace_validation(surface),
    }
}

fn import_trusted_compiled_namespace_surface_profiled(
    surface: &CompiledNamespaceSurface,
    mut profile: Option<&mut CompiledUnitImportProfile>,
) -> CompiledNamespaceImport {
    let start = Instant::now();
    let mut state = LowerState::new();
    install_builtin_primitives(&mut state);
    if let Some(profile) = profile.as_deref_mut() {
        profile.namespace_builtin += start.elapsed();
    }
    let start = Instant::now();
    import_compiled_namespace_module_skeletons(&mut state, &surface.modules);
    if let Some(profile) = profile.as_deref_mut() {
        profile.namespace_skeletons += start.elapsed();
    }
    let start = Instant::now();
    let modules = import_compiled_namespace_module_map(&state, &surface.modules);
    if let Some(profile) = profile.as_deref_mut() {
        profile.namespace_module_map += start.elapsed();
    }
    let start = Instant::now();
    let values = import_compiled_namespace_values(&mut state, surface, &modules);
    if let Some(profile) = profile.as_deref_mut() {
        profile.namespace_values += start.elapsed();
    }
    let start = Instant::now();
    let types = import_compiled_namespace_types(&mut state, surface, &modules);
    if let Some(profile) = profile.as_deref_mut() {
        profile.namespace_types += start.elapsed();
    }
    let start = Instant::now();
    import_compiled_namespace_module_entries(&mut state, surface, &modules, &values, &types);
    if let Some(profile) = profile.as_deref_mut() {
        profile.namespace_entries += start.elapsed();
    }

    let start = Instant::now();
    let validation = trusted_compiled_namespace_validation(surface);
    if let Some(profile) = profile.as_deref_mut() {
        profile.namespace_validation += start.elapsed();
    }
    CompiledNamespaceImport {
        state,
        values,
        types,
        validation,
    }
}

pub fn import_compiled_typed_artifact(
    artifact: &CompiledUnitTypedArtifact,
) -> Result<CompiledTypedImport, CompiledTypedImportError> {
    import_compiled_typed_surface(&artifact.namespace, &artifact.typed)
}

pub fn import_compiled_unit_artifact(
    artifact: &CompiledUnitArtifact,
) -> Result<CompiledUnitImport, CompiledUnitImportError> {
    let typed = import_compiled_typed_surface(&artifact.namespace, &artifact.typed)
        .map_err(CompiledUnitImportError::InvalidTyped)?;
    Ok(CompiledUnitImport {
        syntax: artifact.syntax.clone(),
        typed,
        runtime: artifact.runtime.clone(),
    })
}

pub fn import_compiled_unit_artifacts(
    artifacts: &[CompiledUnitArtifact],
) -> Result<CompiledUnitArtifactsImport, CompiledUnitArtifactsImportError> {
    let bundle = build_compiled_unit_artifact_bundle(artifacts)
        .map_err(CompiledUnitArtifactsImportError::InvalidRuntime)?;
    import_compiled_unit_artifact_bundle(&bundle)
}

pub fn import_compiled_unit_artifact_bundle(
    bundle: &CompiledUnitArtifactBundle,
) -> Result<CompiledUnitArtifactsImport, CompiledUnitArtifactsImportError> {
    let typed = import_compiled_typed_surface(&bundle.namespace, &bundle.typed)
        .map_err(CompiledUnitArtifactsImportError::InvalidTyped)?;

    Ok(CompiledUnitArtifactsImport {
        manifests: bundle.manifests.clone(),
        typed,
        runtime: bundle.runtime.clone(),
    })
}

pub fn import_trusted_compiled_unit_artifact_bundle(
    bundle: &CompiledUnitArtifactBundle,
) -> CompiledUnitArtifactsImport {
    let typed = import_trusted_compiled_typed_surface(&bundle.namespace, &bundle.typed);
    CompiledUnitArtifactsImport {
        manifests: bundle.manifests.clone(),
        typed,
        runtime: bundle.runtime.clone(),
    }
}

pub fn import_trusted_compiled_unit_artifact_bundle_profiled(
    bundle: &CompiledUnitArtifactBundle,
) -> (CompiledUnitArtifactsImport, CompiledUnitImportProfile) {
    let mut profile = CompiledUnitImportProfile::default();
    let typed = import_trusted_compiled_typed_surface_profiled(
        &bundle.namespace,
        &bundle.typed,
        Some(&mut profile),
    );
    let start = Instant::now();
    let manifests = bundle.manifests.clone();
    profile.manifests_clone += start.elapsed();
    let start = Instant::now();
    let runtime = bundle.runtime.clone();
    profile.runtime_clone += start.elapsed();
    (
        CompiledUnitArtifactsImport {
            manifests,
            typed,
            runtime,
        },
        profile,
    )
}

pub fn import_trusted_compiled_unit_semantic_artifact_bundle_profiled(
    bundle: &CompiledUnitSemanticArtifactBundle,
) -> (CompiledUnitSemanticImport, CompiledUnitImportProfile) {
    let mut profile = CompiledUnitImportProfile::default();
    let typed = import_trusted_compiled_typed_surface_profiled(
        &bundle.namespace,
        &bundle.typed,
        Some(&mut profile),
    );
    let start = Instant::now();
    let manifests = bundle.manifests.clone();
    profile.manifests_clone += start.elapsed();
    (CompiledUnitSemanticImport { manifests, typed }, profile)
}

pub fn build_compiled_unit_artifact_bundle(
    artifacts: &[CompiledUnitArtifact],
) -> Result<CompiledUnitArtifactBundle, CompiledRuntimeMergeError> {
    let namespace =
        merge_compiled_namespace_surfaces(artifacts.iter().map(|artifact| &artifact.namespace));
    let typed = merge_compiled_typed_surfaces(artifacts);
    let runtime =
        CompiledRuntimeBundle::from_surfaces(artifacts.iter().map(|artifact| &artifact.runtime))?;

    Ok(CompiledUnitArtifactBundle {
        manifests: artifacts
            .iter()
            .map(|artifact| artifact.manifest.clone())
            .collect(),
        namespace,
        typed,
        runtime,
    })
}

pub fn build_compiled_unit_semantic_artifact_bundle(
    artifacts: &[CompiledUnitArtifact],
) -> CompiledUnitSemanticArtifactBundle {
    CompiledUnitSemanticArtifactBundle {
        manifests: artifacts
            .iter()
            .map(|artifact| artifact.manifest.clone())
            .collect(),
        namespace: merge_compiled_namespace_surfaces(
            artifacts.iter().map(|artifact| &artifact.namespace),
        ),
        typed: merge_compiled_typed_surfaces(artifacts),
    }
}

impl From<&CompiledUnitArtifactBundle> for CompiledUnitSemanticArtifactBundle {
    fn from(bundle: &CompiledUnitArtifactBundle) -> Self {
        Self {
            manifests: bundle.manifests.clone(),
            namespace: bundle.namespace.clone(),
            typed: bundle.typed.clone(),
        }
    }
}

pub fn import_compiled_typed_surface(
    namespace: &CompiledNamespaceSurface,
    typed: &CompiledTypedSurface,
) -> Result<CompiledTypedImport, CompiledTypedImportError> {
    reserve_compiled_typed_type_vars(typed);
    let namespace_validation = namespace.validate();
    if !namespace_validation.is_complete() {
        return Err(CompiledTypedImportError::InvalidNamespace(
            namespace_validation,
        ));
    }

    let typed_validation = typed.validate(namespace);
    if !typed_validation.is_complete() {
        return Err(CompiledTypedImportError::InvalidTyped(typed_validation));
    }

    let mut namespace_import = import_compiled_namespace_surface(namespace).map_err(
        |CompiledNamespaceImportError::InvalidNamespace(validation)| {
            CompiledTypedImportError::InvalidNamespace(validation)
        },
    )?;
    let refs = import_compiled_typed_refs(typed, &namespace_import.values);
    import_compiled_compact_schemes(typed, &refs, &namespace_import.state);
    import_compiled_typed_lookup_tables(typed, &refs, &mut namespace_import.state);
    let coverage = import_compiled_typed_coverage(&namespace_import, &refs);

    Ok(CompiledTypedImport {
        namespace: namespace_import,
        refs,
        coverage,
        validation: typed_validation,
    })
}

pub fn import_trusted_compiled_typed_surface(
    namespace: &CompiledNamespaceSurface,
    typed: &CompiledTypedSurface,
) -> CompiledTypedImport {
    reserve_compiled_typed_type_vars(typed);
    let mut namespace_import = import_trusted_compiled_namespace_surface(namespace);
    let refs = import_compiled_typed_refs(typed, &namespace_import.values);
    import_compiled_compact_schemes(typed, &refs, &namespace_import.state);
    import_compiled_typed_lookup_tables(typed, &refs, &mut namespace_import.state);
    let coverage = import_compiled_typed_coverage(&namespace_import, &refs);

    CompiledTypedImport {
        namespace: namespace_import,
        refs,
        coverage,
        validation: trusted_compiled_typed_validation(typed),
    }
}

fn import_trusted_compiled_typed_surface_profiled(
    namespace: &CompiledNamespaceSurface,
    typed: &CompiledTypedSurface,
    mut profile: Option<&mut CompiledUnitImportProfile>,
) -> CompiledTypedImport {
    let start = Instant::now();
    reserve_compiled_typed_type_vars(typed);
    if let Some(profile) = profile.as_deref_mut() {
        profile.reserve_type_vars += start.elapsed();
    }
    let mut namespace_import =
        import_trusted_compiled_namespace_surface_profiled(namespace, profile.as_deref_mut());
    let start = Instant::now();
    let refs = import_compiled_typed_refs(typed, &namespace_import.values);
    if let Some(profile) = profile.as_deref_mut() {
        profile.typed_refs += start.elapsed();
    }
    let start = Instant::now();
    import_compiled_compact_schemes(typed, &refs, &namespace_import.state);
    if let Some(profile) = profile.as_deref_mut() {
        profile.compact_schemes += start.elapsed();
    }
    let start = Instant::now();
    import_compiled_typed_lookup_tables(typed, &refs, &mut namespace_import.state);
    if let Some(profile) = profile.as_deref_mut() {
        profile.lookup_tables += start.elapsed();
    }
    let start = Instant::now();
    let coverage = import_compiled_typed_coverage(&namespace_import, &refs);
    if let Some(profile) = profile.as_deref_mut() {
        profile.typed_coverage += start.elapsed();
    }
    let start = Instant::now();
    let validation = trusted_compiled_typed_validation(typed);
    if let Some(profile) = profile.as_deref_mut() {
        profile.typed_validation += start.elapsed();
    }

    CompiledTypedImport {
        namespace: namespace_import,
        refs,
        coverage,
        validation,
    }
}

pub fn lower_source_set_with_compiled_unit_artifacts_profiled(
    source_set: &SourceSet,
    artifacts: &[CompiledUnitArtifact],
) -> Result<CompiledUnitProfiledLoweredSources, CompiledUnitArtifactsImportError> {
    let import = import_compiled_unit_artifacts(artifacts)?;
    Ok(lower_source_set_with_compiled_unit_import(
        source_set,
        import,
        HashSet::new(),
    ))
}

pub fn lower_source_set_with_compiled_unit_artifact_bundle_profiled(
    source_set: &SourceSet,
    bundle: &CompiledUnitArtifactBundle,
) -> Result<CompiledUnitProfiledLoweredSources, CompiledUnitArtifactsImportError> {
    let import = import_compiled_unit_artifact_bundle(bundle)?;
    Ok(lower_source_set_with_compiled_unit_import(
        source_set,
        import,
        HashSet::new(),
    ))
}

pub fn lower_source_set_with_trusted_compiled_unit_artifact_bundle_profiled(
    source_set: &SourceSet,
    bundle: &CompiledUnitArtifactBundle,
) -> CompiledUnitProfiledLoweredSources {
    let import = import_trusted_compiled_unit_artifact_bundle(bundle);
    lower_source_set_with_compiled_unit_import(source_set, import, HashSet::new())
}

pub fn lower_source_set_with_trusted_compiled_unit_artifact_bundle_profiled_with_import_profile(
    source_set: &SourceSet,
    bundle: &CompiledUnitArtifactBundle,
) -> (
    CompiledUnitProfiledLoweredSources,
    CompiledUnitImportProfile,
) {
    let (import, mut profile) = import_trusted_compiled_unit_artifact_bundle_profiled(bundle);
    let start = Instant::now();
    let lowered = lower_source_set_with_compiled_unit_import(source_set, import, HashSet::new());
    profile.cached_state_lower += start.elapsed();
    (lowered, profile)
}

pub fn lower_source_set_with_trusted_compiled_unit_semantic_artifact_bundle_profiled(
    source_set: &SourceSet,
    bundle: &CompiledUnitSemanticArtifactBundle,
) -> ProfiledLoweredSources {
    let (import, _) = import_trusted_compiled_unit_semantic_artifact_bundle_profiled(bundle);
    lower_source_set_with_compiled_unit_semantic_import(source_set, import, HashSet::new())
}

pub fn lower_source_set_with_trusted_compiled_unit_semantic_artifact_bundle_profiled_with_import_profile(
    source_set: &SourceSet,
    bundle: &CompiledUnitSemanticArtifactBundle,
) -> (ProfiledLoweredSources, CompiledUnitImportProfile) {
    let (import, mut profile) =
        import_trusted_compiled_unit_semantic_artifact_bundle_profiled(bundle);
    let start = Instant::now();
    let lowered =
        lower_source_set_with_compiled_unit_semantic_import(source_set, import, HashSet::new());
    profile.cached_state_lower += start.elapsed();
    (lowered, profile)
}

/// Lowers a source set on top of trusted compiled artifacts while forcing
/// selected files to act as cache hits.
///
/// This keeps source-only metadata such as synthetic act templates available
/// without re-lowering files whose typed/runtime surfaces came from the bundle.
pub fn lower_source_set_with_trusted_compiled_unit_artifact_bundle_and_cached_files_profiled(
    source_set: &SourceSet,
    bundle: &CompiledUnitArtifactBundle,
    cached_files: impl IntoIterator<Item = usize>,
) -> CompiledUnitProfiledLoweredSources {
    let import = import_trusted_compiled_unit_artifact_bundle(bundle);
    lower_source_set_with_compiled_unit_import(source_set, import, cached_files)
}

fn lower_source_set_with_compiled_unit_import(
    source_set: &SourceSet,
    import: CompiledUnitArtifactsImport,
    extra_cached_files: impl IntoIterator<Item = usize>,
) -> CompiledUnitProfiledLoweredSources {
    let mut profile = source_set_profile_header(source_set);
    profile.std_cache.hits += 1;
    let mut cached_files = cached_source_file_indices(source_set, &import.manifests);
    cached_files.extend(extra_cached_files);
    let lowered = lower_source_set_from_cached_state(
        source_set,
        import.typed.namespace.state,
        profile,
        &cached_files,
    );
    CompiledUnitProfiledLoweredSources {
        lowered,
        runtime: import.runtime,
    }
}

fn lower_source_set_with_compiled_unit_semantic_import(
    source_set: &SourceSet,
    import: CompiledUnitSemanticImport,
    extra_cached_files: impl IntoIterator<Item = usize>,
) -> ProfiledLoweredSources {
    let mut profile = source_set_profile_header(source_set);
    profile.std_cache.hits += 1;
    let mut cached_files = cached_source_file_indices(source_set, &import.manifests);
    cached_files.extend(extra_cached_files);
    lower_source_set_from_cached_state(
        source_set,
        import.typed.namespace.state,
        profile,
        &cached_files,
    )
}

fn cached_source_file_indices(
    source_set: &SourceSet,
    manifests: &[CompiledUnitManifest],
) -> HashSet<usize> {
    if manifests.is_empty() {
        return HashSet::new();
    }
    let units = source_set.compilation_units();
    let syntax_artifacts = units.syntax_artifacts(source_set);
    units
        .units
        .iter()
        .zip(syntax_artifacts)
        .filter(|(_, artifact)| {
            manifests
                .iter()
                .any(|manifest| manifest == &artifact.manifest)
        })
        .flat_map(|(unit, _)| unit.files.iter().copied())
        .collect()
}

fn import_compiled_compact_schemes(
    typed: &CompiledTypedSurface,
    refs: &CompiledTypedImportRefs,
    state: &LowerState,
) {
    for (scheme, def) in typed.schemes.iter().zip(&refs.schemes) {
        if let (Some(compact), Some(def)) = (&scheme.compact, def) {
            state.infer.store_compact_scheme(*def, compact.clone());
            state
                .infer
                .store_compact_role_constraints(*def, scheme.role_constraints.clone());
        }
    }
}

fn import_std_snapshot_compact_schemes(
    data: &StdInferSnapshotData,
    refs: &StdInferSnapshotImportRefs,
    state: &LowerState,
) {
    for (scheme, def) in data.schemes.iter().zip(&refs.schemes) {
        if let (Some(compact), Some(def)) = (&scheme.compact, def) {
            state.infer.store_compact_scheme(*def, compact.clone());
            state
                .infer
                .store_compact_role_constraints(*def, scheme.role_constraints.clone());
        }
    }
}

fn reserve_compiled_typed_type_vars(typed: &CompiledTypedSurface) {
    if let Some(max) = max_compiled_typed_type_var(typed) {
        crate::ids::reserve_type_vars_through(max);
    }
}

fn reserve_std_infer_snapshot_type_vars(data: &StdInferSnapshotData) {
    if let Some(max) = max_std_infer_snapshot_type_var(data) {
        crate::ids::reserve_type_vars_through(max);
    }
}

fn max_std_infer_snapshot_type_var(data: &StdInferSnapshotData) -> Option<TypeVar> {
    let mut max = None;
    for scheme in &data.schemes {
        collect_snapshot_scheme_max_type_var(scheme, &mut max);
    }
    for role_impl in &data.role_impls {
        for arg in &role_impl.compact_args {
            collect_compact_type_max_type_var(arg, &mut max);
        }
        for prerequisite in &role_impl.prerequisites {
            for arg in &prerequisite.args {
                collect_compact_bounds_max_type_var(arg, &mut max);
            }
        }
    }
    max
}

fn max_compiled_typed_type_var(typed: &CompiledTypedSurface) -> Option<TypeVar> {
    let mut max = None;
    for scheme in &typed.schemes {
        collect_snapshot_scheme_max_type_var(scheme, &mut max);
    }
    for role_impl in &typed.role_impls {
        for arg in &role_impl.compact_args {
            collect_compact_type_max_type_var(arg, &mut max);
        }
        for prerequisite in &role_impl.prerequisites {
            for arg in &prerequisite.args {
                collect_compact_bounds_max_type_var(arg, &mut max);
            }
        }
    }
    max
}

fn collect_snapshot_scheme_max_type_var(
    scheme: &StdInferSnapshotScheme,
    max: &mut Option<TypeVar>,
) {
    if let Some(compact) = &scheme.compact {
        collect_compact_scheme_max_type_var(compact, max);
    }
    for constraint in &scheme.role_constraints {
        for arg in &constraint.args {
            collect_compact_bounds_max_type_var(arg, max);
        }
    }
}

fn collect_compact_scheme_max_type_var(scheme: &CompactTypeScheme, max: &mut Option<TypeVar>) {
    collect_compact_bounds_max_type_var(&scheme.cty, max);
    for (var, bounds) in &scheme.rec_vars {
        push_max_type_var(*var, max);
        collect_compact_bounds_max_type_var(bounds, max);
    }
}

fn collect_compact_bounds_max_type_var(bounds: &CompactBounds, max: &mut Option<TypeVar>) {
    if let Some(var) = bounds.self_var {
        push_max_type_var(var, max);
    }
    collect_compact_type_max_type_var(&bounds.lower, max);
    collect_compact_type_max_type_var(&bounds.upper, max);
}

fn collect_compact_type_max_type_var(ty: &CompactType, max: &mut Option<TypeVar>) {
    for var in &ty.vars {
        push_max_type_var(*var, max);
    }
    for con in &ty.cons {
        for arg in &con.args {
            collect_compact_bounds_max_type_var(arg, max);
        }
    }
    for fun in &ty.funs {
        collect_compact_type_max_type_var(&fun.arg, max);
        collect_compact_type_max_type_var(&fun.arg_eff, max);
        collect_compact_type_max_type_var(&fun.ret_eff, max);
        collect_compact_type_max_type_var(&fun.ret, max);
    }
    for record in &ty.records {
        for field in &record.fields {
            collect_compact_type_max_type_var(&field.value, max);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            collect_compact_type_max_type_var(&field.value, max);
        }
        collect_compact_type_max_type_var(&spread.tail, max);
    }
    for variant in &ty.variants {
        for (_, payload) in &variant.items {
            for item in payload {
                collect_compact_type_max_type_var(item, max);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in tuple {
            collect_compact_type_max_type_var(item, max);
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            collect_compact_type_max_type_var(item, max);
        }
        collect_compact_type_max_type_var(&row.tail, max);
    }
}

fn push_max_type_var(var: TypeVar, max: &mut Option<TypeVar>) {
    if max.is_none_or(|current| var.0 > current.0) {
        *max = Some(var);
    }
}

fn import_compiled_typed_lookup_tables(
    typed: &CompiledTypedSurface,
    refs: &CompiledTypedImportRefs,
    state: &mut LowerState,
) {
    for role in &typed.roles {
        state.infer.register_role_arg_infos(
            path_from_snapshot_segments(&role.path),
            role.args
                .iter()
                .map(|arg| crate::solve::RoleArgInfo {
                    name: arg.name.clone(),
                    is_input: arg.is_input,
                })
                .collect(),
        );
    }

    for (method, def) in typed.role_methods.iter().zip(&refs.role_methods) {
        let Some(def) = def else {
            continue;
        };
        let info = crate::solve::RoleMethodInfo {
            name: Name(method.name.clone()),
            def: *def,
            role: path_from_snapshot_segments(&method.role),
            args: Vec::new(),
            sig: None,
            input_names: method.input_names.clone(),
            output_name: method.output_name.clone(),
            has_receiver: method.has_receiver,
            has_default_body: method.has_default_body,
        };
        state
            .infer
            .register_role_method(Name(method.name.clone()), info);
    }

    for (role_impl, member_defs) in typed.role_impls.iter().zip(&refs.role_impl_members) {
        let member_defs = role_impl
            .members
            .iter()
            .zip(member_defs)
            .filter_map(|(member, def)| Some((Name(member.name.clone()), (*def)?)))
            .collect::<HashMap<_, _>>();
        if member_defs.is_empty() {
            continue;
        }
        state
            .infer
            .register_role_impl_candidate(crate::solve::RoleImplCandidate {
                role: path_from_snapshot_segments(&role_impl.role),
                args: role_impl.args.clone(),
                compact_args: role_impl.compact_args.clone(),
                prerequisites: role_impl.prerequisites.clone(),
                member_defs,
            });
    }

    for effect in &typed.effects {
        state
            .effect_arities
            .insert(path_from_snapshot_segments(&effect.path), effect.arity);
    }

    for (method, def) in typed.effect_methods.iter().zip(&refs.effect_methods) {
        let Some(def) = def else {
            continue;
        };
        let effect = path_from_snapshot_segments(&method.effect);
        let def = compiled_effect_method_runtime_def(state, method, *def, &effect);
        let module = state
            .ctx
            .resolve_module_path(&path_from_snapshot_segments(&method.module_path))
            .unwrap_or(state.ctx.current_module);
        state
            .infer
            .register_effect_method(crate::solve::EffectMethodInfo {
                name: Name(method.name.clone()),
                effect,
                def,
                module,
                visibility: import_snapshot_visibility(method.visibility),
                receiver_expects_computation: method.receiver_expects_computation,
            });
    }

    state.mark_selection_lookup_dirty();
}

fn compiled_effect_method_runtime_def(
    state: &LowerState,
    method: &StdInferSnapshotEffectMethod,
    method_def: crate::ids::DefId,
    effect: &Path,
) -> crate::ids::DefId {
    if !method.receiver_expects_computation {
        return method_def;
    }
    // Cached imports do not yet restore source helper bodies into LowerState.
    // When std exposes both `(x: [_] _).m` and a direct `effect::m`, use the
    // direct runtime handler target so downstream export can keep the
    // computation receiver effect attached without re-lowering the helper.
    let mut direct_path = effect.clone();
    direct_path.segments.push(Name(method.name.clone()));
    state
        .ctx
        .resolve_path_value(&direct_path)
        .unwrap_or(method_def)
}

pub fn build_compiled_unit_artifacts(
    source_set: &SourceSet,
    state: &LowerState,
) -> Vec<CompiledUnitArtifact> {
    let syntax_artifacts = source_set.compiled_unit_syntax_artifacts();
    let typed_artifacts = build_compiled_typed_artifacts(source_set, state);
    let runtime_surfaces = build_compiled_runtime_surfaces(state, &typed_artifacts);

    assert_eq!(
        syntax_artifacts.len(),
        typed_artifacts.len(),
        "syntax and typed artifact builders must use the same compilation units"
    );
    assert_eq!(
        typed_artifacts.len(),
        runtime_surfaces.len(),
        "typed and runtime artifact builders must use the same compilation units"
    );

    syntax_artifacts
        .into_iter()
        .zip(typed_artifacts)
        .zip(runtime_surfaces)
        .map(|((syntax_artifact, typed_artifact), runtime)| {
            debug_assert_eq!(syntax_artifact.manifest, typed_artifact.manifest);
            CompiledUnitArtifact {
                manifest: syntax_artifact.manifest,
                syntax: syntax_artifact.syntax,
                namespace: typed_artifact.namespace,
                typed: typed_artifact.typed,
                runtime,
            }
        })
        .collect()
}

pub fn build_compiled_typed_artifacts(
    source_set: &SourceSet,
    state: &LowerState,
) -> Vec<CompiledUnitTypedArtifact> {
    let mut finalized_state = state.clone();
    finalized_state.finalize_compact_results();
    let state = &finalized_state;
    let namespace_artifacts = build_compiled_namespace_artifacts(source_set, state);
    let value_paths = state.ctx.collect_all_binding_paths();
    let value_defs_by_path = value_paths
        .iter()
        .map(|(path, def)| (snapshot_path_segments(path), *def))
        .collect::<HashMap<_, _>>();
    let all_value_ids = value_paths
        .iter()
        .enumerate()
        .map(|(index, (_, def))| (*def, index as u32))
        .collect::<HashMap<_, _>>();
    let all_schemes = collect_std_snapshot_schemes(state, &all_value_ids);
    let all_role_methods = collect_std_snapshot_role_methods(state, &all_value_ids);
    let all_role_impls = collect_std_snapshot_role_impls(state, &all_value_ids);
    let all_effect_methods = collect_std_snapshot_effect_methods(state, &all_value_ids);
    let roles = collect_std_snapshot_roles(state);
    let effects = collect_std_snapshot_effects(state);

    namespace_artifacts
        .into_iter()
        .map(|artifact| {
            let unit_value_ids = compiled_unit_value_id_remap(
                &artifact.namespace,
                &value_defs_by_path,
                &all_value_ids,
            );
            let typed = compiled_typed_surface_for_namespace(
                &artifact.namespace,
                &unit_value_ids,
                &all_schemes,
                &roles,
                &all_role_methods,
                &all_role_impls,
                &effects,
                &all_effect_methods,
            );
            CompiledUnitTypedArtifact {
                manifest: artifact.manifest,
                namespace: artifact.namespace,
                typed,
            }
        })
        .collect()
}

pub fn import_std_infer_snapshot_data(
    data: &StdInferSnapshotData,
) -> Result<StdInferSnapshotImport, StdInferSnapshotImportError> {
    data.validate()
        .map_err(StdInferSnapshotImportError::InvalidData)?;
    reserve_std_infer_snapshot_type_vars(data);

    let mut state = LowerState::new();
    install_builtin_primitives(&mut state);
    import_std_snapshot_module_skeletons(&mut state, &data.modules);

    let modules = import_std_snapshot_modules(&state, &data.modules);
    let values = import_std_snapshot_values(&state, &data.values);
    let types = import_std_snapshot_types(&state, &data.types);
    let refs = import_std_snapshot_refs(data, &values, &modules);
    import_std_snapshot_compact_schemes(data, &refs, &state);
    let coverage = import_std_snapshot_coverage(&modules, &values, &types, &refs);
    let missing = StdInferSnapshotImportMissing {
        modules: missing_snapshot_paths(&data.modules, &modules, |module| {
            (module.snapshot_id, &module.path)
        }),
        values: missing_snapshot_paths(&data.values, &values, |symbol| {
            (symbol.snapshot_id, &symbol.path)
        }),
        types: missing_snapshot_paths(&data.types, &types, |symbol| {
            (symbol.snapshot_id, &symbol.path)
        }),
    };

    Ok(StdInferSnapshotImport {
        state,
        modules,
        values,
        types,
        refs,
        missing,
        coverage,
    })
}

pub fn lower_source_set_with_std_snapshot(
    source_set: &SourceSet,
    snapshot: &StdInferSnapshot,
) -> ProfiledLoweredSources {
    let key = StdSourceCacheKey::from_source_set(source_set);
    if !snapshot.covers(&key) {
        return lower_source_set_profiled(source_set);
    }
    with_profile_enabled(true, || {
        let mut profile = source_set_profile_header(source_set);
        profile.std_cache.hits += 1;
        let clone_start = ProfileClock::now();
        let state = snapshot.instantiate();
        profile.std_cache.clone += clone_start.elapsed();
        let cached_files = std_source_file_indices(source_set);
        lower_source_set_from_cached_state(source_set, state, profile, &cached_files)
    })
}

pub fn lower_source_set_profiled(source_set: &SourceSet) -> ProfiledLoweredSources {
    lower_source_set_with_profile(source_set, true)
}

fn lower_source_set_with_profile(
    source_set: &SourceSet,
    collect_profile: bool,
) -> ProfiledLoweredSources {
    with_profile_enabled(collect_profile, || lower_source_set_inner(source_set))
}

fn lower_source_set_inner(source_set: &SourceSet) -> ProfiledLoweredSources {
    let diagnostic_source = source_set
        .files
        .iter()
        .find(|file| file.module_path.segments.is_empty())
        .map(|file| file.source.clone())
        .unwrap_or_default();

    let mut profile = source_set_profile_header(source_set);
    let mut state = LowerState::new();
    install_builtin_primitives(&mut state);
    for file in &source_set.files {
        lower_source_file_inner(file, &mut state, &mut profile);
    }
    let finish_start = ProfileClock::now();
    finish_lowering(&mut state);
    profile.finish = finish_start.elapsed();
    profile.detail = state.lower_detail.clone();

    ProfiledLoweredSources {
        lowered: LoweredSources {
            state,
            diagnostic_source,
        },
        profile,
    }
}

fn source_set_profile_header(source_set: &SourceSet) -> SourceLowerProfile {
    SourceLowerProfile {
        files: source_set.files.len(),
        entry_files: source_set.files_with_origin(SourceOrigin::Entry).count(),
        std_files: source_set.files_with_origin(SourceOrigin::Std).count(),
        user_files: source_set.files_with_origin(SourceOrigin::User).count(),
        ..SourceLowerProfile::default()
    }
}

fn lower_source_set_cached_inner(
    source_set: &SourceSet,
    cache: &mut SourceLowerCache,
) -> ProfiledLoweredSources {
    if source_set.std_files().next().is_none() {
        let mut lowered = lower_source_set_profiled(source_set);
        lowered.profile.std_cache.disabled += 1;
        return lowered;
    }

    let mut profile = source_set_profile_header(source_set);
    let state = cache.std_state(source_set, &mut profile);
    let cached_files = std_source_file_indices(source_set);
    lower_source_set_from_cached_state(source_set, state, profile, &cached_files)
}

fn lower_source_set_from_cached_state(
    source_set: &SourceSet,
    mut state: LowerState,
    mut profile: SourceLowerProfile,
    cached_files: &HashSet<usize>,
) -> ProfiledLoweredSources {
    let diagnostic_source = source_set
        .entry_files()
        .next()
        .map(|file| file.source.clone())
        .unwrap_or_default();
    if uncached_sources_may_copy_cached_act(source_set, cached_files) {
        seed_cached_source_act_templates(source_set, cached_files, &mut state, &mut profile);
    }
    for (file_idx, file) in source_set.files.iter().enumerate() {
        if cached_files.contains(&file_idx) {
            continue;
        }
        lower_source_file_inner(file, &mut state, &mut profile);
    }
    let finish_start = ProfileClock::now();
    finish_lowering(&mut state);
    profile.finish = finish_start.elapsed();
    profile.detail = state.lower_detail.clone();

    ProfiledLoweredSources {
        lowered: LoweredSources {
            state,
            diagnostic_source,
        },
        profile,
    }
}

fn uncached_sources_may_copy_cached_act(
    source_set: &SourceSet,
    cached_files: &HashSet<usize>,
) -> bool {
    source_set
        .files
        .iter()
        .enumerate()
        .filter(|(file_idx, _)| !cached_files.contains(file_idx))
        .any(|(_, file)| source_may_contain_act_copy(&file.source))
}

fn source_may_contain_act_copy(source: &str) -> bool {
    source.lines().any(line_may_contain_act_copy)
}

fn line_may_contain_act_copy(line: &str) -> bool {
    let Some((before_equal, _)) = line.split_once('=') else {
        return false;
    };
    before_equal
        .split(|ch: char| !ch.is_ascii_alphanumeric() && ch != '_')
        .any(|token| token == "act")
}

fn seed_cached_source_act_templates(
    source_set: &SourceSet,
    cached_files: &HashSet<usize>,
    state: &mut LowerState,
    profile: &mut SourceLowerProfile,
) {
    if !state.act_templates.is_empty() {
        return;
    }
    for (file_idx, file) in source_set.files.iter().enumerate() {
        if !cached_files.contains(&file_idx) {
            continue;
        }
        let source = file.source_text_for_lazy_parse();
        if !source.contains("act ") {
            continue;
        }
        let parse_start = ProfileClock::now();
        let green = parse_module_to_green_with_ops(&source, file.op_table.clone());
        let parse = parse_start.elapsed();
        profile.parse += parse;
        push_origin_profile(profile, file.origin, parse, Duration::ZERO);
        let root = SyntaxNode::<YulangLanguage>::new_root(green);
        for act in root
            .children()
            .filter(|node| node.kind() == SyntaxKind::ActDecl)
        {
            let Some(name) = act_decl_name(&act) else {
                continue;
            };
            let mut segments = file
                .module_path
                .segments
                .iter()
                .map(|segment| Name(segment.0.clone()))
                .collect::<Vec<_>>();
            segments.push(name);
            state.act_templates.insert(Path { segments }, act);
        }
    }
}

fn std_source_file_indices(source_set: &SourceSet) -> HashSet<usize> {
    source_set
        .files
        .iter()
        .enumerate()
        .filter_map(|(file_idx, file)| (file.origin == SourceOrigin::Std).then_some(file_idx))
        .collect()
}

fn act_decl_name(node: &SyntaxNode<YulangLanguage>) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|token| matches!(token.kind(), SyntaxKind::Ident | SyntaxKind::SigilIdent))
        .map(|token| Name(token.text().to_string()))
}

pub fn lower_source_file(file: &SourceFile, state: &mut LowerState) {
    with_profile_enabled(false, || {
        let mut profile = SourceLowerProfile::default();
        lower_source_file_inner(file, state, &mut profile);
    });
}

pub fn lower_source_file_profiled(
    file: &SourceFile,
    state: &mut LowerState,
    profile: &mut SourceLowerProfile,
) {
    with_profile_enabled(true, || lower_source_file_inner(file, state, profile));
}

fn lower_source_file_inner(
    file: &SourceFile,
    state: &mut LowerState,
    profile: &mut SourceLowerProfile,
) {
    let parse_start = ProfileClock::now();
    let green = parse_module_to_green_with_ops(&file.source, file.op_table.clone());
    let parse = parse_start.elapsed();
    profile.parse += parse;
    let root = SyntaxNode::<YulangLanguage>::new_root(green);
    let lower_start = ProfileClock::now();
    let file_id = state.register_file(crate::lower::state::FileInfo {
        path: file.path.clone(),
        origin: file.origin,
        source_prefix_len: file.source_prefix_len,
    });
    state.with_current_file(file_id, file.source_prefix_len, |state| {
        lower_root_in_module(state, &root, tir_module_path(file));
    });
    let lower_roots = lower_start.elapsed();
    profile.lower_roots += lower_roots;
    push_origin_profile(profile, file.origin, parse, lower_roots);
}

fn push_origin_profile(
    profile: &mut SourceLowerProfile,
    origin: SourceOrigin,
    parse: Duration,
    lower_roots: Duration,
) {
    let origin_profile = match origin {
        SourceOrigin::Entry => &mut profile.entry,
        SourceOrigin::Std => &mut profile.std,
        SourceOrigin::User => &mut profile.user,
    };
    origin_profile.files += 1;
    origin_profile.parse += parse;
    origin_profile.lower_roots += lower_roots;
}

fn tir_module_path(file: &SourceFile) -> Path {
    Path {
        segments: file
            .module_path
            .segments
            .iter()
            .map(|name| Name(name.0.clone()))
            .collect(),
    }
}

impl SourceLowerCache {
    fn std_state(
        &mut self,
        source_set: &SourceSet,
        profile: &mut SourceLowerProfile,
    ) -> LowerState {
        let key = StdSourceCacheKey::from_source_set(source_set);
        if let Some(snapshot) = self.covering_std_snapshot(&key) {
            profile.std_cache.hits += 1;
            let clone_start = ProfileClock::now();
            let cloned = snapshot.instantiate();
            profile.std_cache.clone += clone_start.elapsed();
            return cloned;
        }

        profile.std_cache.misses += 1;
        let build_start = ProfileClock::now();
        let snapshot = build_std_infer_snapshot_inner(source_set, Some(profile))
            .expect("std source set should build a snapshot after std file check");
        profile.std_cache.build += build_start.elapsed();
        let clone_start = ProfileClock::now();
        let state = snapshot.instantiate();
        self.std_snapshots.insert(key, snapshot);
        profile.std_cache.clone += clone_start.elapsed();
        state
    }

    fn covering_std_snapshot(&self, key: &StdSourceCacheKey) -> Option<&StdInferSnapshot> {
        self.std_snapshots.get(key).or_else(|| {
            self.std_snapshots
                .iter()
                .find_map(|(cached, snapshot)| cached.covers(key).then_some(snapshot))
        })
    }
}

impl StdInferSnapshot {
    fn new(key: StdSourceCacheKey, state: LowerState) -> Self {
        let data = StdInferSnapshotData::from_state(key.clone(), &state);
        Self { key, state, data }
    }

    fn instantiate(&self) -> LowerState {
        self.state.clone()
    }

    fn covers(&self, requested: &StdSourceCacheKey) -> bool {
        self.key.covers(requested)
    }

    pub fn manifest(&self) -> StdInferSnapshotManifest {
        StdInferSnapshotManifest {
            format_version: STD_INFER_SNAPSHOT_FORMAT_VERSION,
            key: self.key.clone(),
        }
    }

    pub fn data(&self) -> &StdInferSnapshotData {
        &self.data
    }
}

impl StdInferSnapshotData {
    pub fn validate(&self) -> Result<(), StdInferSnapshotDataError> {
        if self.manifest.format_version != STD_INFER_SNAPSHOT_FORMAT_VERSION {
            return Err(StdInferSnapshotDataError::UnsupportedFormatVersion {
                actual: self.manifest.format_version,
                expected: STD_INFER_SNAPSHOT_FORMAT_VERSION,
            });
        }
        validate_snapshot_symbols("value", &self.values)?;
        validate_snapshot_symbols("type", &self.types)?;
        validate_snapshot_modules(&self.modules, self.values.len(), self.types.len())?;
        validate_snapshot_schemes(&self.schemes, self.values.len())?;
        validate_snapshot_role_methods(&self.role_methods, self.values.len())?;
        validate_snapshot_role_impls(&self.role_impls, self.values.len())?;
        validate_snapshot_effect_methods(
            &self.effect_methods,
            self.values.len(),
            self.modules.len(),
        )?;
        validate_snapshot_effect_operations(&self.effect_operations)?;
        Ok(())
    }

    fn from_state(key: StdSourceCacheKey, state: &LowerState) -> Self {
        let manifest = StdInferSnapshotManifest {
            format_version: STD_INFER_SNAPSHOT_FORMAT_VERSION,
            key,
        };
        let (values, value_ids) = collect_std_snapshot_values(state);
        let (types, type_ids) = collect_std_snapshot_types(state);
        Self {
            manifest,
            modules: collect_std_snapshot_modules(state, &value_ids, &type_ids),
            values,
            types,
            schemes: collect_std_snapshot_schemes(state, &value_ids),
            roles: collect_std_snapshot_roles(state),
            role_methods: collect_std_snapshot_role_methods(state, &value_ids),
            role_impls: collect_std_snapshot_role_impls(state, &value_ids),
            effects: collect_std_snapshot_effects(state),
            effect_methods: collect_std_snapshot_effect_methods(state, &value_ids),
            effect_operations: collect_std_snapshot_effect_operations(state),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StdInferSnapshotDataError {
    UnsupportedFormatVersion {
        actual: u32,
        expected: u32,
    },
    NonSequentialSymbolId {
        table: &'static str,
        index: usize,
        snapshot_id: u32,
    },
    NonSequentialModuleId {
        index: usize,
        snapshot_id: u32,
    },
    MissingModuleParent {
        module: u32,
        parent: u32,
    },
    MissingModuleValue {
        module: u32,
        name: String,
        symbol: u32,
    },
    MissingModuleOperator {
        module: u32,
        name: String,
        symbol: u32,
    },
    MissingModuleType {
        module: u32,
        name: String,
        symbol: u32,
    },
    MissingModuleChild {
        module: u32,
        name: String,
        child: u32,
    },
    MissingSchemeSymbol {
        symbol: u32,
    },
    MissingRoleMethodSymbol {
        role: Vec<String>,
        name: String,
        symbol: u32,
    },
    MissingRoleImplMember {
        role: Vec<String>,
        name: String,
        symbol: u32,
    },
    MissingEffectMethodSymbol {
        name: String,
        symbol: u32,
    },
    MissingEffectMethodModule {
        name: String,
        module: u32,
    },
}

fn build_std_infer_snapshot_inner(
    source_set: &SourceSet,
    profile: Option<&mut SourceLowerProfile>,
) -> Option<StdInferSnapshot> {
    if source_set.std_files().next().is_none() {
        return None;
    }
    let key = StdSourceCacheKey::from_source_set(source_set);
    let mut state = LowerState::new();
    install_builtin_primitives(&mut state);
    let mut local_profile;
    let profile = match profile {
        Some(profile) => profile,
        None => {
            local_profile = SourceLowerProfile::default();
            &mut local_profile
        }
    };
    for file in source_set.std_files() {
        lower_source_file_inner(file, &mut state, profile);
    }
    Some(StdInferSnapshot::new(key, state))
}

fn build_std_infer_snapshot_data_inner(source_set: &SourceSet) -> Option<StdInferSnapshotData> {
    if source_set.std_files().next().is_none() {
        return None;
    }
    let key = StdSourceCacheKey::from_source_set(source_set);
    let mut state = LowerState::new();
    install_builtin_primitives(&mut state);
    let mut profile = SourceLowerProfile::default();
    for file in source_set.std_files() {
        lower_source_file_inner(file, &mut state, &mut profile);
    }
    finish_lowering(&mut state);
    Some(StdInferSnapshotData::from_state(key, &state))
}

fn build_std_core_snapshot_data_inner(source_set: &SourceSet) -> Option<StdCoreSnapshotData> {
    if source_set.std_files().next().is_none() {
        return None;
    }
    let key = StdSourceCacheKey::from_source_set(source_set);
    let manifest = StdInferSnapshotManifest {
        format_version: STD_INFER_SNAPSHOT_FORMAT_VERSION,
        key,
    };
    let mut state = LowerState::new();
    install_builtin_primitives(&mut state);
    let mut profile = SourceLowerProfile::default();
    for file in source_set.std_files() {
        lower_source_file_inner(file, &mut state, &mut profile);
    }
    finish_lowering(&mut state);
    let binding_paths = state.ctx.collect_all_binding_paths();
    let program = crate::export_core_program_for_binding_paths(&mut state, &binding_paths);
    Some(StdCoreSnapshotData { manifest, program })
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct StdSourceCacheKey {
    files: Vec<StdSourceFileCacheKey>,
}

impl StdSourceCacheKey {
    pub fn from_source_set(source_set: &SourceSet) -> Self {
        Self {
            files: source_set
                .std_files()
                .map(StdSourceFileCacheKey::from_file)
                .collect(),
        }
    }

    pub fn covers(&self, requested: &StdSourceCacheKey) -> bool {
        requested.files.iter().all(|file| self.files.contains(file))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
struct StdSourceFileCacheKey {
    module_path: Vec<String>,
    source_len: usize,
    source_hash: u64,
}

impl StdSourceFileCacheKey {
    fn from_file(file: &SourceFile) -> Self {
        Self {
            module_path: file
                .module_path
                .segments
                .iter()
                .map(|name| name.0.clone())
                .collect(),
            source_len: file.source_identity_len(),
            source_hash: file.source_identity_hash(),
        }
    }
}

fn collect_std_snapshot_modules(
    state: &LowerState,
    value_ids: &HashMap<crate::ids::DefId, u32>,
    type_ids: &HashMap<crate::ids::DefId, u32>,
) -> Vec<StdInferSnapshotModule> {
    let module_paths = collect_std_snapshot_module_paths(state);
    let module_ids = module_paths
        .iter()
        .enumerate()
        .map(|(index, (module, _))| (*module, index as u32))
        .collect::<HashMap<_, _>>();

    module_paths
        .iter()
        .map(|(module, path)| {
            let node = state.ctx.modules.node(*module);
            let parent = node
                .parent
                .and_then(|parent| module_ids.get(&parent).copied());
            StdInferSnapshotModule {
                path: snapshot_path_segments(path),
                snapshot_id: module_ids[module],
                parent,
                values: snapshot_module_values(state, *module, &value_ids),
                operators: snapshot_module_operators(state, *module, &value_ids),
                types: snapshot_module_types(state, *module, &type_ids),
                modules: snapshot_module_children(state, *module, &module_ids),
                reexports: snapshot_module_reexports(state, *module),
            }
        })
        .collect()
}

fn validate_snapshot_symbols(
    table: &'static str,
    symbols: &[StdInferSnapshotSymbol],
) -> Result<(), StdInferSnapshotDataError> {
    for (index, symbol) in symbols.iter().enumerate() {
        if symbol.snapshot_id != index as u32 {
            return Err(StdInferSnapshotDataError::NonSequentialSymbolId {
                table,
                index,
                snapshot_id: symbol.snapshot_id,
            });
        }
    }
    Ok(())
}

fn validate_snapshot_modules(
    modules: &[StdInferSnapshotModule],
    values_len: usize,
    types_len: usize,
) -> Result<(), StdInferSnapshotDataError> {
    for (index, module) in modules.iter().enumerate() {
        if module.snapshot_id != index as u32 {
            return Err(StdInferSnapshotDataError::NonSequentialModuleId {
                index,
                snapshot_id: module.snapshot_id,
            });
        }
        if let Some(parent) = module.parent {
            if parent as usize >= modules.len() {
                return Err(StdInferSnapshotDataError::MissingModuleParent {
                    module: module.snapshot_id,
                    parent,
                });
            }
        }
        for value in &module.values {
            if value.symbol as usize >= values_len {
                return Err(StdInferSnapshotDataError::MissingModuleValue {
                    module: module.snapshot_id,
                    name: value.name.clone(),
                    symbol: value.symbol,
                });
            }
        }
        for operator in &module.operators {
            if operator.symbol as usize >= values_len {
                return Err(StdInferSnapshotDataError::MissingModuleOperator {
                    module: module.snapshot_id,
                    name: operator.name.clone(),
                    symbol: operator.symbol,
                });
            }
        }
        for ty in &module.types {
            if ty.symbol as usize >= types_len {
                return Err(StdInferSnapshotDataError::MissingModuleType {
                    module: module.snapshot_id,
                    name: ty.name.clone(),
                    symbol: ty.symbol,
                });
            }
        }
        for child in &module.modules {
            if child.module as usize >= modules.len() {
                return Err(StdInferSnapshotDataError::MissingModuleChild {
                    module: module.snapshot_id,
                    name: child.name.clone(),
                    child: child.module,
                });
            }
        }
    }
    Ok(())
}

fn validate_snapshot_schemes(
    schemes: &[StdInferSnapshotScheme],
    values_len: usize,
) -> Result<(), StdInferSnapshotDataError> {
    for scheme in schemes {
        if scheme.symbol as usize >= values_len {
            return Err(StdInferSnapshotDataError::MissingSchemeSymbol {
                symbol: scheme.symbol,
            });
        }
    }
    Ok(())
}

fn validate_snapshot_role_methods(
    methods: &[StdInferSnapshotRoleMethod],
    values_len: usize,
) -> Result<(), StdInferSnapshotDataError> {
    for method in methods {
        if method.symbol as usize >= values_len {
            return Err(StdInferSnapshotDataError::MissingRoleMethodSymbol {
                role: method.role.clone(),
                name: method.name.clone(),
                symbol: method.symbol,
            });
        }
    }
    Ok(())
}

fn validate_snapshot_role_impls(
    impls: &[StdInferSnapshotRoleImpl],
    values_len: usize,
) -> Result<(), StdInferSnapshotDataError> {
    for role_impl in impls {
        for member in &role_impl.members {
            if member.symbol as usize >= values_len {
                return Err(StdInferSnapshotDataError::MissingRoleImplMember {
                    role: role_impl.role.clone(),
                    name: member.name.clone(),
                    symbol: member.symbol,
                });
            }
        }
    }
    Ok(())
}

fn validate_snapshot_effect_methods(
    methods: &[StdInferSnapshotEffectMethod],
    values_len: usize,
    modules_len: usize,
) -> Result<(), StdInferSnapshotDataError> {
    for method in methods {
        if method.symbol as usize >= values_len {
            return Err(StdInferSnapshotDataError::MissingEffectMethodSymbol {
                name: method.name.clone(),
                symbol: method.symbol,
            });
        }
        if method.module as usize >= modules_len {
            return Err(StdInferSnapshotDataError::MissingEffectMethodModule {
                name: method.name.clone(),
                module: method.module,
            });
        }
    }
    Ok(())
}

fn validate_snapshot_effect_operations(
    operations: &[StdInferSnapshotEffectOperation],
) -> Result<(), StdInferSnapshotDataError> {
    for (index, operation) in operations.iter().enumerate() {
        if operation.snapshot_id != index as u32 {
            return Err(StdInferSnapshotDataError::NonSequentialSymbolId {
                table: "effect_operation",
                index,
                snapshot_id: operation.snapshot_id,
            });
        }
    }
    Ok(())
}

fn import_std_snapshot_module_skeletons(
    state: &mut LowerState,
    modules: &[StdInferSnapshotModule],
) {
    let mut paths = modules
        .iter()
        .map(|module| path_from_snapshot_segments(&module.path))
        .collect::<Vec<_>>();
    paths.sort_by(|lhs, rhs| {
        lhs.segments
            .len()
            .cmp(&rhs.segments.len())
            .then_with(|| snapshot_path_segments(lhs).cmp(&snapshot_path_segments(rhs)))
    });
    paths.dedup_by(|lhs, rhs| lhs.segments == rhs.segments);

    for path in paths {
        let saved = state.ctx.enter_module_path(&path);
        state.ctx.leave_module_path(saved);
    }
}

fn import_std_snapshot_modules(
    state: &LowerState,
    modules: &[StdInferSnapshotModule],
) -> Vec<Option<ModuleId>> {
    modules
        .iter()
        .map(|module| {
            state
                .ctx
                .resolve_module_path(&path_from_snapshot_segments(&module.path))
        })
        .collect()
}

fn import_std_snapshot_values(
    state: &LowerState,
    values: &[StdInferSnapshotSymbol],
) -> Vec<Option<crate::ids::DefId>> {
    values
        .iter()
        .map(|symbol| {
            state
                .ctx
                .resolve_path_value(&path_from_snapshot_segments(&symbol.path))
        })
        .collect()
}

fn import_std_snapshot_types(
    state: &LowerState,
    types: &[StdInferSnapshotSymbol],
) -> Vec<Option<crate::ids::DefId>> {
    types
        .iter()
        .map(|symbol| {
            state
                .ctx
                .resolve_path_type(&path_from_snapshot_segments(&symbol.path))
        })
        .collect()
}

fn import_std_snapshot_refs(
    data: &StdInferSnapshotData,
    values: &[Option<crate::ids::DefId>],
    modules: &[Option<ModuleId>],
) -> StdInferSnapshotImportRefs {
    StdInferSnapshotImportRefs {
        schemes: data
            .schemes
            .iter()
            .map(|scheme| values[scheme.symbol as usize])
            .collect(),
        role_methods: data
            .role_methods
            .iter()
            .map(|method| values[method.symbol as usize])
            .collect(),
        role_impl_members: data
            .role_impls
            .iter()
            .map(|role_impl| {
                role_impl
                    .members
                    .iter()
                    .map(|member| values[member.symbol as usize])
                    .collect()
            })
            .collect(),
        effect_methods: data
            .effect_methods
            .iter()
            .map(|method| values[method.symbol as usize])
            .collect(),
        effect_method_modules: data
            .effect_methods
            .iter()
            .map(|method| modules[method.module as usize])
            .collect(),
    }
}

fn import_compiled_typed_refs(
    typed: &CompiledTypedSurface,
    values: &[Option<crate::ids::DefId>],
) -> CompiledTypedImportRefs {
    CompiledTypedImportRefs {
        schemes: typed
            .schemes
            .iter()
            .map(|scheme| values[scheme.symbol as usize])
            .collect(),
        role_methods: typed
            .role_methods
            .iter()
            .map(|method| values[method.symbol as usize])
            .collect(),
        role_impl_members: typed
            .role_impls
            .iter()
            .map(|role_impl| {
                role_impl
                    .members
                    .iter()
                    .map(|member| values[member.symbol as usize])
                    .collect()
            })
            .collect(),
        effect_methods: typed
            .effect_methods
            .iter()
            .map(|method| values[method.symbol as usize])
            .collect(),
    }
}

fn import_std_snapshot_coverage(
    modules: &[Option<ModuleId>],
    values: &[Option<crate::ids::DefId>],
    types: &[Option<crate::ids::DefId>],
    refs: &StdInferSnapshotImportRefs,
) -> StdInferSnapshotImportCoverage {
    StdInferSnapshotImportCoverage {
        modules_total: modules.len(),
        modules_resolved: count_resolved(modules),
        values_total: values.len(),
        values_resolved: count_resolved(values),
        types_total: types.len(),
        types_resolved: count_resolved(types),
        schemes_total: refs.schemes.len(),
        schemes_resolved: count_resolved(&refs.schemes),
        role_methods_total: refs.role_methods.len(),
        role_methods_resolved: count_resolved(&refs.role_methods),
        effect_methods_total: refs.effect_methods.len(),
        effect_methods_resolved: count_resolved(&refs.effect_methods),
    }
}

fn import_compiled_typed_coverage(
    namespace: &CompiledNamespaceImport,
    refs: &CompiledTypedImportRefs,
) -> CompiledTypedImportCoverage {
    CompiledTypedImportCoverage {
        namespace_values_total: namespace.values.len(),
        namespace_values_resolved: count_resolved(&namespace.values),
        namespace_types_total: namespace.types.len(),
        namespace_types_resolved: count_resolved(&namespace.types),
        schemes_total: refs.schemes.len(),
        schemes_resolved: count_resolved(&refs.schemes),
        role_methods_total: refs.role_methods.len(),
        role_methods_resolved: count_resolved(&refs.role_methods),
        effect_methods_total: refs.effect_methods.len(),
        effect_methods_resolved: count_resolved(&refs.effect_methods),
    }
}

fn count_resolved<T>(items: &[Option<T>]) -> usize {
    items.iter().filter(|item| item.is_some()).count()
}

fn missing_snapshot_paths<T>(
    items: &[T],
    resolved: &[Option<impl Copy>],
    item_path: impl Fn(&T) -> (u32, &Vec<String>),
) -> Vec<StdInferSnapshotMissingPath> {
    items
        .iter()
        .zip(resolved)
        .filter_map(|(item, resolved)| {
            resolved.is_none().then(|| {
                let (snapshot_id, path) = item_path(item);
                StdInferSnapshotMissingPath {
                    snapshot_id,
                    path: path.clone(),
                }
            })
        })
        .collect()
}

fn collect_std_snapshot_values(
    state: &LowerState,
) -> (Vec<StdInferSnapshotSymbol>, HashMap<crate::ids::DefId, u32>) {
    let mut values = canonical_snapshot_symbols(
        state.ctx.collect_all_binding_paths(),
        &state.ctx.canonical_value_paths(),
    );
    values.sort_by(|(_, lhs), (_, rhs)| lhs.path.cmp(&rhs.path));
    let mut id_map = HashMap::new();
    for (index, (def, symbol)) in values.iter_mut().enumerate() {
        symbol.snapshot_id = index as u32;
        id_map.insert(*def, index as u32);
    }
    (
        values.into_iter().map(|(_, symbol)| symbol).collect(),
        id_map,
    )
}

fn collect_std_snapshot_types(
    state: &LowerState,
) -> (Vec<StdInferSnapshotSymbol>, HashMap<crate::ids::DefId, u32>) {
    let mut types = canonical_snapshot_symbols(
        state.ctx.collect_all_type_paths(),
        &state.ctx.canonical_type_paths(),
    );
    types.sort_by(|(_, lhs), (_, rhs)| lhs.path.cmp(&rhs.path));
    let mut id_map = HashMap::new();
    for (index, (def, symbol)) in types.iter_mut().enumerate() {
        symbol.snapshot_id = index as u32;
        id_map.insert(*def, index as u32);
    }
    (
        types.into_iter().map(|(_, symbol)| symbol).collect(),
        id_map,
    )
}

fn canonical_snapshot_symbols(
    paths: Vec<(Path, crate::ids::DefId)>,
    canonical_paths: &HashMap<crate::ids::DefId, Path>,
) -> Vec<(crate::ids::DefId, StdInferSnapshotSymbol)> {
    let mut by_def = HashMap::<crate::ids::DefId, Path>::new();
    for (path, def) in paths {
        let path = canonical_paths.get(&def).cloned().unwrap_or(path);
        by_def
            .entry(def)
            .and_modify(|current| {
                if snapshot_path_segments(&path) < snapshot_path_segments(current) {
                    *current = path.clone();
                }
            })
            .or_insert(path);
    }
    by_def
        .into_iter()
        .map(|(def, path)| {
            (
                def,
                StdInferSnapshotSymbol {
                    path: snapshot_path_segments(&path),
                    snapshot_id: 0,
                },
            )
        })
        .collect()
}

fn collect_std_snapshot_schemes(
    state: &LowerState,
    value_ids: &HashMap<crate::ids::DefId, u32>,
) -> Vec<StdInferSnapshotScheme> {
    let compact_schemes = state.infer.compact_schemes.borrow();
    let infer_def_tvs = state.infer.def_tvs.borrow();
    let mut schemes = value_ids
        .iter()
        .filter_map(|(def, symbol)| {
            let compact = if let Some(scheme) = compact_schemes.get(def) {
                Some(scheme.clone())
            } else if let Some(tv) = state.def_tvs.get(def).or_else(|| infer_def_tvs.get(def)) {
                Some(crate::simplify::compact::compact_type_var(
                    &state.infer,
                    *tv,
                ))
            } else {
                return None;
            };
            let rendered = crate::display::dump::format_compact_scheme(
                compact.as_ref().expect("compact scheme should exist"),
            );
            Some(StdInferSnapshotScheme {
                symbol: *symbol,
                rendered,
                compact,
                role_constraints: snapshot_role_constraints_for_def(state, *def),
            })
        })
        .collect::<Vec<_>>();
    schemes.sort_by(|lhs, rhs| lhs.symbol.cmp(&rhs.symbol));
    schemes
}

fn snapshot_role_constraints_for_def(
    state: &LowerState,
    def: crate::ids::DefId,
) -> Vec<CompactRoleConstraint> {
    let compact = state.infer.compact_role_constraints_of(def);
    if compact.is_empty() {
        crate::lower::role::compact_role_constraints(&state.infer, def)
    } else {
        compact
    }
}

fn collect_std_snapshot_roles(state: &LowerState) -> Vec<StdInferSnapshotRole> {
    let mut roles = state
        .infer
        .role_arg_infos
        .borrow()
        .iter()
        .map(|(role, args)| StdInferSnapshotRole {
            path: snapshot_path_segments(role),
            args: args
                .iter()
                .map(|arg| StdInferSnapshotRoleArg {
                    name: arg.name.clone(),
                    is_input: arg.is_input,
                })
                .collect(),
        })
        .collect::<Vec<_>>();
    roles.sort_by(|lhs, rhs| lhs.path.cmp(&rhs.path));
    roles
}

fn collect_std_snapshot_role_methods(
    state: &LowerState,
    value_ids: &HashMap<crate::ids::DefId, u32>,
) -> Vec<StdInferSnapshotRoleMethod> {
    let mut methods = state
        .infer
        .role_methods
        .values()
        .filter_map(|info| {
            value_ids
                .get(&info.def)
                .copied()
                .map(|symbol| StdInferSnapshotRoleMethod {
                    role: snapshot_path_segments(&info.role),
                    name: info.name.0.clone(),
                    symbol,
                    input_names: info.input_names.clone(),
                    output_name: info.output_name.clone(),
                    has_receiver: info.has_receiver,
                    has_default_body: info.has_default_body,
                })
        })
        .collect::<Vec<_>>();
    methods.sort_by(|lhs, rhs| {
        lhs.role
            .cmp(&rhs.role)
            .then_with(|| lhs.name.cmp(&rhs.name))
    });
    methods
}

fn collect_std_snapshot_role_impls(
    state: &LowerState,
    value_ids: &HashMap<crate::ids::DefId, u32>,
) -> Vec<StdInferSnapshotRoleImpl> {
    let mut impls = state
        .infer
        .role_impl_candidates
        .borrow()
        .values()
        .flat_map(|candidates| candidates.iter())
        .map(|candidate| {
            let mut members = candidate
                .member_defs
                .iter()
                .filter_map(|(name, def)| {
                    value_ids
                        .get(def)
                        .copied()
                        .map(|symbol| StdInferSnapshotRoleImplMember {
                            name: name.0.clone(),
                            symbol,
                        })
                })
                .collect::<Vec<_>>();
            members.sort_by(|lhs, rhs| lhs.name.cmp(&rhs.name));
            StdInferSnapshotRoleImpl {
                role: snapshot_path_segments(&candidate.role),
                args: candidate.args.clone(),
                compact_args: candidate.compact_args.clone(),
                prerequisites: candidate.prerequisites.clone(),
                members,
            }
        })
        .collect::<Vec<_>>();
    impls.sort_by(|lhs, rhs| {
        lhs.role
            .cmp(&rhs.role)
            .then_with(|| lhs.args.cmp(&rhs.args))
    });
    impls
}

fn collect_std_snapshot_effects(state: &LowerState) -> Vec<StdInferSnapshotEffect> {
    let mut effects = state
        .effect_arities
        .iter()
        .map(|(path, arity)| StdInferSnapshotEffect {
            path: snapshot_path_segments(path),
            arity: *arity,
        })
        .collect::<Vec<_>>();
    effects.sort_by(|lhs, rhs| lhs.path.cmp(&rhs.path));
    effects
}

fn collect_std_snapshot_effect_methods(
    state: &LowerState,
    value_ids: &HashMap<crate::ids::DefId, u32>,
) -> Vec<StdInferSnapshotEffectMethod> {
    let module_ids = collect_std_snapshot_module_paths(state)
        .iter()
        .enumerate()
        .map(|(index, (module, _))| (*module, index as u32))
        .collect::<HashMap<_, _>>();
    let mut methods = state
        .infer
        .effect_methods
        .values()
        .flat_map(|methods| methods.iter())
        .filter_map(|method| {
            let symbol = value_ids.get(&method.def).copied()?;
            let module = module_ids.get(&method.module).copied()?;
            let module_path = state.ctx.module_path(method.module);
            Some(StdInferSnapshotEffectMethod {
                name: method.name.0.clone(),
                effect: snapshot_path_segments(&method.effect),
                symbol,
                module,
                module_path: snapshot_path_segments(&module_path),
                visibility: snapshot_visibility(method.visibility),
                receiver_expects_computation: method.receiver_expects_computation,
            })
        })
        .collect::<Vec<_>>();
    methods.sort_by(|lhs, rhs| {
        lhs.effect
            .cmp(&rhs.effect)
            .then_with(|| lhs.name.cmp(&rhs.name))
            .then_with(|| lhs.symbol.cmp(&rhs.symbol))
    });
    methods
}

fn collect_std_snapshot_effect_operations(
    state: &LowerState,
) -> Vec<StdInferSnapshotEffectOperation> {
    let mut operations = state
        .effect_op_effect_paths
        .iter()
        .map(|(_, path)| StdInferSnapshotEffectOperation {
            snapshot_id: 0,
            effect_path: snapshot_path_segments(path),
        })
        .collect::<Vec<_>>();
    operations.sort_by(|lhs, rhs| lhs.effect_path.cmp(&rhs.effect_path));
    for (index, operation) in operations.iter_mut().enumerate() {
        operation.snapshot_id = index as u32;
    }
    operations
}

fn collect_std_snapshot_module_paths(state: &LowerState) -> Vec<(ModuleId, Path)> {
    let mut out = Vec::new();
    for module in state.ctx.modules.module_ids() {
        if state.ctx.modules.node(module).parent.is_none() {
            collect_std_snapshot_module_paths_from(
                state,
                module,
                Path {
                    segments: Vec::new(),
                },
                &mut out,
            );
        }
    }
    out.sort_by(|(_, lhs), (_, rhs)| snapshot_path_segments(lhs).cmp(&snapshot_path_segments(rhs)));
    out
}

fn collect_std_snapshot_module_paths_from(
    state: &LowerState,
    module: ModuleId,
    path: Path,
    out: &mut Vec<(ModuleId, Path)>,
) {
    out.push((module, path.clone()));
    let mut children = state
        .ctx
        .modules
        .node(module)
        .modules
        .iter()
        .filter_map(|(name, child)| {
            (state.ctx.modules.node(*child).parent == Some(module)).then_some((name, *child))
        })
        .collect::<Vec<_>>();
    children.sort_by(|(lhs, _), (rhs, _)| lhs.0.cmp(&rhs.0));
    for (name, child) in children {
        let mut child_path = path.clone();
        child_path.segments.push(name.clone());
        collect_std_snapshot_module_paths_from(state, child, child_path, out);
    }
}

fn compiled_namespace_surface_for_modules(
    state: &LowerState,
    source_modules: &[yulang_typed_ir::Path],
    value_paths: &[(Path, crate::ids::DefId)],
    type_paths: &[(Path, crate::ids::DefId)],
) -> CompiledNamespaceSurface {
    let root_module_ids = source_modules
        .iter()
        .filter_map(|module_path| module_id_for_core_path(state, module_path))
        .collect::<Vec<_>>();
    let mut module_ids = Vec::new();
    for module in root_module_ids {
        collect_namespace_surface_module_tree(state, module, &mut module_ids);
    }
    module_ids.sort_by_key(|module| module.0);
    module_ids.dedup();
    let unit_paths = module_ids
        .iter()
        .map(|module| snapshot_path_segments(&state.ctx.module_path(*module)))
        .collect::<Vec<_>>();
    let mut value_defs = HashMap::new();
    let mut type_defs = HashMap::new();
    let values = compiled_namespace_symbols_for_defs(
        value_paths,
        module_ids.iter().flat_map(|module| {
            state
                .ctx
                .modules
                .node(*module)
                .values
                .values()
                .chain(state.ctx.modules.node(*module).operator_values.values())
                .copied()
        }),
        &state.ctx.canonical_value_paths(),
        &unit_paths,
        &mut value_defs,
    );
    let types = compiled_namespace_symbols_for_defs(
        type_paths,
        module_ids
            .iter()
            .flat_map(|module| state.ctx.modules.node(*module).types.values().copied()),
        &state.ctx.canonical_type_paths(),
        &unit_paths,
        &mut type_defs,
    );
    let modules = module_ids
        .into_iter()
        .map(|module| compiled_namespace_module(state, module, &value_defs, &type_defs))
        .collect::<Vec<_>>();

    CompiledNamespaceSurface {
        modules,
        values,
        types,
    }
}

fn collect_namespace_surface_module_tree(
    state: &LowerState,
    module: ModuleId,
    out: &mut Vec<ModuleId>,
) {
    out.push(module);
    let children = state
        .ctx
        .modules
        .node(module)
        .modules
        .iter()
        .filter_map(|(name, child)| {
            (state.ctx.modules.node(*child).parent == Some(module)
                && namespace_surface_includes_child_module(state, name, *child))
            .then_some(*child)
        })
        .collect::<Vec<_>>();
    for child in children {
        collect_namespace_surface_module_tree(state, child, out);
    }
}

fn namespace_surface_includes_child_module(
    state: &LowerState,
    name: &Name,
    child: ModuleId,
) -> bool {
    state.companion_modules.contains(&child) || name.0.starts_with("&impl#")
}

fn compiled_unit_value_id_remap(
    namespace: &CompiledNamespaceSurface,
    value_defs_by_path: &HashMap<Vec<String>, crate::ids::DefId>,
    all_value_ids: &HashMap<crate::ids::DefId, u32>,
) -> HashMap<u32, u32> {
    let mut remap = HashMap::new();
    for symbol in &namespace.values {
        let Some(def) = value_defs_by_path.get(&symbol.path) else {
            continue;
        };
        let Some(global_id) = all_value_ids.get(def) else {
            continue;
        };
        remap.insert(*global_id, symbol.unit_id);
    }
    remap
}

fn build_compiled_runtime_surfaces(
    state: &LowerState,
    typed_artifacts: &[CompiledUnitTypedArtifact],
) -> Vec<CompiledRuntimeSurface> {
    let value_paths = state.ctx.collect_all_binding_paths();
    let unit_runtime_binding_paths = typed_artifacts
        .iter()
        .flat_map(|artifact| {
            let unit_paths = artifact
                .namespace
                .modules
                .iter()
                .map(|module| module.path.clone())
                .collect::<Vec<_>>();
            compiled_runtime_binding_paths_for_modules(&value_paths, &unit_paths)
                .into_iter()
                .map(|(path, _)| snapshot_path_segments(&path))
        })
        .collect::<HashSet<_>>();
    let primitive_unit_index = typed_artifacts
        .iter()
        .find(|artifact| artifact.manifest.origin == SourceCompilationUnitOrigin::Std)
        .or_else(|| typed_artifacts.first())
        .map(|artifact| artifact.manifest.unit_index);

    typed_artifacts
        .iter()
        .map(|artifact| {
            let unit_paths = artifact
                .namespace
                .modules
                .iter()
                .map(|module| module.path.clone())
                .collect::<Vec<_>>();
            let mut binding_paths =
                compiled_runtime_binding_paths_for_modules(&value_paths, &unit_paths);
            let extra_runtime_paths = if Some(artifact.manifest.unit_index) == primitive_unit_index
            {
                extend_primitive_runtime_binding_paths(
                    state,
                    &value_paths,
                    &unit_runtime_binding_paths,
                    &mut binding_paths,
                )
            } else {
                Vec::new()
            };
            let mut export_state = state.clone();
            let mut program =
                crate::export_core_program_for_binding_paths(&mut export_state, &binding_paths);
            let aliases = compiled_runtime_binding_aliases(state, &binding_paths);
            add_core_program_binding_aliases(&mut program, &aliases);
            prune_core_program_to_modules_and_paths(
                &mut program,
                &unit_paths,
                &extra_runtime_paths,
            );
            clear_core_program_roots(&mut program);
            CompiledRuntimeSurface { program }
        })
        .collect()
}

fn extend_primitive_runtime_binding_paths(
    state: &LowerState,
    value_paths: &[(Path, crate::ids::DefId)],
    unit_runtime_binding_paths: &HashSet<Vec<String>>,
    binding_paths: &mut Vec<(Path, crate::ids::DefId)>,
) -> Vec<typed_ir::Path> {
    let mut seen_paths = binding_paths
        .iter()
        .map(|(path, _)| snapshot_path_segments(path))
        .collect::<HashSet<_>>();
    let mut extra = Vec::new();
    for (path, def) in value_paths {
        let path_segments = snapshot_path_segments(path);
        if seen_paths.contains(&path_segments)
            || unit_runtime_binding_paths.contains(&path_segments)
            || !def_has_primitive_body(state, *def)
        {
            continue;
        }
        extra.push(core_path_from_symbol_path(path));
        binding_paths.push((path.clone(), *def));
        seen_paths.insert(path_segments);
    }
    for (def, path) in crate::export::paths::collect_canonical_binding_paths(state) {
        let path_segments = snapshot_path_segments(&path);
        if seen_paths.contains(&path_segments)
            || unit_runtime_binding_paths.contains(&path_segments)
            || !def_has_primitive_body(state, def)
        {
            continue;
        }
        extra.push(core_path_from_symbol_path(&path));
        binding_paths.push((path, def));
        seen_paths.insert(path_segments);
    }
    extra
}

fn def_has_primitive_body(state: &LowerState, def: crate::ids::DefId) -> bool {
    let Some(body) = state.principal_bodies.get(&def) else {
        return false;
    };
    matches!(body.kind, crate::ast::expr::ExprKind::PrimitiveOp(_))
}

fn compiled_runtime_binding_aliases(
    state: &LowerState,
    binding_paths: &[(Path, crate::ids::DefId)],
) -> Vec<(typed_ir::Path, typed_ir::Path)> {
    let canonical_paths = state.ctx.canonical_value_paths();
    binding_paths
        .iter()
        .filter_map(|(path, def)| {
            if state.effect_op_args.contains_key(def) || path_contains_impl_helper_module(path) {
                return None;
            }
            let canonical = canonical_paths.get(def)?;
            (canonical != path).then(|| {
                (
                    core_path_from_symbol_path(canonical),
                    core_path_from_symbol_path(path),
                )
            })
        })
        .collect()
}

fn path_contains_impl_helper_module(path: &Path) -> bool {
    path.segments
        .iter()
        .any(|segment| segment.0.starts_with("&impl#"))
}

fn path_contains_runtime_identity_segment_core(path: &typed_ir::Path) -> bool {
    path.segments
        .iter()
        .any(|segment| segment.0.starts_with("#effect-method:"))
}

fn add_core_program_binding_aliases(
    program: &mut CoreProgram,
    aliases: &[(typed_ir::Path, typed_ir::Path)],
) {
    let mut existing_bindings = program
        .program
        .bindings
        .iter()
        .map(|binding| binding.name.clone())
        .collect::<HashSet<_>>();
    for (canonical, alias) in aliases {
        if existing_bindings.contains(alias) {
            continue;
        }
        let Some(mut binding) = program
            .program
            .bindings
            .iter()
            .find(|binding| binding.name == *canonical)
            .cloned()
        else {
            continue;
        };
        binding.name = alias.clone();
        if path_contains_runtime_identity_segment_core(alias) {
            binding.body = typed_ir::Expr::Var(canonical.clone());
        }
        existing_bindings.insert(alias.clone());
        program.program.bindings.push(binding);
    }

    let mut existing_graph_bindings = program
        .graph
        .bindings
        .iter()
        .map(|node| node.binding.clone())
        .collect::<HashSet<_>>();
    for (canonical, alias) in aliases {
        if existing_graph_bindings.contains(alias) {
            continue;
        }
        let Some(mut node) = program
            .graph
            .bindings
            .iter()
            .find(|node| node.binding == *canonical)
            .cloned()
        else {
            continue;
        };
        node.binding = alias.clone();
        existing_graph_bindings.insert(alias.clone());
        program.graph.bindings.push(node);
    }

    let mut existing_symbols = program
        .graph
        .runtime_symbols
        .iter()
        .map(|symbol| symbol.path.clone())
        .collect::<HashSet<_>>();
    for (canonical, alias) in aliases {
        if existing_symbols.contains(alias) {
            continue;
        }
        let Some(mut symbol) = program
            .graph
            .runtime_symbols
            .iter()
            .find(|symbol| symbol.path == *canonical)
            .cloned()
        else {
            continue;
        };
        symbol.path = alias.clone();
        existing_symbols.insert(alias.clone());
        program.graph.runtime_symbols.push(symbol);
    }
}

fn prune_core_program_to_modules_and_paths(
    program: &mut CoreProgram,
    module_paths: &[Vec<String>],
    extra_paths: &[typed_ir::Path],
) {
    program.program.bindings.retain(|binding| {
        core_path_belongs_to_modules_or_paths(&binding.name, module_paths, extra_paths)
    });
    program.graph.bindings.retain(|node| {
        core_path_belongs_to_modules_or_paths(&node.binding, module_paths, extra_paths)
    });
    program.graph.runtime_symbols.retain(|symbol| {
        core_path_belongs_to_modules_or_paths(&symbol.path, module_paths, extra_paths)
    });
    program.graph.role_impls.retain(|node| {
        node.members.iter().any(|member| {
            core_path_belongs_to_modules_or_paths(&member.value, module_paths, extra_paths)
        })
    });
}

fn core_path_belongs_to_modules_or_paths(
    path: &typed_ir::Path,
    modules: &[Vec<String>],
    extra_paths: &[typed_ir::Path],
) -> bool {
    extra_paths.iter().any(|extra| extra == path) || core_path_belongs_to_modules(path, modules)
}

fn core_path_belongs_to_modules(path: &typed_ir::Path, modules: &[Vec<String>]) -> bool {
    let segments = path
        .segments
        .iter()
        .map(|segment| segment.0.clone())
        .collect::<Vec<_>>();
    path_belongs_to_modules(&segments, modules)
}

fn core_path_from_symbol_path(path: &Path) -> typed_ir::Path {
    typed_ir::Path {
        segments: path
            .segments
            .iter()
            .map(|segment| typed_ir::Name(segment.0.clone()))
            .collect(),
    }
}

fn merge_compiled_runtime_surfaces<'a>(
    surfaces: impl IntoIterator<Item = &'a CompiledRuntimeSurface>,
) -> Result<CompiledRuntimeSurface, CompiledRuntimeMergeError> {
    let mut merged = CompiledRuntimeSurface::default();
    let mut next_expected_id = 0u32;
    let mut next_adapter_id = 0u32;
    for surface in surfaces {
        let expected_edge_offset = next_expected_id;
        let adapter_edge_offset = next_adapter_id;
        let root_expr_offset = merged.program.program.root_exprs.len();
        let mut program = surface.program.clone();
        clear_core_program_roots(&mut program);
        remap_core_program_runtime_ids(
            &mut program,
            expected_edge_offset,
            adapter_edge_offset,
            root_expr_offset,
        );
        next_expected_id = next_expected_id.max(next_expected_edge_id(&program));
        next_adapter_id = next_adapter_id.max(next_adapter_edge_id(&program));
        merge_core_program_into(&mut merged.program, program)?;
    }
    Ok(merged)
}

fn merge_runtime_bundle_with_user_program(
    dependencies: &CompiledRuntimeSurface,
    mut user_program: CoreProgram,
) -> Result<CoreProgram, CompiledRuntimeMergeError> {
    let dependency_program = &dependencies.program;
    prune_user_program_dependency_runtime_duplicates(&mut user_program, dependency_program);
    let user_binding_roots = user_program
        .program
        .bindings
        .iter()
        .map(|binding| binding.name.clone())
        .collect::<Vec<_>>();
    let expected_edge_offset = next_expected_edge_id(dependency_program);
    let adapter_edge_offset = next_adapter_edge_id(dependency_program);
    remap_core_program_runtime_ids(
        &mut user_program,
        expected_edge_offset,
        adapter_edge_offset,
        0,
    );
    let reachable = collect_runtime_merge_reachable_paths(dependency_program, &user_program);
    let mut merged = clone_reachable_dependency_program(dependency_program, &reachable);
    merge_core_program_into(&mut merged, user_program)?;
    prune_core_program_to_reachable_runtime_with_extra_roots(&mut merged, &user_binding_roots);
    Ok(merged)
}

fn clear_core_program_roots(program: &mut CoreProgram) {
    program.program.root_exprs.clear();
    program.program.roots.clear();
    program.graph.root_exprs.clear();
}

fn prune_user_program_dependency_runtime_duplicates(
    user_program: &mut CoreProgram,
    dependencies: &CoreProgram,
) {
    let dependency_bindings = dependencies
        .program
        .bindings
        .iter()
        .map(|binding| binding.name.clone())
        .collect::<HashSet<_>>();
    let dependency_runtime_symbols = dependencies
        .graph
        .runtime_symbols
        .iter()
        .map(|symbol| symbol.path.clone())
        .collect::<HashSet<_>>();

    user_program
        .program
        .bindings
        .retain(|binding| !dependency_bindings.contains(&binding.name));
    user_program
        .graph
        .bindings
        .retain(|node| !dependency_bindings.contains(&node.binding));
    user_program
        .graph
        .runtime_symbols
        .retain(|symbol| !dependency_runtime_symbols.contains(&symbol.path));
}

fn collect_runtime_merge_reachable_paths(
    dependencies: &CoreProgram,
    user_program: &CoreProgram,
) -> HashSet<typed_ir::Path> {
    let mut bindings_by_path = HashMap::new();
    extend_core_binding_body_index(&mut bindings_by_path, dependencies);
    extend_core_binding_body_index(&mut bindings_by_path, user_program);

    let mut reachable = HashSet::new();
    let mut stack = Vec::new();

    collect_core_program_root_runtime_paths(user_program, &mut stack);
    stack.extend(
        user_program
            .program
            .bindings
            .iter()
            .map(|binding| binding.name.clone()),
    );
    collect_core_program_role_impl_member_paths(dependencies, &mut stack);
    collect_core_program_role_impl_member_paths(user_program, &mut stack);

    while let Some(path) = stack.pop() {
        if !reachable.insert(path.clone()) {
            continue;
        }
        let Some(body) = bindings_by_path.get(&path) else {
            continue;
        };
        collect_core_expr_runtime_paths(body, &mut stack);
    }

    reachable
}

fn extend_core_binding_body_index<'a>(
    bindings_by_path: &mut HashMap<typed_ir::Path, &'a typed_ir::Expr>,
    program: &'a CoreProgram,
) {
    for binding in &program.program.bindings {
        bindings_by_path.insert(binding.name.clone(), &binding.body);
    }
}

fn collect_core_program_root_runtime_paths(program: &CoreProgram, stack: &mut Vec<typed_ir::Path>) {
    for expr in &program.program.root_exprs {
        collect_core_expr_runtime_paths(expr, stack);
    }
    for root in &program.program.roots {
        match root {
            typed_ir::PrincipalRoot::Binding(path) => stack.push(path.clone()),
            typed_ir::PrincipalRoot::Expr(index) => {
                if let Some(expr) = program.program.root_exprs.get(*index) {
                    collect_core_expr_runtime_paths(expr, stack);
                }
            }
        }
    }
}

fn collect_core_program_role_impl_member_paths(
    program: &CoreProgram,
    stack: &mut Vec<typed_ir::Path>,
) {
    for role_impl in &program.graph.role_impls {
        stack.extend(role_impl.members.iter().map(|member| member.value.clone()));
    }
}

fn clone_reachable_dependency_program(
    dependencies: &CoreProgram,
    reachable: &HashSet<typed_ir::Path>,
) -> CoreProgram {
    CoreProgram {
        program: typed_ir::PrincipalModule {
            path: dependencies.program.path.clone(),
            bindings: dependencies
                .program
                .bindings
                .iter()
                .filter(|binding| reachable.contains(&binding.name))
                .cloned()
                .collect(),
            root_exprs: Vec::new(),
            roots: Vec::new(),
        },
        graph: typed_ir::CoreGraphView {
            bindings: dependencies
                .graph
                .bindings
                .iter()
                .filter(|node| reachable.contains(&node.binding))
                .cloned()
                .collect(),
            root_exprs: Vec::new(),
            runtime_symbols: dependencies
                .graph
                .runtime_symbols
                .iter()
                .filter(|symbol| reachable.contains(&symbol.path))
                .cloned()
                .collect(),
            enum_variants: dependencies.graph.enum_variants.clone(),
            role_impls: dependencies.graph.role_impls.clone(),
            primitive_types: dependencies.graph.primitive_types.clone(),
        },
        evidence: dependencies.evidence.clone(),
    }
}

fn prune_core_program_to_reachable_runtime_with_extra_roots(
    program: &mut CoreProgram,
    extra_roots: &[typed_ir::Path],
) {
    let bindings_by_path = program
        .program
        .bindings
        .iter()
        .map(|binding| (binding.name.clone(), &binding.body))
        .collect::<HashMap<_, _>>();
    let mut reachable = HashSet::new();
    let mut stack = Vec::new();

    collect_core_program_root_runtime_paths(program, &mut stack);
    stack.extend(extra_roots.iter().cloned());
    collect_core_program_role_impl_member_paths(program, &mut stack);

    while let Some(path) = stack.pop() {
        if !reachable.insert(path.clone()) {
            continue;
        }
        let Some(body) = bindings_by_path.get(&path) else {
            continue;
        };
        collect_core_expr_runtime_paths(body, &mut stack);
    }

    program
        .program
        .bindings
        .retain(|binding| reachable.contains(&binding.name));
    program.program.roots.retain(|root| match root {
        typed_ir::PrincipalRoot::Binding(path) => reachable.contains(path),
        typed_ir::PrincipalRoot::Expr(_) => true,
    });
    program
        .graph
        .bindings
        .retain(|node| reachable.contains(&node.binding));
    program
        .graph
        .runtime_symbols
        .retain(|symbol| reachable.contains(&symbol.path));
    program.graph.role_impls.retain(|role_impl| {
        role_impl
            .members
            .iter()
            .any(|member| reachable.contains(&member.value))
    });
}

fn collect_core_expr_runtime_paths(expr: &typed_ir::Expr, out: &mut Vec<typed_ir::Path>) {
    match expr {
        typed_ir::Expr::Var(path) => out.push(path.clone()),
        typed_ir::Expr::PrimitiveOp(_) | typed_ir::Expr::Lit(_) => {}
        typed_ir::Expr::Lambda { body, .. } => collect_core_expr_runtime_paths(body, out),
        typed_ir::Expr::Apply {
            callee,
            arg,
            evidence,
        } => {
            collect_core_expr_runtime_paths(callee, out);
            collect_core_expr_runtime_paths(arg, out);
            if let Some(target) = evidence
                .as_ref()
                .and_then(|evidence| evidence.principal_elaboration.as_ref())
                .and_then(|plan| plan.target.as_ref())
            {
                out.push(target.clone());
            }
        }
        typed_ir::Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_core_expr_runtime_paths(cond, out);
            collect_core_expr_runtime_paths(then_branch, out);
            collect_core_expr_runtime_paths(else_branch, out);
        }
        typed_ir::Expr::Tuple(items) => {
            for item in items {
                collect_core_expr_runtime_paths(item, out);
            }
        }
        typed_ir::Expr::Record { fields, spread } => {
            for field in fields {
                collect_core_expr_runtime_paths(&field.value, out);
            }
            if let Some(spread) = spread {
                match spread {
                    typed_ir::RecordSpreadExpr::Head(expr)
                    | typed_ir::RecordSpreadExpr::Tail(expr) => {
                        collect_core_expr_runtime_paths(expr, out);
                    }
                }
            }
        }
        typed_ir::Expr::Variant { value, .. } => {
            if let Some(value) = value {
                collect_core_expr_runtime_paths(value, out);
            }
        }
        typed_ir::Expr::Select { base, .. } => collect_core_expr_runtime_paths(base, out),
        typed_ir::Expr::Match {
            scrutinee, arms, ..
        } => {
            collect_core_expr_runtime_paths(scrutinee, out);
            for arm in arms {
                collect_core_pattern_runtime_paths(&arm.pattern, out);
                if let Some(guard) = &arm.guard {
                    collect_core_expr_runtime_paths(guard, out);
                }
                collect_core_expr_runtime_paths(&arm.body, out);
            }
        }
        typed_ir::Expr::Block { stmts, tail } => {
            for stmt in stmts {
                collect_core_stmt_runtime_paths(stmt, out);
            }
            if let Some(tail) = tail {
                collect_core_expr_runtime_paths(tail, out);
            }
        }
        typed_ir::Expr::BindHere { expr }
        | typed_ir::Expr::Coerce { expr, .. }
        | typed_ir::Expr::Pack { expr, .. } => collect_core_expr_runtime_paths(expr, out),
        typed_ir::Expr::Handle { body, arms, .. } => {
            collect_core_expr_runtime_paths(body, out);
            for arm in arms {
                out.push(arm.effect.clone());
                collect_core_pattern_runtime_paths(&arm.payload, out);
                if let Some(guard) = &arm.guard {
                    collect_core_expr_runtime_paths(guard, out);
                }
                collect_core_expr_runtime_paths(&arm.body, out);
            }
        }
    }
}

fn collect_core_stmt_runtime_paths(stmt: &typed_ir::Stmt, out: &mut Vec<typed_ir::Path>) {
    match stmt {
        typed_ir::Stmt::Let { pattern, value } => {
            collect_core_pattern_runtime_paths(pattern, out);
            collect_core_expr_runtime_paths(value, out);
        }
        typed_ir::Stmt::Expr(expr) => collect_core_expr_runtime_paths(expr, out),
        typed_ir::Stmt::Module { body, .. } => collect_core_expr_runtime_paths(body, out),
    }
}

fn collect_core_pattern_runtime_paths(pattern: &typed_ir::Pattern, out: &mut Vec<typed_ir::Path>) {
    match pattern {
        typed_ir::Pattern::Wildcard | typed_ir::Pattern::Bind(_) | typed_ir::Pattern::Lit(_) => {}
        typed_ir::Pattern::Tuple(items) => {
            for item in items {
                collect_core_pattern_runtime_paths(item, out);
            }
        }
        typed_ir::Pattern::List {
            prefix,
            spread,
            suffix,
        } => {
            for item in prefix {
                collect_core_pattern_runtime_paths(item, out);
            }
            if let Some(spread) = spread {
                collect_core_pattern_runtime_paths(spread, out);
            }
            for item in suffix {
                collect_core_pattern_runtime_paths(item, out);
            }
        }
        typed_ir::Pattern::Record { fields, spread } => {
            for field in fields {
                collect_core_pattern_runtime_paths(&field.pattern, out);
                if let Some(default) = &field.default {
                    collect_core_expr_runtime_paths(default, out);
                }
            }
            if let Some(spread) = spread {
                match spread {
                    typed_ir::RecordSpreadPattern::Head(pattern)
                    | typed_ir::RecordSpreadPattern::Tail(pattern) => {
                        collect_core_pattern_runtime_paths(pattern, out);
                    }
                }
            }
        }
        typed_ir::Pattern::Variant { value, .. } => {
            if let Some(value) = value {
                collect_core_pattern_runtime_paths(value, out);
            }
        }
        typed_ir::Pattern::Or { left, right } => {
            collect_core_pattern_runtime_paths(left, out);
            collect_core_pattern_runtime_paths(right, out);
        }
        typed_ir::Pattern::As { pattern, .. } => collect_core_pattern_runtime_paths(pattern, out),
    }
}

fn next_expected_edge_id(program: &CoreProgram) -> u32 {
    program
        .evidence
        .expected_edges
        .iter()
        .map(|edge| edge.id.saturating_add(1))
        .max()
        .unwrap_or(0)
}

fn next_adapter_edge_id(program: &CoreProgram) -> u32 {
    program
        .evidence
        .expected_adapter_edges
        .iter()
        .map(|edge| edge.id.saturating_add(1))
        .max()
        .unwrap_or(0)
}

fn remap_core_program_runtime_ids(
    program: &mut CoreProgram,
    expected_edge_offset: u32,
    adapter_edge_offset: u32,
    root_expr_offset: usize,
) {
    for binding in &mut program.program.bindings {
        remap_core_expr_runtime_ids(&mut binding.body, expected_edge_offset);
    }
    for root in &mut program.program.root_exprs {
        remap_core_expr_runtime_ids(root, expected_edge_offset);
    }
    for root in &mut program.program.roots {
        if let typed_ir::PrincipalRoot::Expr(index) = root {
            *index += root_expr_offset;
        }
    }
    for edge in &mut program.evidence.expected_edges {
        edge.id += expected_edge_offset;
    }
    for edge in &mut program.evidence.expected_adapter_edges {
        edge.id += adapter_edge_offset;
        if let Some(source) = &mut edge.source_expected_edge {
            *source += expected_edge_offset;
        }
    }
    for edge in &mut program.evidence.derived_expected_edges {
        edge.parent += expected_edge_offset;
    }
    for graph_root in &mut program.graph.root_exprs {
        let typed_ir::GraphOwner::RootExpr(index) = &mut graph_root.owner;
        *index += root_expr_offset;
    }
}

fn remap_core_expr_runtime_ids(expr: &mut typed_ir::Expr, expected_edge_offset: u32) {
    match expr {
        typed_ir::Expr::Var(_) | typed_ir::Expr::PrimitiveOp(_) | typed_ir::Expr::Lit(_) => {}
        typed_ir::Expr::Lambda { body, .. } => {
            remap_core_expr_runtime_ids(body, expected_edge_offset);
        }
        typed_ir::Expr::Apply {
            callee,
            arg,
            evidence,
        } => {
            remap_core_expr_runtime_ids(callee, expected_edge_offset);
            remap_core_expr_runtime_ids(arg, expected_edge_offset);
            if let Some(evidence) = evidence {
                remap_apply_evidence_runtime_ids(evidence, expected_edge_offset);
            }
        }
        typed_ir::Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            remap_core_expr_runtime_ids(cond, expected_edge_offset);
            remap_core_expr_runtime_ids(then_branch, expected_edge_offset);
            remap_core_expr_runtime_ids(else_branch, expected_edge_offset);
        }
        typed_ir::Expr::Tuple(items) => {
            for item in items {
                remap_core_expr_runtime_ids(item, expected_edge_offset);
            }
        }
        typed_ir::Expr::Record { fields, spread } => {
            for field in fields {
                remap_core_expr_runtime_ids(&mut field.value, expected_edge_offset);
            }
            if let Some(spread) = spread {
                remap_record_spread_expr_runtime_ids(spread, expected_edge_offset);
            }
        }
        typed_ir::Expr::Variant { value, .. } => {
            if let Some(value) = value {
                remap_core_expr_runtime_ids(value, expected_edge_offset);
            }
        }
        typed_ir::Expr::Select { base, .. } => {
            remap_core_expr_runtime_ids(base, expected_edge_offset);
        }
        typed_ir::Expr::Match {
            scrutinee, arms, ..
        } => {
            remap_core_expr_runtime_ids(scrutinee, expected_edge_offset);
            for arm in arms {
                if let Some(guard) = &mut arm.guard {
                    remap_core_expr_runtime_ids(guard, expected_edge_offset);
                }
                remap_core_expr_runtime_ids(&mut arm.body, expected_edge_offset);
            }
        }
        typed_ir::Expr::Block { stmts, tail } => {
            for stmt in stmts {
                remap_core_stmt_runtime_ids(stmt, expected_edge_offset);
            }
            if let Some(tail) = tail {
                remap_core_expr_runtime_ids(tail, expected_edge_offset);
            }
        }
        typed_ir::Expr::Handle { body, arms, .. } => {
            remap_core_expr_runtime_ids(body, expected_edge_offset);
            for arm in arms {
                if let Some(guard) = &mut arm.guard {
                    remap_core_expr_runtime_ids(guard, expected_edge_offset);
                }
                remap_core_expr_runtime_ids(&mut arm.body, expected_edge_offset);
            }
        }
        typed_ir::Expr::Coerce { expr, evidence } => {
            remap_core_expr_runtime_ids(expr, expected_edge_offset);
            if let Some(evidence) = evidence {
                remap_optional_expected_edge(&mut evidence.source_edge, expected_edge_offset);
            }
        }
        typed_ir::Expr::BindHere { expr } => {
            remap_core_expr_runtime_ids(expr, expected_edge_offset);
        }
        typed_ir::Expr::Pack { expr, .. } => {
            remap_core_expr_runtime_ids(expr, expected_edge_offset);
        }
    }
}

fn remap_record_spread_expr_runtime_ids(
    spread: &mut typed_ir::RecordSpreadExpr,
    expected_edge_offset: u32,
) {
    match spread {
        typed_ir::RecordSpreadExpr::Head(expr) | typed_ir::RecordSpreadExpr::Tail(expr) => {
            remap_core_expr_runtime_ids(expr, expected_edge_offset);
        }
    }
}

fn remap_core_pattern_runtime_ids(pattern: &mut typed_ir::Pattern, expected_edge_offset: u32) {
    match pattern {
        typed_ir::Pattern::Wildcard | typed_ir::Pattern::Bind(_) | typed_ir::Pattern::Lit(_) => {}
        typed_ir::Pattern::Tuple(items) => {
            for item in items {
                remap_core_pattern_runtime_ids(item, expected_edge_offset);
            }
        }
        typed_ir::Pattern::List {
            prefix,
            spread,
            suffix,
        } => {
            for item in prefix {
                remap_core_pattern_runtime_ids(item, expected_edge_offset);
            }
            if let Some(spread) = spread {
                remap_core_pattern_runtime_ids(spread, expected_edge_offset);
            }
            for item in suffix {
                remap_core_pattern_runtime_ids(item, expected_edge_offset);
            }
        }
        typed_ir::Pattern::Record { fields, spread } => {
            for field in fields {
                remap_core_pattern_runtime_ids(&mut field.pattern, expected_edge_offset);
                if let Some(default) = &mut field.default {
                    remap_core_expr_runtime_ids(default, expected_edge_offset);
                }
            }
            if let Some(spread) = spread {
                remap_record_spread_pattern_runtime_ids(spread, expected_edge_offset);
            }
        }
        typed_ir::Pattern::Variant { value, .. } => {
            if let Some(value) = value {
                remap_core_pattern_runtime_ids(value, expected_edge_offset);
            }
        }
        typed_ir::Pattern::Or { left, right } => {
            remap_core_pattern_runtime_ids(left, expected_edge_offset);
            remap_core_pattern_runtime_ids(right, expected_edge_offset);
        }
        typed_ir::Pattern::As { pattern, .. } => {
            remap_core_pattern_runtime_ids(pattern, expected_edge_offset);
        }
    }
}

fn remap_record_spread_pattern_runtime_ids(
    spread: &mut typed_ir::RecordSpreadPattern,
    expected_edge_offset: u32,
) {
    match spread {
        typed_ir::RecordSpreadPattern::Head(pattern)
        | typed_ir::RecordSpreadPattern::Tail(pattern) => {
            remap_core_pattern_runtime_ids(pattern, expected_edge_offset);
        }
    }
}

fn remap_core_stmt_runtime_ids(stmt: &mut typed_ir::Stmt, expected_edge_offset: u32) {
    match stmt {
        typed_ir::Stmt::Let { pattern, value } => {
            remap_core_pattern_runtime_ids(pattern, expected_edge_offset);
            remap_core_expr_runtime_ids(value, expected_edge_offset);
        }
        typed_ir::Stmt::Expr(value) => {
            remap_core_expr_runtime_ids(value, expected_edge_offset);
        }
        typed_ir::Stmt::Module { body, .. } => {
            remap_core_expr_runtime_ids(body, expected_edge_offset);
        }
    }
}

fn remap_apply_evidence_runtime_ids(
    evidence: &mut typed_ir::ApplyEvidence,
    expected_edge_offset: u32,
) {
    remap_optional_expected_edge(&mut evidence.callee_source_edge, expected_edge_offset);
    remap_optional_expected_edge(&mut evidence.arg_source_edge, expected_edge_offset);
    for candidate in &mut evidence.substitution_candidates {
        remap_optional_expected_edge(&mut candidate.source_edge, expected_edge_offset);
    }
    if let Some(plan) = &mut evidence.principal_elaboration {
        for arg in &mut plan.args {
            remap_optional_expected_edge(&mut arg.source_edge, expected_edge_offset);
        }
        for adapter in &mut plan.adapters {
            remap_optional_expected_edge(&mut adapter.source_edge, expected_edge_offset);
        }
    }
}

fn remap_optional_expected_edge(edge: &mut Option<u32>, expected_edge_offset: u32) {
    if let Some(edge) = edge {
        *edge += expected_edge_offset;
    }
}

fn merge_core_program_into(
    target: &mut CoreProgram,
    source: CoreProgram,
) -> Result<(), CompiledRuntimeMergeError> {
    merge_principal_bindings(&mut target.program.bindings, source.program.bindings)?;
    target.program.root_exprs.extend(source.program.root_exprs);
    target.program.roots.extend(source.program.roots);
    merge_binding_graph_nodes(&mut target.graph.bindings, source.graph.bindings)?;
    target.graph.root_exprs.extend(source.graph.root_exprs);
    merge_runtime_symbols(
        &mut target.graph.runtime_symbols,
        source.graph.runtime_symbols,
    )?;
    merge_enum_variant_graph_nodes(&mut target.graph.enum_variants, source.graph.enum_variants);
    merge_role_impl_graph_nodes(&mut target.graph.role_impls, source.graph.role_impls);
    merge_primitive_type_graph_nodes(
        &mut target.graph.primitive_types,
        source.graph.primitive_types,
    )?;
    target
        .evidence
        .expected_edges
        .extend(source.evidence.expected_edges);
    target
        .evidence
        .expected_adapter_edges
        .extend(source.evidence.expected_adapter_edges);
    target
        .evidence
        .derived_expected_edges
        .extend(source.evidence.derived_expected_edges);
    Ok(())
}

fn merge_enum_variant_graph_nodes(
    target: &mut Vec<typed_ir::EnumVariantGraphNode>,
    source: Vec<typed_ir::EnumVariantGraphNode>,
) {
    for node in source {
        if !target.contains(&node) {
            target.push(node);
        }
    }
}

fn merge_primitive_type_graph_nodes(
    target: &mut Vec<typed_ir::PrimitiveTypeGraphNode>,
    source: Vec<typed_ir::PrimitiveTypeGraphNode>,
) -> Result<(), CompiledRuntimeMergeError> {
    for node in source {
        match target
            .iter()
            .find(|existing| existing.family == node.family)
        {
            Some(existing) if existing.path != node.path => {
                return Err(CompiledRuntimeMergeError::ConflictingPrimitiveType {
                    family: node.family,
                });
            }
            Some(_) => {}
            None => target.push(node),
        }
    }
    Ok(())
}

fn merge_role_impl_graph_nodes(
    target: &mut Vec<typed_ir::RoleImplGraphNode>,
    source: Vec<typed_ir::RoleImplGraphNode>,
) {
    for node in source {
        if !target.contains(&node) {
            target.push(node);
        }
    }
}

fn merge_principal_bindings(
    target: &mut Vec<typed_ir::PrincipalBinding>,
    source: Vec<typed_ir::PrincipalBinding>,
) -> Result<(), CompiledRuntimeMergeError> {
    let mut by_path = target
        .iter()
        .enumerate()
        .map(|(index, binding)| (binding.name.clone(), index))
        .collect::<HashMap<_, _>>();
    for binding in source {
        if let Some(index) = by_path.get(&binding.name).copied() {
            if target[index] != binding {
                return Err(CompiledRuntimeMergeError::ConflictingBinding { path: binding.name });
            }
            continue;
        }
        by_path.insert(binding.name.clone(), target.len());
        target.push(binding);
    }
    Ok(())
}

fn merge_binding_graph_nodes(
    target: &mut Vec<typed_ir::BindingGraphNode>,
    source: Vec<typed_ir::BindingGraphNode>,
) -> Result<(), CompiledRuntimeMergeError> {
    let mut by_path = target
        .iter()
        .enumerate()
        .map(|(index, node)| (node.binding.clone(), index))
        .collect::<HashMap<_, _>>();
    for node in source {
        if let Some(index) = by_path.get(&node.binding).copied() {
            if target[index] != node {
                return Err(CompiledRuntimeMergeError::ConflictingGraphBinding {
                    path: node.binding,
                });
            }
            continue;
        }
        by_path.insert(node.binding.clone(), target.len());
        target.push(node);
    }
    Ok(())
}

fn merge_runtime_symbols(
    target: &mut Vec<typed_ir::RuntimeSymbol>,
    source: Vec<typed_ir::RuntimeSymbol>,
) -> Result<(), CompiledRuntimeMergeError> {
    let mut by_path = target
        .iter()
        .enumerate()
        .map(|(index, symbol)| (symbol.path.clone(), index))
        .collect::<HashMap<_, _>>();
    for symbol in source {
        if let Some(index) = by_path.get(&symbol.path).copied() {
            if target[index].kind != symbol.kind {
                return Err(CompiledRuntimeMergeError::ConflictingRuntimeSymbol {
                    path: symbol.path,
                });
            }
            continue;
        }
        by_path.insert(symbol.path.clone(), target.len());
        target.push(symbol);
    }
    Ok(())
}

fn compiled_runtime_binding_paths_for_modules(
    value_paths: &[(Path, crate::ids::DefId)],
    unit_paths: &[Vec<String>],
) -> Vec<(Path, crate::ids::DefId)> {
    value_paths
        .iter()
        .filter(|(path, _)| path_belongs_to_modules(&snapshot_path_segments(path), unit_paths))
        .cloned()
        .collect()
}

#[allow(clippy::too_many_arguments)]
fn compiled_typed_surface_for_namespace(
    namespace: &CompiledNamespaceSurface,
    unit_value_ids: &HashMap<u32, u32>,
    schemes: &[StdInferSnapshotScheme],
    roles: &[StdInferSnapshotRole],
    role_methods: &[StdInferSnapshotRoleMethod],
    role_impls: &[StdInferSnapshotRoleImpl],
    effects: &[StdInferSnapshotEffect],
    effect_methods: &[StdInferSnapshotEffectMethod],
) -> CompiledTypedSurface {
    let unit_paths = namespace
        .modules
        .iter()
        .map(|module| module.path.clone())
        .collect::<Vec<_>>();
    CompiledTypedSurface {
        schemes: schemes
            .iter()
            .filter_map(|scheme| {
                let symbol = *unit_value_ids.get(&scheme.symbol)?;
                Some(StdInferSnapshotScheme {
                    symbol,
                    rendered: scheme.rendered.clone(),
                    compact: scheme.compact.clone(),
                    role_constraints: scheme.role_constraints.clone(),
                })
            })
            .collect(),
        roles: roles
            .iter()
            .filter(|role| path_belongs_to_modules(&role.path, &unit_paths))
            .cloned()
            .collect(),
        role_methods: role_methods
            .iter()
            .filter_map(|method| {
                let symbol = *unit_value_ids.get(&method.symbol)?;
                Some(StdInferSnapshotRoleMethod {
                    role: method.role.clone(),
                    name: method.name.clone(),
                    symbol,
                    input_names: method.input_names.clone(),
                    output_name: method.output_name.clone(),
                    has_receiver: method.has_receiver,
                    has_default_body: method.has_default_body,
                })
            })
            .collect(),
        role_impls: role_impls
            .iter()
            .map(|role_impl| {
                let members = role_impl
                    .members
                    .iter()
                    .filter_map(|member| {
                        let symbol = *unit_value_ids.get(&member.symbol)?;
                        Some(StdInferSnapshotRoleImplMember {
                            name: member.name.clone(),
                            symbol,
                        })
                    })
                    .collect::<Vec<_>>();
                StdInferSnapshotRoleImpl {
                    role: role_impl.role.clone(),
                    args: role_impl.args.clone(),
                    compact_args: role_impl.compact_args.clone(),
                    prerequisites: role_impl.prerequisites.clone(),
                    members,
                }
            })
            .filter(|role_impl| !role_impl.members.is_empty())
            .collect(),
        effects: effects
            .iter()
            .filter(|effect| path_belongs_to_modules(&effect.path, &unit_paths))
            .cloned()
            .collect(),
        effect_methods: effect_methods
            .iter()
            .filter_map(|method| {
                let symbol = *unit_value_ids.get(&method.symbol)?;
                Some(StdInferSnapshotEffectMethod {
                    name: method.name.clone(),
                    effect: method.effect.clone(),
                    symbol,
                    module: method.module,
                    module_path: method.module_path.clone(),
                    visibility: method.visibility,
                    receiver_expects_computation: method.receiver_expects_computation,
                })
            })
            .collect(),
    }
}

fn path_belongs_to_modules(path: &[String], modules: &[Vec<String>]) -> bool {
    modules.iter().any(|module| {
        !module.is_empty() && path.len() >= module.len() && path[..module.len()] == module[..]
    })
}

fn validate_compiled_typed_surface(
    typed: &CompiledTypedSurface,
    namespace: &CompiledNamespaceSurface,
) -> CompiledTypedValidation {
    let value_ids = namespace
        .values
        .iter()
        .map(|symbol| symbol.unit_id)
        .collect::<std::collections::HashSet<_>>();
    let mut validation = CompiledTypedValidation {
        schemes: typed.schemes.len(),
        roles: typed.roles.len(),
        role_methods: typed.role_methods.len(),
        role_impls: typed.role_impls.len(),
        effects: typed.effects.len(),
        effect_methods: typed.effect_methods.len(),
        ..CompiledTypedValidation::default()
    };

    for scheme in &typed.schemes {
        if !value_ids.contains(&scheme.symbol) {
            validation.missing_scheme_symbols.push(scheme.symbol);
        }
    }
    for method in &typed.role_methods {
        if !value_ids.contains(&method.symbol) {
            validation.missing_role_method_symbols.push(method.symbol);
        }
    }
    for role_impl in &typed.role_impls {
        for member in &role_impl.members {
            if !value_ids.contains(&member.symbol) {
                validation
                    .missing_role_impl_member_symbols
                    .push(member.symbol);
            }
        }
    }
    for method in &typed.effect_methods {
        if !value_ids.contains(&method.symbol) {
            validation.missing_effect_method_symbols.push(method.symbol);
        }
    }

    validation
}

fn trusted_compiled_typed_validation(typed: &CompiledTypedSurface) -> CompiledTypedValidation {
    CompiledTypedValidation {
        schemes: typed.schemes.len(),
        roles: typed.roles.len(),
        role_methods: typed.role_methods.len(),
        role_impls: typed.role_impls.len(),
        effects: typed.effects.len(),
        effect_methods: typed.effect_methods.len(),
        ..CompiledTypedValidation::default()
    }
}

fn validate_compiled_namespace_surface(
    surface: &CompiledNamespaceSurface,
) -> CompiledNamespaceValidation {
    let value_ids = surface
        .values
        .iter()
        .map(|symbol| symbol.unit_id)
        .collect::<std::collections::HashSet<_>>();
    let type_ids = surface
        .types
        .iter()
        .map(|symbol| symbol.unit_id)
        .collect::<std::collections::HashSet<_>>();
    let mut validation = CompiledNamespaceValidation {
        modules: surface.modules.len(),
        values: surface.values.len(),
        types: surface.types.len(),
        operators: surface
            .modules
            .iter()
            .map(|module| module.operators.len())
            .sum(),
        ..CompiledNamespaceValidation::default()
    };

    for module in &surface.modules {
        for value in &module.values {
            if !value_ids.contains(&value.symbol) {
                validation
                    .missing_value_symbols
                    .push(CompiledNamespaceMissingSymbol {
                        module_path: module.path.clone(),
                        name: value.name.clone(),
                        symbol: value.symbol,
                    });
            }
        }
        for operator in &module.operators {
            if !value_ids.contains(&operator.symbol) {
                validation
                    .missing_value_symbols
                    .push(CompiledNamespaceMissingSymbol {
                        module_path: module.path.clone(),
                        name: format!(
                            "#op:{}:{}",
                            compiled_namespace_fixity_tag(operator.fixity),
                            operator.name
                        ),
                        symbol: operator.symbol,
                    });
            }
        }
        for ty in &module.types {
            if !type_ids.contains(&ty.symbol) {
                validation
                    .missing_type_symbols
                    .push(CompiledNamespaceMissingSymbol {
                        module_path: module.path.clone(),
                        name: ty.name.clone(),
                        symbol: ty.symbol,
                    });
            }
        }
    }

    validation
}

fn trusted_compiled_namespace_validation(
    surface: &CompiledNamespaceSurface,
) -> CompiledNamespaceValidation {
    CompiledNamespaceValidation {
        modules: surface.modules.len(),
        values: surface.values.len(),
        types: surface.types.len(),
        operators: surface
            .modules
            .iter()
            .map(|module| module.operators.len())
            .sum(),
        ..CompiledNamespaceValidation::default()
    }
}

fn merge_compiled_namespace_surfaces<'a>(
    surfaces: impl IntoIterator<Item = &'a CompiledNamespaceSurface>,
) -> CompiledNamespaceSurface {
    let surfaces = surfaces.into_iter().collect::<Vec<_>>();
    let mut modules = Vec::new();
    let mut values = Vec::new();
    let mut types = Vec::new();
    for surface in &surfaces {
        let value_offset = values.len() as u32;
        let type_offset = types.len() as u32;
        values.extend(surface.values.iter().cloned().map(|mut symbol| {
            symbol.unit_id += value_offset;
            symbol
        }));
        types.extend(surface.types.iter().cloned().map(|mut symbol| {
            symbol.unit_id += type_offset;
            symbol
        }));
        modules.extend(surface.modules.iter().cloned().map(|mut module| {
            for value in &mut module.values {
                value.symbol += value_offset;
            }
            for operator in &mut module.operators {
                operator.symbol += value_offset;
            }
            for ty in &mut module.types {
                ty.symbol += type_offset;
            }
            module
        }));
    }
    modules.sort_by(|left, right| left.path.cmp(&right.path));
    CompiledNamespaceSurface {
        modules,
        values,
        types,
    }
}

fn merge_compiled_typed_surfaces(artifacts: &[CompiledUnitArtifact]) -> CompiledTypedSurface {
    let mut typed = CompiledTypedSurface::default();
    let mut value_offset = 0u32;

    for artifact in artifacts {
        typed
            .schemes
            .extend(artifact.typed.schemes.iter().cloned().map(|mut scheme| {
                scheme.symbol += value_offset;
                scheme
            }));
        typed.roles.extend(artifact.typed.roles.iter().cloned());
        typed.role_methods.extend(
            artifact
                .typed
                .role_methods
                .iter()
                .cloned()
                .map(|mut method| {
                    method.symbol += value_offset;
                    method
                }),
        );
        typed.role_impls.extend(
            artifact
                .typed
                .role_impls
                .iter()
                .cloned()
                .map(|mut role_impl| {
                    for member in &mut role_impl.members {
                        member.symbol += value_offset;
                    }
                    role_impl
                }),
        );
        typed.effects.extend(artifact.typed.effects.iter().cloned());
        typed
            .effect_methods
            .extend(
                artifact
                    .typed
                    .effect_methods
                    .iter()
                    .cloned()
                    .map(|mut method| {
                        method.symbol += value_offset;
                        method
                    }),
            );

        value_offset += artifact.namespace.values.len() as u32;
    }

    typed.roles.sort_by(|lhs, rhs| lhs.path.cmp(&rhs.path));
    typed.effects.sort_by(|lhs, rhs| lhs.path.cmp(&rhs.path));
    typed
}

fn import_compiled_namespace_module_skeletons(
    state: &mut LowerState,
    modules: &[CompiledNamespaceModule],
) {
    let mut paths = modules
        .iter()
        .map(|module| Path {
            segments: module.path.iter().cloned().map(Name).collect(),
        })
        .collect::<Vec<_>>();
    paths.sort_by(|left, right| left.segments.len().cmp(&right.segments.len()));
    paths.dedup();
    for path in paths {
        let saved = state.ctx.enter_module_path(&path);
        state.ctx.leave_module_path(saved);
    }
}

fn import_compiled_namespace_module_map(
    state: &LowerState,
    modules: &[CompiledNamespaceModule],
) -> Vec<Option<ModuleId>> {
    modules
        .iter()
        .map(|module| {
            let path = yulang_typed_ir::Path {
                segments: module
                    .path
                    .iter()
                    .cloned()
                    .map(yulang_typed_ir::Name)
                    .collect(),
            };
            module_id_for_core_path(state, &path)
        })
        .collect()
}

fn import_compiled_namespace_values(
    state: &mut LowerState,
    surface: &CompiledNamespaceSurface,
    _modules: &[Option<ModuleId>],
) -> Vec<Option<crate::ids::DefId>> {
    let mut out = vec![None; surface.values.len()];
    let mut defs_by_path = HashMap::<Vec<String>, crate::ids::DefId>::new();
    for symbol in &surface.values {
        let Some(slot) = out.get_mut(symbol.unit_id as usize) else {
            continue;
        };
        if slot.is_some() {
            continue;
        }
        let path = path_from_snapshot_segments(&symbol.path);
        if let Some(def) = defs_by_path.get(&symbol.path).copied() {
            *slot = Some(def);
            continue;
        }
        if let Some(def) = state.ctx.resolve_path_value(&path) {
            defs_by_path.insert(symbol.path.clone(), def);
            *slot = Some(def);
            continue;
        }
        let def = state.ctx.fresh_def();
        let tv = state.ctx.fresh_tv();
        let display_name = symbol
            .path
            .last()
            .cloned()
            .unwrap_or_else(|| format!("#unit-value{}", symbol.unit_id));
        state.register_def_tv(def, tv);
        state.register_def_name(def, Name(display_name));
        defs_by_path.insert(symbol.path.clone(), def);
        *slot = Some(def);
    }
    out
}

fn import_compiled_namespace_types(
    state: &mut LowerState,
    surface: &CompiledNamespaceSurface,
    _modules: &[Option<ModuleId>],
) -> Vec<Option<crate::ids::DefId>> {
    let mut out = vec![None; surface.types.len()];
    let mut defs_by_path = HashMap::<Vec<String>, crate::ids::DefId>::new();
    for symbol in &surface.types {
        let Some(slot) = out.get_mut(symbol.unit_id as usize) else {
            continue;
        };
        if slot.is_some() {
            continue;
        }
        let path = path_from_snapshot_segments(&symbol.path);
        if let Some(def) = defs_by_path.get(&symbol.path).copied() {
            *slot = Some(def);
            continue;
        }
        if let Some(def) = state.ctx.resolve_path_type(&path) {
            defs_by_path.insert(symbol.path.clone(), def);
            *slot = Some(def);
            continue;
        }
        let def = state.ctx.fresh_def();
        let tv = state.ctx.fresh_tv();
        let display_name = symbol
            .path
            .last()
            .cloned()
            .unwrap_or_else(|| format!("#unit-type{}", symbol.unit_id));
        state.register_def_tv(def, tv);
        state.register_def_name(def, Name(display_name));
        defs_by_path.insert(symbol.path.clone(), def);
        *slot = Some(def);
    }
    out
}

fn import_compiled_namespace_module_entries(
    state: &mut LowerState,
    surface: &CompiledNamespaceSurface,
    modules: &[Option<ModuleId>],
    values: &[Option<crate::ids::DefId>],
    types: &[Option<crate::ids::DefId>],
) {
    for module in &surface.modules {
        let Some(module_idx) = compiled_namespace_module_index(surface, &module.path) else {
            continue;
        };
        let Some(module_id) = modules.get(module_idx).and_then(|module| *module) else {
            continue;
        };
        for operator in &module.operators {
            let Some(def) = values.get(operator.symbol as usize).and_then(|def| *def) else {
                continue;
            };
            state
                .ctx
                .mark_operator_def(def, import_snapshot_operator_fixity(operator.fixity));
            if operator.lazy {
                state.ctx.mark_lazy_operator_def(def);
            }
            state.ctx.modules.insert_operator_value_with_visibility(
                module_id,
                Name(operator.name.clone()),
                import_snapshot_operator_fixity(operator.fixity),
                def,
                import_snapshot_visibility(operator.visibility),
            );
            state.ctx.record_canonical_value_path(
                def,
                compiled_namespace_symbol_path(&surface.values, operator.symbol),
            );
        }
        for child in &module.modules {
            let Some(child_idx) = compiled_namespace_module_index(surface, &child.module_path)
            else {
                continue;
            };
            let Some(child_id) = modules.get(child_idx).and_then(|module| *module) else {
                continue;
            };
            state.ctx.modules.insert_module_alias_with_visibility(
                module_id,
                Name(child.name.clone()),
                child_id,
                import_snapshot_visibility(child.visibility),
            );
        }
        for value in &module.values {
            let Some(def) = values.get(value.symbol as usize).and_then(|def| *def) else {
                continue;
            };
            state.ctx.record_canonical_value_path(
                def,
                compiled_namespace_symbol_path(&surface.values, value.symbol),
            );
            state.insert_value_with_visibility(
                module_id,
                Name(value.name.clone()),
                def,
                import_snapshot_visibility(value.visibility),
            );
        }
        for ty in &module.types {
            let Some(def) = types.get(ty.symbol as usize).and_then(|def| *def) else {
                continue;
            };
            state.ctx.record_canonical_type_path(
                def,
                compiled_namespace_symbol_path(&surface.types, ty.symbol),
            );
            state.insert_type_with_visibility(
                module_id,
                Name(ty.name.clone()),
                def,
                import_snapshot_visibility(ty.visibility),
            );
        }
    }
}

fn compiled_namespace_symbol_path(symbols: &[CompiledNamespaceSymbol], unit_id: u32) -> Path {
    Path {
        segments: symbols
            .iter()
            .find(|symbol| symbol.unit_id == unit_id)
            .map(|symbol| symbol.path.as_slice())
            .unwrap_or_default()
            .iter()
            .cloned()
            .map(Name)
            .collect(),
    }
}

fn compiled_namespace_module_index(
    surface: &CompiledNamespaceSurface,
    path: &[String],
) -> Option<usize> {
    surface
        .modules
        .iter()
        .position(|module| module.path == path)
}

fn import_snapshot_visibility(visibility: StdInferSnapshotVisibility) -> Visibility {
    match visibility {
        StdInferSnapshotVisibility::My => Visibility::My,
        StdInferSnapshotVisibility::Our => Visibility::Our,
        StdInferSnapshotVisibility::Pub => Visibility::Pub,
    }
}

fn import_snapshot_operator_fixity(fixity: StdInferSnapshotOperatorFixity) -> OperatorFixity {
    match fixity {
        StdInferSnapshotOperatorFixity::Prefix => OperatorFixity::Prefix,
        StdInferSnapshotOperatorFixity::Infix => OperatorFixity::Infix,
        StdInferSnapshotOperatorFixity::Suffix => OperatorFixity::Suffix,
        StdInferSnapshotOperatorFixity::Nullfix => OperatorFixity::Nullfix,
    }
}

fn compiled_namespace_fixity_tag(fixity: StdInferSnapshotOperatorFixity) -> &'static str {
    match fixity {
        StdInferSnapshotOperatorFixity::Prefix => "prefix",
        StdInferSnapshotOperatorFixity::Infix => "infix",
        StdInferSnapshotOperatorFixity::Suffix => "suffix",
        StdInferSnapshotOperatorFixity::Nullfix => "nullfix",
    }
}

fn module_id_for_core_path(state: &LowerState, path: &yulang_typed_ir::Path) -> Option<ModuleId> {
    state.ctx.modules.module_ids().find(|module| {
        path_from_infer_path(&state.ctx.module_path(*module)).segments == path.segments
    })
}

fn compiled_namespace_symbols_for_defs(
    all_paths: &[(Path, crate::ids::DefId)],
    defs: impl IntoIterator<Item = crate::ids::DefId>,
    canonical_paths: &HashMap<crate::ids::DefId, Path>,
    unit_paths: &[Vec<String>],
    out_ids: &mut HashMap<crate::ids::DefId, u32>,
) -> Vec<CompiledNamespaceSymbol> {
    let mut symbols = Vec::new();
    let mut defs = defs.into_iter().collect::<Vec<_>>();
    defs.sort_by_key(|def| def.0);
    defs.dedup();
    for def in defs {
        let path = all_paths
            .iter()
            .filter_map(|(path, current)| {
                (*current == def).then(|| effect_method_hidden_canonical_path(path, unit_paths))?
            })
            .next()
            .or_else(|| canonical_paths.get(&def).cloned())
            .or_else(|| {
                all_paths
                    .iter()
                    .find_map(|(path, current)| (*current == def).then(|| path.clone()))
            });
        let Some(path) = path else {
            continue;
        };
        let unit_id = out_ids.len() as u32;
        out_ids.insert(def, unit_id);
        symbols.push(CompiledNamespaceSymbol {
            path: path.segments.iter().map(|name| name.0.clone()).collect(),
            unit_id,
        });
    }
    symbols.sort_by(|left, right| left.path.cmp(&right.path));
    symbols
}

fn effect_method_hidden_canonical_path(path: &Path, unit_paths: &[Vec<String>]) -> Option<Path> {
    let hidden_name = path.segments.last()?;
    let rest = hidden_name.0.strip_prefix("#effect-method:")?;
    let mut parts = rest.rsplitn(3, ':');
    let _def = parts.next()?;
    let _method = parts.next()?;
    let effect = parts.next()?;
    let mut segments = effect
        .split("::")
        .filter(|segment| !segment.is_empty())
        .map(|segment| Name(segment.to_string()))
        .collect::<Vec<_>>();
    segments.push(hidden_name.clone());
    let candidate = Path { segments };
    path_belongs_to_modules(&snapshot_path_segments(&candidate), unit_paths).then_some(candidate)
}

fn compiled_namespace_module(
    state: &LowerState,
    module: ModuleId,
    value_ids: &HashMap<crate::ids::DefId, u32>,
    type_ids: &HashMap<crate::ids::DefId, u32>,
) -> CompiledNamespaceModule {
    let node = state.ctx.modules.node(module);
    CompiledNamespaceModule {
        path: state
            .ctx
            .module_path(module)
            .segments
            .iter()
            .map(|name| name.0.clone())
            .collect(),
        values: compiled_namespace_module_values(state, module, value_ids),
        operators: compiled_namespace_module_operators(state, module, value_ids),
        types: compiled_namespace_module_types(state, module, type_ids),
        modules: compiled_namespace_module_children(state, module, node),
    }
}

fn compiled_namespace_module_values(
    state: &LowerState,
    module: ModuleId,
    value_ids: &HashMap<crate::ids::DefId, u32>,
) -> Vec<CompiledNamespaceModuleValue> {
    let mut values = state
        .ctx
        .modules
        .node(module)
        .values
        .iter()
        .filter_map(|(name, def)| {
            value_ids
                .get(def)
                .copied()
                .map(|symbol| CompiledNamespaceModuleValue {
                    name: name.0.clone(),
                    symbol,
                    visibility: snapshot_visibility(
                        state.ctx.modules.value_visibility(module, name),
                    ),
                })
        })
        .collect::<Vec<_>>();
    values.sort_by(|left, right| left.name.cmp(&right.name));
    values
}

fn compiled_namespace_module_operators(
    state: &LowerState,
    module: ModuleId,
    value_ids: &HashMap<crate::ids::DefId, u32>,
) -> Vec<CompiledNamespaceModuleOperator> {
    let mut operators = state
        .ctx
        .modules
        .node(module)
        .operator_values
        .iter()
        .filter_map(|((name, fixity), def)| {
            value_ids
                .get(def)
                .copied()
                .map(|symbol| CompiledNamespaceModuleOperator {
                    name: name.0.clone(),
                    fixity: snapshot_operator_fixity(*fixity),
                    symbol,
                    visibility: snapshot_visibility(
                        state.ctx.modules.operator_visibility(module, name, *fixity),
                    ),
                    lazy: state.ctx.is_lazy_operator_def(*def),
                })
        })
        .collect::<Vec<_>>();
    operators.sort_by(|left, right| {
        left.name
            .cmp(&right.name)
            .then_with(|| left.fixity.cmp(&right.fixity))
    });
    operators
}

fn compiled_namespace_module_types(
    state: &LowerState,
    module: ModuleId,
    type_ids: &HashMap<crate::ids::DefId, u32>,
) -> Vec<CompiledNamespaceModuleType> {
    let mut types = state
        .ctx
        .modules
        .node(module)
        .types
        .iter()
        .filter_map(|(name, def)| {
            type_ids
                .get(def)
                .copied()
                .map(|symbol| CompiledNamespaceModuleType {
                    name: name.0.clone(),
                    symbol,
                    visibility: snapshot_visibility(
                        state.ctx.modules.type_visibility(module, name),
                    ),
                })
        })
        .collect::<Vec<_>>();
    types.sort_by(|left, right| left.name.cmp(&right.name));
    types
}

fn compiled_namespace_module_children(
    state: &LowerState,
    parent: ModuleId,
    node: &crate::symbols::ModuleNode,
) -> Vec<CompiledNamespaceModuleChild> {
    let mut modules = node
        .modules
        .iter()
        .map(|(name, module)| CompiledNamespaceModuleChild {
            name: name.0.clone(),
            module_path: state
                .ctx
                .module_path(*module)
                .segments
                .iter()
                .map(|segment| segment.0.clone())
                .collect(),
            visibility: snapshot_visibility(state.ctx.modules.module_visibility(parent, name)),
        })
        .collect::<Vec<_>>();
    modules.sort_by(|left, right| left.name.cmp(&right.name));
    modules
}

fn path_from_infer_path(path: &Path) -> yulang_typed_ir::Path {
    yulang_typed_ir::Path {
        segments: path
            .segments
            .iter()
            .map(|name| yulang_typed_ir::Name(name.0.clone()))
            .collect(),
    }
}

fn snapshot_module_values(
    state: &LowerState,
    module: ModuleId,
    value_ids: &HashMap<crate::ids::DefId, u32>,
) -> Vec<StdInferSnapshotModuleValue> {
    let node = state.ctx.modules.node(module);
    let mut values = node
        .values
        .iter()
        .filter_map(|(name, def)| {
            value_ids
                .get(def)
                .copied()
                .map(|symbol| StdInferSnapshotModuleValue {
                    name: name.0.clone(),
                    symbol,
                    visibility: snapshot_visibility(
                        state.ctx.modules.value_visibility(module, name),
                    ),
                })
        })
        .collect::<Vec<_>>();
    values.sort_by(|lhs, rhs| lhs.name.cmp(&rhs.name));
    values
}

fn snapshot_module_operators(
    state: &LowerState,
    module: ModuleId,
    value_ids: &HashMap<crate::ids::DefId, u32>,
) -> Vec<StdInferSnapshotModuleOperator> {
    let node = state.ctx.modules.node(module);
    let mut operators = node
        .operator_values
        .iter()
        .filter_map(|((name, fixity), def)| {
            value_ids
                .get(def)
                .copied()
                .map(|symbol| StdInferSnapshotModuleOperator {
                    name: name.0.clone(),
                    fixity: snapshot_operator_fixity(*fixity),
                    symbol,
                    visibility: snapshot_visibility(
                        state.ctx.modules.operator_visibility(module, name, *fixity),
                    ),
                })
        })
        .collect::<Vec<_>>();
    operators.sort_by(|lhs, rhs| {
        lhs.name
            .cmp(&rhs.name)
            .then_with(|| lhs.fixity.cmp(&rhs.fixity))
    });
    operators
}

fn snapshot_module_types(
    state: &LowerState,
    module: ModuleId,
    type_ids: &HashMap<crate::ids::DefId, u32>,
) -> Vec<StdInferSnapshotModuleType> {
    let node = state.ctx.modules.node(module);
    let mut types = node
        .types
        .iter()
        .filter_map(|(name, def)| {
            type_ids
                .get(def)
                .copied()
                .map(|symbol| StdInferSnapshotModuleType {
                    name: name.0.clone(),
                    symbol,
                    visibility: snapshot_visibility(
                        state.ctx.modules.type_visibility(module, name),
                    ),
                })
        })
        .collect::<Vec<_>>();
    types.sort_by(|lhs, rhs| lhs.name.cmp(&rhs.name));
    types
}

fn snapshot_module_children(
    state: &LowerState,
    module: ModuleId,
    module_ids: &HashMap<ModuleId, u32>,
) -> Vec<StdInferSnapshotModuleChild> {
    let node = state.ctx.modules.node(module);
    let mut modules = node
        .modules
        .iter()
        .filter_map(|(name, child)| {
            module_ids
                .get(child)
                .copied()
                .map(|module_id| StdInferSnapshotModuleChild {
                    name: name.0.clone(),
                    module: module_id,
                    visibility: snapshot_visibility(
                        state.ctx.modules.module_visibility(module, name),
                    ),
                })
        })
        .collect::<Vec<_>>();
    modules.sort_by(|lhs, rhs| lhs.name.cmp(&rhs.name));
    modules
}

fn snapshot_module_reexports(
    state: &LowerState,
    module: ModuleId,
) -> Vec<StdInferSnapshotReexport> {
    let node = state.ctx.modules.node(module);
    let mut reexports = node
        .reexports
        .iter()
        .map(|(name, reexport)| StdInferSnapshotReexport {
            name: name.0.clone(),
            path: snapshot_path_segments(&reexport.path),
            namespace: snapshot_namespace(reexport.ns),
        })
        .collect::<Vec<_>>();
    reexports.sort_by(|lhs, rhs| lhs.name.cmp(&rhs.name));
    reexports
}

fn snapshot_visibility(visibility: Visibility) -> StdInferSnapshotVisibility {
    match visibility {
        Visibility::My => StdInferSnapshotVisibility::My,
        Visibility::Our => StdInferSnapshotVisibility::Our,
        Visibility::Pub => StdInferSnapshotVisibility::Pub,
    }
}

fn snapshot_namespace(namespace: Namespace) -> StdInferSnapshotNamespace {
    match namespace {
        Namespace::Value => StdInferSnapshotNamespace::Value,
        Namespace::Type => StdInferSnapshotNamespace::Type,
        Namespace::Module => StdInferSnapshotNamespace::Module,
    }
}

fn snapshot_operator_fixity(fixity: OperatorFixity) -> StdInferSnapshotOperatorFixity {
    match fixity {
        OperatorFixity::Prefix => StdInferSnapshotOperatorFixity::Prefix,
        OperatorFixity::Infix => StdInferSnapshotOperatorFixity::Infix,
        OperatorFixity::Suffix => StdInferSnapshotOperatorFixity::Suffix,
        OperatorFixity::Nullfix => StdInferSnapshotOperatorFixity::Nullfix,
    }
}

fn snapshot_path_segments(path: &Path) -> Vec<String> {
    path.segments.iter().map(|name| name.0.clone()).collect()
}

fn path_from_snapshot_segments(segments: &[String]) -> Path {
    Path {
        segments: segments.iter().cloned().map(Name).collect(),
    }
}

#[cfg(test)]
mod tests;
