use std::collections::HashMap;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::path::{Path as FsPath, PathBuf};
use std::time::Duration;

use rowan::SyntaxNode;
use serde::{Deserialize, Serialize};
use yulang_parser::parse_module_to_green_with_ops;
use yulang_parser::sink::YulangLanguage;
use yulang_source::{
    CompiledUnitManifest, SourceFile, SourceLoadError, SourceOptions, SourceOrigin, SourceSet,
    collect_source_files_with_options, collect_virtual_source_files_with_options,
};

use crate::lower::primitives::install_builtin_primitives;
use crate::lower::stmt::{finish_lowering, lower_root_in_module};
use crate::lower::{LowerDetailProfile, LowerState};
use crate::profile::{ProfileClock, with_profile_enabled};
use crate::symbols::{ModuleId, Name, Namespace, OperatorFixity, Path, Visibility};
use yulang_core_ir::CoreProgram;

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

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledUnitTypedArtifact {
    pub manifest: CompiledUnitManifest,
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

pub const STD_INFER_SNAPSHOT_FORMAT_VERSION: u32 = 0;

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
    pub has_receiver: bool,
    pub has_default_body: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StdInferSnapshotRoleImpl {
    pub role: Vec<String>,
    pub args: Vec<String>,
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

pub fn build_compiled_typed_artifacts(
    source_set: &SourceSet,
    state: &LowerState,
) -> Vec<CompiledUnitTypedArtifact> {
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

    let mut state = LowerState::new();
    install_builtin_primitives(&mut state);
    import_std_snapshot_module_skeletons(&mut state, &data.modules);

    let modules = import_std_snapshot_modules(&state, &data.modules);
    let values = import_std_snapshot_values(&state, &data.values);
    let types = import_std_snapshot_types(&state, &data.types);
    let refs = import_std_snapshot_refs(data, &values, &modules);
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
        lower_source_set_from_std_state(source_set, state, profile)
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
    lower_source_set_from_std_state(source_set, state, profile)
}

fn lower_source_set_from_std_state(
    source_set: &SourceSet,
    mut state: LowerState,
    mut profile: SourceLowerProfile,
) -> ProfiledLoweredSources {
    let diagnostic_source = source_set
        .entry_files()
        .next()
        .map(|file| file.source.clone())
        .unwrap_or_default();
    for file in source_set
        .files
        .iter()
        .filter(|file| file.origin != SourceOrigin::Std)
    {
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
    lower_root_in_module(state, &root, tir_module_path(file));
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
            source_len: file.source.len(),
            source_hash: source_hash(&file.source),
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
    let mut values = state
        .ctx
        .collect_all_binding_paths()
        .into_iter()
        .map(|(path, def)| {
            (
                def,
                StdInferSnapshotSymbol {
                    path: snapshot_path_segments(&path),
                    snapshot_id: 0,
                },
            )
        })
        .collect::<Vec<_>>();
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
    let mut types = state
        .ctx
        .collect_all_type_paths()
        .into_iter()
        .map(|(path, def)| {
            (
                def,
                StdInferSnapshotSymbol {
                    path: snapshot_path_segments(&path),
                    snapshot_id: 0,
                },
            )
        })
        .collect::<Vec<_>>();
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

fn collect_std_snapshot_schemes(
    state: &LowerState,
    value_ids: &HashMap<crate::ids::DefId, u32>,
) -> Vec<StdInferSnapshotScheme> {
    let compact_schemes = state.infer.compact_schemes.borrow();
    let infer_def_tvs = state.infer.def_tvs.borrow();
    let mut schemes = value_ids
        .iter()
        .filter_map(|(def, symbol)| {
            let rendered = if let Some(scheme) = compact_schemes.get(def) {
                crate::display::dump::format_compact_scheme(scheme)
            } else if let Some(tv) = state.def_tvs.get(def).or_else(|| infer_def_tvs.get(def)) {
                let scheme = crate::simplify::compact::compact_type_var(&state.infer, *tv);
                crate::display::dump::format_compact_scheme(&scheme)
            } else {
                return None;
            };
            Some(StdInferSnapshotScheme {
                symbol: *symbol,
                rendered,
            })
        })
        .collect::<Vec<_>>();
    schemes.sort_by(|lhs, rhs| lhs.symbol.cmp(&rhs.symbol));
    schemes
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
            Some(StdInferSnapshotEffectMethod {
                name: method.name.0.clone(),
                effect: snapshot_path_segments(&method.effect),
                symbol,
                module,
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
    source_modules: &[yulang_core_ir::Path],
    value_paths: &[(Path, crate::ids::DefId)],
    type_paths: &[(Path, crate::ids::DefId)],
) -> CompiledNamespaceSurface {
    let module_ids = source_modules
        .iter()
        .filter_map(|module_path| module_id_for_core_path(state, module_path))
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
        &mut value_defs,
    );
    let types = compiled_namespace_symbols_for_defs(
        type_paths,
        module_ids
            .iter()
            .flat_map(|module| state.ctx.modules.node(*module).types.values().copied()),
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

fn merge_compiled_namespace_surfaces<'a>(
    surfaces: impl IntoIterator<Item = &'a CompiledNamespaceSurface>,
) -> CompiledNamespaceSurface {
    let mut modules = Vec::new();
    let mut values = Vec::new();
    let mut types = Vec::new();
    for surface in surfaces {
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
    values.sort_by(|left, right| left.path.cmp(&right.path));
    types.sort_by(|left, right| left.path.cmp(&right.path));
    CompiledNamespaceSurface {
        modules,
        values,
        types,
    }
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
            let path = yulang_core_ir::Path {
                segments: module
                    .path
                    .iter()
                    .cloned()
                    .map(yulang_core_ir::Name)
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
    for symbol in &surface.values {
        let Some(slot) = out.get_mut(symbol.unit_id as usize) else {
            continue;
        };
        if slot.is_some() {
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
    for symbol in &surface.types {
        let Some(slot) = out.get_mut(symbol.unit_id as usize) else {
            continue;
        };
        if slot.is_some() {
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
            state.insert_value_with_visibility(
                module_id,
                Name(value.name.clone()),
                def,
                import_snapshot_visibility(value.visibility),
            );
            state.ctx.record_canonical_value_path(
                def,
                compiled_namespace_symbol_path(&surface.values, value.symbol),
            );
        }
        for ty in &module.types {
            let Some(def) = types.get(ty.symbol as usize).and_then(|def| *def) else {
                continue;
            };
            state.insert_type_with_visibility(
                module_id,
                Name(ty.name.clone()),
                def,
                import_snapshot_visibility(ty.visibility),
            );
            state.ctx.record_canonical_type_path(
                def,
                compiled_namespace_symbol_path(&surface.types, ty.symbol),
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

fn module_id_for_core_path(state: &LowerState, path: &yulang_core_ir::Path) -> Option<ModuleId> {
    state.ctx.modules.module_ids().find(|module| {
        path_from_infer_path(&state.ctx.module_path(*module)).segments == path.segments
    })
}

fn compiled_namespace_symbols_for_defs(
    all_paths: &[(Path, crate::ids::DefId)],
    defs: impl IntoIterator<Item = crate::ids::DefId>,
    out_ids: &mut HashMap<crate::ids::DefId, u32>,
) -> Vec<CompiledNamespaceSymbol> {
    let mut symbols = Vec::new();
    let mut defs = defs.into_iter().collect::<Vec<_>>();
    defs.sort_by_key(|def| def.0);
    defs.dedup();
    for def in defs {
        let Some(path) = all_paths
            .iter()
            .find_map(|(path, current)| (*current == def).then_some(path))
        else {
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

fn path_from_infer_path(path: &Path) -> yulang_core_ir::Path {
    yulang_core_ir::Path {
        segments: path
            .segments
            .iter()
            .map(|name| yulang_core_ir::Name(name.0.clone()))
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

fn source_hash(source: &str) -> u64 {
    let mut hasher = DefaultHasher::new();
    source.hash(&mut hasher);
    hasher.finish()
}

#[cfg(test)]
mod tests;
