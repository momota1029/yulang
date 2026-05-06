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
    SourceFile, SourceLoadError, SourceOptions, SourceOrigin, SourceSet,
    collect_source_files_with_options, collect_virtual_source_files_with_options,
};

use crate::lower::primitives::install_builtin_primitives;
use crate::lower::stmt::{finish_lowering, lower_root_in_module};
use crate::lower::{LowerDetailProfile, LowerState};
use crate::profile::{ProfileClock, with_profile_enabled};
use crate::symbols::{ModuleId, Name, Namespace, OperatorFixity, Path, Visibility};

pub struct LoweredSources {
    pub state: LowerState,
    pub diagnostic_source: String,
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

pub struct StdInferSnapshotImport {
    pub state: LowerState,
    pub modules: Vec<Option<ModuleId>>,
    pub values: Vec<Option<crate::ids::DefId>>,
    pub types: Vec<Option<crate::ids::DefId>>,
    pub refs: StdInferSnapshotImportRefs,
    pub missing: StdInferSnapshotImportMissing,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct StdInferSnapshotImportRefs {
    pub schemes: Vec<Option<crate::ids::DefId>>,
    pub role_methods: Vec<Option<crate::ids::DefId>>,
    pub role_impl_members: Vec<Vec<Option<crate::ids::DefId>>>,
    pub effect_methods: Vec<Option<crate::ids::DefId>>,
    pub effect_method_modules: Vec<Option<ModuleId>>,
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
