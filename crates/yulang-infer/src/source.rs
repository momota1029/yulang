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
    pub effect_operations: Vec<StdInferSnapshotEffectOperation>,
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
    build_std_infer_snapshot(source_set).map(|snapshot| snapshot.data().clone())
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
            effect_operations: collect_std_snapshot_effect_operations(state),
        }
    }
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

fn source_hash(source: &str) -> u64 {
    let mut hasher = DefaultHasher::new();
    source.hash(&mut hasher);
    hasher.finish()
}

#[cfg(test)]
mod tests;
