use std::collections::HashMap;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::path::{Path as FsPath, PathBuf};
use std::time::Duration;

use rowan::SyntaxNode;
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
use crate::symbols::{Name, Path};

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
    std_states: HashMap<StdSourceCacheKey, LowerState>,
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

    let mut profile = SourceLowerProfile {
        files: source_set.files.len(),
        entry_files: source_set.files_with_origin(SourceOrigin::Entry).count(),
        std_files: source_set.files_with_origin(SourceOrigin::Std).count(),
        user_files: source_set.files_with_origin(SourceOrigin::User).count(),
        ..SourceLowerProfile::default()
    };
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

fn lower_source_set_cached_inner(
    source_set: &SourceSet,
    cache: &mut SourceLowerCache,
) -> ProfiledLoweredSources {
    if source_set.std_files().next().is_none() {
        let mut lowered = lower_source_set_profiled(source_set);
        lowered.profile.std_cache.disabled += 1;
        return lowered;
    }

    let diagnostic_source = source_set
        .entry_files()
        .next()
        .map(|file| file.source.clone())
        .unwrap_or_default();
    let mut profile = SourceLowerProfile {
        files: source_set.files.len(),
        entry_files: source_set.files_with_origin(SourceOrigin::Entry).count(),
        std_files: source_set.files_with_origin(SourceOrigin::Std).count(),
        user_files: source_set.files_with_origin(SourceOrigin::User).count(),
        ..SourceLowerProfile::default()
    };
    let mut state = cache.std_state(source_set, &mut profile);
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
        if let Some(state) = self.covering_std_state(&key) {
            profile.std_cache.hits += 1;
            let clone_start = ProfileClock::now();
            let cloned = state.clone();
            profile.std_cache.clone += clone_start.elapsed();
            return cloned;
        }

        profile.std_cache.misses += 1;
        let build_start = ProfileClock::now();
        let mut state = LowerState::new();
        install_builtin_primitives(&mut state);
        for file in source_set.std_files() {
            lower_source_file_inner(file, &mut state, profile);
        }
        profile.std_cache.build += build_start.elapsed();
        let clone_start = ProfileClock::now();
        self.std_states.insert(key, state.clone());
        profile.std_cache.clone += clone_start.elapsed();
        state
    }

    fn covering_std_state(&self, key: &StdSourceCacheKey) -> Option<&LowerState> {
        self.std_states.get(key).or_else(|| {
            self.std_states
                .iter()
                .find_map(|(cached, state)| cached.covers(key).then_some(state))
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct StdSourceCacheKey {
    files: Vec<StdSourceFileCacheKey>,
}

impl StdSourceCacheKey {
    fn from_source_set(source_set: &SourceSet) -> Self {
        Self {
            files: source_set
                .std_files()
                .map(StdSourceFileCacheKey::from_file)
                .collect(),
        }
    }

    fn covers(&self, requested: &StdSourceCacheKey) -> bool {
        requested.files.iter().all(|file| self.files.contains(file))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

fn source_hash(source: &str) -> u64 {
    let mut hasher = DefaultHasher::new();
    source.hash(&mut hasher);
    hasher.finish()
}

#[cfg(test)]
mod tests;
