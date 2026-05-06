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

pub struct ProfiledLoweredSources {
    pub lowered: LoweredSources,
    pub profile: SourceLowerProfile,
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

#[cfg(test)]
mod tests;
