//! 実ファイルから新 `sources` / `infer` route へ渡す source set を作る入口。
//!
//! `sources` crate は in-memory source set の parse/load 層に留め、FS traversal と
//! 実験中の std 取り込みはここへ置く。

mod collector;
mod compilation_units;
mod format;
mod realm_install;
mod std_sources;

use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;
use std::fmt::Write as _;
use std::fs;
use std::io;
use std::path::{Path as FsPath, PathBuf};

use sources::{ModuleLoadRequest, Name, Path, SourceFile};

use crate::stdlib::{
    YULANG_STD_ENV, default_versioned_std_root, embedded_std_files, env_std_root,
    install_embedded_std, installed_versioned_std_root,
};
use crate::time::{Duration, Instant};

#[cfg(test)]
mod tests;

use collector::*;
pub use compilation_units::{
    SourceCompilationUnit, SourceCompilationUnits, SourceUnitCacheSelection,
    SourceUnitLoweringInputError, source_compilation_units, source_unit_closure_file_indices,
    source_unit_closure_lowering_source_files, source_unit_lowering_source_files,
};
pub(crate) use compilation_units::{
    source_unit_closure_lowering_loaded_files, source_unit_lowering_loaded_files,
};
use format::*;
pub(crate) use realm_install::{
    InstalledLocalRealmBand, installed_local_import_module_path, resolve_installed_local_realm_band,
};
pub use realm_install::{RealmInstallError, RealmInstallOutput, install_local_realm};
use std_sources::*;

pub use format::{format_run_mono_values, format_run_mono_values_with_labels};
pub use sources::SourceRange;

pub const IMPLICIT_PRELUDE_IMPORT: &str = "use std::prelude::*\n";
pub(crate) const IMPLICIT_STD_MODULE_DECL: &str = "mod std;\n";
pub const IMPLICIT_STD_SOURCE_PREFIX_LEN: usize =
    IMPLICIT_PRELUDE_IMPORT.len() + IMPLICIT_STD_MODULE_DECL.len();

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct StdSourceOptions {
    pub std_root: Option<PathBuf>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceCollectionCache {
    artifact_cache: crate::cache::ArtifactCache,
}

impl SourceCollectionCache {
    pub fn new(artifact_cache: crate::cache::ArtifactCache) -> Self {
        Self { artifact_cache }
    }

    fn cached_current_realm_band_file(
        &self,
        source_file: &CollectedSource,
        band: &Path,
        expected_path: &FsPath,
    ) -> Option<(PathBuf, String)> {
        let source_realm = sources::local_realm_id(&source_file.path);
        for request in &source_file.resolution_imports {
            if crate::cache::current_realm_import_band_path(request).as_ref() != Some(band) {
                continue;
            }
            let key = crate::cache::realm_resolution_cache_key(source_file, request);
            let Ok(Some(artifact)) = self
                .artifact_cache
                .read_realm_resolution_artifact(&source_realm, key)
            else {
                continue;
            };
            let Some(path) = checked_current_realm_resolution_path(
                &source_realm,
                band,
                expected_path,
                &artifact,
            ) else {
                continue;
            };
            if let Some(source) = cached_target_source_if_matches(&path, band, &artifact.target) {
                return Some((path, source));
            }
        }
        None
    }

    fn cached_installed_local_realm_band_file(
        &self,
        source_file: &CollectedSource,
        request: &sources::UseImport,
        resolved: &InstalledLocalRealmBand,
    ) -> Option<(PathBuf, String)> {
        let source_realm = sources::local_realm_id(&source_file.path);
        let key = crate::cache::realm_resolution_cache_key(source_file, request);
        let Ok(Some(artifact)) = self
            .artifact_cache
            .read_realm_resolution_artifact(&source_realm, key)
        else {
            return None;
        };
        if artifact.source_realm != source_realm {
            return None;
        }
        if artifact.request != *request {
            return None;
        }
        if artifact.target.realm != resolved.realm
            || artifact.target.band_path != resolved.band_path
            || artifact.target.module_path != resolved.module_path
        {
            return None;
        }
        let path = PathBuf::from(&artifact.target.source_path);
        if canonicalize_for_dedupe(&path) != canonicalize_for_dedupe(&resolved.source_path) {
            return None;
        }
        cached_target_source_if_matches(&path, &resolved.module_path, &artifact.target)
            .map(|source| (path, source))
    }
}

fn checked_current_realm_resolution_path(
    source_realm: &sources::ResolvedRealmId,
    band: &Path,
    expected_path: &FsPath,
    artifact: &crate::cache::CachedRealmResolutionArtifact,
) -> Option<PathBuf> {
    if &artifact.source_realm != source_realm {
        return None;
    }
    if &artifact.target.realm != source_realm {
        return None;
    }
    if &artifact.target.band_path != band || &artifact.target.module_path != band {
        return None;
    }

    let path = PathBuf::from(&artifact.target.source_path);
    if canonicalize_for_dedupe(&path) != canonicalize_for_dedupe(expected_path) {
        return None;
    }
    Some(path)
}

fn cached_target_source_if_matches(
    path: &FsPath,
    module_path: &Path,
    target: &crate::cache::CachedRealmResolutionTarget,
) -> Option<String> {
    let Ok(source) = fs::read_to_string(path) else {
        return None;
    };
    if source.len() != target.source_len {
        return None;
    }
    let metadata = discover_source_header_metadata(module_path, &source);
    let file = CollectedSource::with_band_path_and_resolution_imports(
        path.to_path_buf(),
        module_path.clone(),
        target.band_path.clone(),
        source,
        metadata.resolution_imports,
    );
    (crate::cache::source_file_hash(&file) == target.source_hash).then_some(file.source)
}

/// entry file から local module file を読み、1つの module tree として poly dump を返す。
pub fn dump_poly_from_entry(entry: impl AsRef<FsPath>) -> Result<DumpPolyOutput, RouteError> {
    dump_poly_from_sources(collect_local_sources(entry)?, DumpPolyKind::Compact)
}

/// entry file から local module file を読み、raw poly debug dump を返す。
pub fn dump_poly_raw_from_entry(entry: impl AsRef<FsPath>) -> Result<DumpPolyOutput, RouteError> {
    dump_poly_from_sources(collect_local_sources(entry)?, DumpPolyKind::Raw)
}

/// entry file から local module file を読み、mono dump を返す。
pub fn dump_mono_from_entry(entry: impl AsRef<FsPath>) -> Result<DumpMonoOutput, RouteError> {
    dump_mono_from_sources(collect_local_sources(entry)?)
}

/// entry file から local module file を読み、mono runtime で root を実行する。
pub fn run_mono_from_entry(entry: impl AsRef<FsPath>) -> Result<RunMonoOutput, RouteError> {
    run_mono_from_sources(collect_local_sources(entry)?)
}

/// entry file から local module file を読み、control VM で root を実行する。
pub fn run_control_from_entry(entry: impl AsRef<FsPath>) -> Result<RunControlOutput, RouteError> {
    run_control_from_sources(collect_local_sources(entry)?)
}

/// entry file から local module file を読み、control VM artifact 用 IR を作る。
pub fn build_control_from_entry(
    entry: impl AsRef<FsPath>,
) -> Result<BuildControlOutput, RouteError> {
    build_control_from_sources(collect_local_sources(entry)?)
}

/// 収集済み source set から control VM artifact 用 IR を作る。
///
/// CLI の artifact cache は source collection を cache の外に置くので、この入口から
/// 推論・単相化・control lowering を再利用単位にする。
pub fn build_control_from_collected_sources(
    files: Vec<CollectedSource>,
) -> Result<BuildControlOutput, RouteError> {
    build_control_from_sources(files)
}

/// 収集済み source set から principal poly artifact を作る。
///
/// `BuildPolyOutput` は infer の mutable graph ではなく、後段が読む `poly::Arena` と
/// 表示用 lowering error だけを持つ。CLI の `.yuir` cache はこの出力を保存する。
pub fn build_poly_from_collected_sources(
    files: Vec<CollectedSource>,
) -> Result<BuildPolyOutput, RouteError> {
    build_poly_from_sources(files)
}

pub fn build_poly_and_compiled_unit_from_collected_sources(
    files: Vec<CollectedSource>,
) -> Result<BuildPolyAndCompiledUnitOutput, RouteError> {
    let loaded = load_collected_sources(files.clone());
    let lowering = infer::lowering::lower_loaded_files(&loaded).map_err(RouteError::Lower)?;
    let errors = lowering
        .errors
        .iter()
        .map(format_body_lowering_error)
        .collect::<Vec<_>>();
    let compiled_unit = crate::cache::compiled_unit_artifact_from_lowering(
        &files,
        &loaded,
        &lowering,
        errors.clone(),
    );
    let host_manifest = host_manifest_from_compiled_unit_artifact(&compiled_unit)?;
    Ok(BuildPolyAndCompiledUnitOutput {
        poly: BuildPolyOutput {
            arena: lowering.session.poly,
            labels: lowering.labels,
            host_manifest: Some(host_manifest),
            file_count: loaded.len(),
            errors,
        },
        compiled_unit,
    })
}

pub fn build_poly_from_compiled_unit_artifact(
    artifact: crate::cache::CachedCompiledUnitArtifact,
) -> BuildPolyOutput {
    BuildPolyOutput {
        arena: artifact.runtime.arena,
        labels: artifact.runtime.labels,
        host_manifest: None,
        file_count: artifact.manifest.files.len(),
        errors: artifact.errors,
    }
}

pub fn build_poly_from_compiled_unit_prefix_and_collected_sources(
    prefix: crate::cache::CachedCompiledUnitArtifact,
    suffix: Vec<CollectedSource>,
) -> Result<BuildPolyOutput, RouteError> {
    let output = lower_compiled_unit_prefix_suffix(prefix, suffix)?;
    let host_manifest = host_manifest_from_lowering(&output.lowering)?;
    Ok(BuildPolyOutput {
        arena: output.lowering.session.poly,
        labels: output.lowering.labels,
        host_manifest: Some(host_manifest),
        file_count: output.file_count,
        errors: output.errors,
    })
}

/// Build the full poly output and materialize the matching full-source
/// compiled-unit artifact after importing a cached dependency prefix.
///
/// `files` is the complete source set for the current run. `suffix` is the
/// subset not covered by `prefix`.
pub fn build_poly_and_compiled_unit_from_compiled_unit_prefix_and_collected_sources(
    prefix: crate::cache::CachedCompiledUnitArtifact,
    files: Vec<CollectedSource>,
    suffix: Vec<CollectedSource>,
) -> Result<BuildPolyAndCompiledUnitOutput, RouteError> {
    let output = lower_compiled_unit_prefix_suffix(prefix, suffix)?;
    debug_assert_eq!(output.file_count, files.len());
    let suffix_syntax = sources::CompiledSyntaxSurface::from_loaded_files(&output.loaded);
    let syntax =
        sources::CompiledSyntaxSurface::merge_prefixes([&output.prefix_syntax, &suffix_syntax])
            .map_err(RouteError::SyntaxMerge)?;
    let compiled_unit = crate::cache::compiled_unit_artifact_from_lowering_with_syntax_and_key(
        &files,
        syntax,
        &output.lowering,
        output.errors.clone(),
        crate::cache::source_cache_key(&files),
    );
    let host_manifest = host_manifest_from_compiled_unit_artifact(&compiled_unit)?;
    Ok(BuildPolyAndCompiledUnitOutput {
        poly: BuildPolyOutput {
            arena: output.lowering.session.poly,
            labels: output.lowering.labels,
            host_manifest: Some(host_manifest),
            file_count: output.file_count,
            errors: output.errors,
        },
        compiled_unit,
    })
}

struct CompiledUnitPrefixLowering {
    prefix_syntax: sources::CompiledSyntaxSurface,
    loaded: Vec<sources::LoadedFile>,
    lowering: infer::lowering::BodyLowering,
    errors: Vec<String>,
    file_count: usize,
}

fn lower_compiled_unit_prefix_suffix(
    prefix: crate::cache::CachedCompiledUnitArtifact,
    suffix: Vec<CollectedSource>,
) -> Result<CompiledUnitPrefixLowering, RouteError> {
    let crate::cache::CachedCompiledUnitArtifact {
        manifest,
        syntax,
        namespace,
        lowering,
        typed: _,
        runtime,
        external_runtime: _,
        errors: prefix_errors,
    } = prefix;
    let suffix_file_count = suffix.len();
    let (suffix_files, suffix_bands) = collected_source_files_and_band_paths(suffix);
    let loaded =
        sources::load_suffix_with_syntax_prefix_and_band_paths(&syntax, suffix_files, suffix_bands);
    let lowering_prefix = infer::lowering::BodyLoweringPrefix::from_compiled_unit_surfaces(
        &namespace, &lowering, &runtime,
    )
    .ok_or(infer::LoadedFilesError::MissingRoot)
    .map_err(RouteError::Lower)?;
    let lowering = infer::lowering::lower_loaded_files_with_prefix(&lowering_prefix, &loaded)
        .map_err(RouteError::Lower)?;
    let mut errors = prefix_errors;
    errors.extend(lowering.errors.iter().map(format_body_lowering_error));
    Ok(CompiledUnitPrefixLowering {
        prefix_syntax: syntax,
        loaded,
        lowering,
        errors,
        file_count: manifest.files.len() + suffix_file_count,
    })
}

fn host_manifest_from_lowering(
    lowering: &infer::lowering::BodyLowering,
) -> Result<poly::host_manifest::HostActManifest, RouteError> {
    let namespace = infer::CompiledNamespaceSurface::from_module_table(&lowering.modules);
    let lowering_surface =
        infer::CompiledLoweringSurface::from_module_table(&lowering.modules, &namespace);
    let typed = infer::CompiledTypedSurface::from_lowering(lowering, &namespace);
    infer::host_acts::host_act_manifest_from_compiled(&namespace, &lowering_surface, &typed)
        .map_err(RouteError::HostActManifest)
}

fn host_manifest_from_compiled_unit_artifact(
    artifact: &crate::cache::CachedCompiledUnitArtifact,
) -> Result<poly::host_manifest::HostActManifest, RouteError> {
    infer::host_acts::host_act_manifest_from_compiled(
        &artifact.namespace,
        &artifact.lowering,
        &artifact.typed,
    )
    .map_err(RouteError::HostActManifest)
}

/// principal poly artifact から control VM artifact 用 IR を作る。
pub fn build_control_from_poly_output(
    output: &BuildPolyOutput,
) -> Result<BuildControlOutput, RouteError> {
    output.ensure_runtime_ready()?;
    let mut specialized = specialize::specialize_with_runtime_evidence(&output.arena)
        .map_err(RouteError::Specialize)?;
    specialized.runtime_evidence.host_manifest = output.host_manifest.clone();
    specialized
        .runtime_evidence
        .attach_static_routes(&output.arena);
    let program = control_vm::lower(&specialized.program).map_err(RouteError::ControlLower)?;
    Ok(BuildControlOutput {
        program,
        runtime_evidence: specialized.runtime_evidence,
        labels: output.labels.clone(),
        file_count: output.file_count,
        errors: output.errors.clone(),
    })
}

/// すでに lower 済みの control VM program を実行し、通常の route output に包む。
pub fn run_built_control_program(
    program: &control_vm::Program,
    file_count: usize,
    errors: Vec<String>,
) -> Result<RunControlOutput, RouteError> {
    run_built_control_program_with_labels(program, file_count, errors, None)
}

pub fn run_built_control_program_with_labels(
    program: &control_vm::Program,
    file_count: usize,
    errors: Vec<String>,
    labels: Option<&poly::dump::DumpLabels>,
) -> Result<RunControlOutput, RouteError> {
    reject_runtime_lowering_errors(&errors)?;
    let mut stdout = String::new();
    let (values, stats, runtime_timings) =
        control_vm::run_program_with_host_stats_and_timings(program, &mut |path, payload| {
            handle_control_host_effect(path, payload, &mut stdout)
        })
        .map_err(RouteError::Control)?;
    let format_start = Instant::now();
    let text = format_run_control_values_with_labels(&values, labels);
    let root_format = format_start.elapsed();
    Ok(RunControlOutput {
        text,
        file_count,
        errors,
        values,
        stdout,
        stats,
        timings: ControlRunTimings {
            validate: runtime_timings.validate,
            init: runtime_timings.init,
            execute: runtime_timings.execute,
            root_format,
        },
    })
}

fn handle_control_host_effect(
    path: &[String],
    payload: &control_vm::Value,
    stdout: &mut String,
) -> Option<control_vm::Value> {
    if path == ["std", "io", "console", "out", "write"] {
        push_control_host_string_payload(payload, stdout)?;
        return Some(control_vm::Value::Unit);
    }
    None
}

fn push_control_host_string_payload(value: &control_vm::Value, out: &mut String) -> Option<()> {
    match value {
        control_vm::Value::Str(value) => {
            value.push_to_string(out);
            Some(())
        }
        control_vm::Value::Marked { value, .. } => push_control_host_string_payload(value, out),
        _ => None,
    }
}

/// entry file と近場の `lib/std.yu` を読み、implicit prelude 付きで poly dump を返す。
///
/// デバッグ用の暫定入口。install 済み std ではなく、entry の親から上へ辿って見つかる
/// `lib/std.yu` を優先する。
pub fn dump_poly_from_entry_with_std(
    entry: impl AsRef<FsPath>,
) -> Result<DumpPolyOutput, RouteError> {
    dump_poly_from_entry_with_std_options(entry, &StdSourceOptions::default())
}

pub fn dump_poly_from_entry_with_std_options(
    entry: impl AsRef<FsPath>,
    options: &StdSourceOptions,
) -> Result<DumpPolyOutput, RouteError> {
    dump_poly_from_sources(
        collect_local_sources_with_std_options(entry, options)?,
        DumpPolyKind::Compact,
    )
}

/// entry file と近場の `lib/std.yu` を読み、implicit prelude 付きで raw poly debug dump を返す。
pub fn dump_poly_raw_from_entry_with_std(
    entry: impl AsRef<FsPath>,
) -> Result<DumpPolyOutput, RouteError> {
    dump_poly_raw_from_entry_with_std_options(entry, &StdSourceOptions::default())
}

pub fn dump_poly_raw_from_entry_with_std_options(
    entry: impl AsRef<FsPath>,
    options: &StdSourceOptions,
) -> Result<DumpPolyOutput, RouteError> {
    dump_poly_from_sources(
        collect_local_sources_with_std_options(entry, options)?,
        DumpPolyKind::Raw,
    )
}

/// entry file と近場の `lib/std.yu` を読み、implicit prelude 付きで mono dump を返す。
pub fn dump_mono_from_entry_with_std(
    entry: impl AsRef<FsPath>,
) -> Result<DumpMonoOutput, RouteError> {
    dump_mono_from_entry_with_std_options(entry, &StdSourceOptions::default())
}

pub fn dump_mono_from_entry_with_std_options(
    entry: impl AsRef<FsPath>,
    options: &StdSourceOptions,
) -> Result<DumpMonoOutput, RouteError> {
    dump_mono_from_sources(collect_local_sources_with_std_options(entry, options)?)
}

/// entry file と近場の `lib/std.yu` を読み、implicit prelude 付きで mono runtime を実行する。
pub fn run_mono_from_entry_with_std(
    entry: impl AsRef<FsPath>,
) -> Result<RunMonoOutput, RouteError> {
    run_mono_from_entry_with_std_options(entry, &StdSourceOptions::default())
}

pub fn run_mono_from_entry_with_std_options(
    entry: impl AsRef<FsPath>,
    options: &StdSourceOptions,
) -> Result<RunMonoOutput, RouteError> {
    run_mono_from_sources(collect_local_sources_with_std_options(entry, options)?)
}

/// entry file と近場の `lib/std.yu` を読み、implicit prelude 付きで control VM を実行する。
pub fn run_control_from_entry_with_std(
    entry: impl AsRef<FsPath>,
) -> Result<RunControlOutput, RouteError> {
    run_control_from_entry_with_std_options(entry, &StdSourceOptions::default())
}

pub fn run_control_from_entry_with_std_options(
    entry: impl AsRef<FsPath>,
    options: &StdSourceOptions,
) -> Result<RunControlOutput, RouteError> {
    run_control_from_sources(collect_local_sources_with_std_options(entry, options)?)
}

/// entry file と近場の `lib/std.yu` を読み、control VM artifact 用 IR を作る。
pub fn build_control_from_entry_with_std(
    entry: impl AsRef<FsPath>,
) -> Result<BuildControlOutput, RouteError> {
    build_control_from_entry_with_std_options(entry, &StdSourceOptions::default())
}

pub fn build_control_from_entry_with_std_options(
    entry: impl AsRef<FsPath>,
    options: &StdSourceOptions,
) -> Result<BuildControlOutput, RouteError> {
    build_control_from_sources(collect_local_sources_with_std_options(entry, options)?)
}

/// entry file から local module file を読み、dump なしで型付け状況を集計する。
pub fn check_poly_from_entry(entry: impl AsRef<FsPath>) -> Result<CheckPolyOutput, RouteError> {
    let total_start = Instant::now();
    let collect_start = Instant::now();
    let files = collect_local_sources(entry)?;
    let collect = collect_start.elapsed();
    check_poly_from_sources(
        files,
        collect,
        total_start,
        CheckPolyKind::All {
            title: "check-poly",
        },
    )
}

/// entry file と近場の `lib/std.yu` を読み、dump なしで型付け状況を集計する。
pub fn check_poly_from_entry_with_std(
    entry: impl AsRef<FsPath>,
) -> Result<CheckPolyOutput, RouteError> {
    check_poly_from_entry_with_std_options(entry, &StdSourceOptions::default())
}

pub fn check_poly_from_entry_with_std_options(
    entry: impl AsRef<FsPath>,
    options: &StdSourceOptions,
) -> Result<CheckPolyOutput, RouteError> {
    let total_start = Instant::now();
    let collect_start = Instant::now();
    let files = collect_local_sources_with_std_options(entry, options)?;
    let collect = collect_start.elapsed();
    check_poly_from_sources(
        files,
        collect,
        total_start,
        CheckPolyKind::All {
            title: "check-poly-std",
        },
    )
}

pub fn analyze_entry_source_with_std_options(
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
    options: &StdSourceOptions,
) -> Result<AnalyzeSourceOutput, RouteError> {
    Ok(source_text_analysis_with_std_options(entry, source, options)?.analyze())
}

pub fn analyze_entry_source(
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
) -> Result<AnalyzeSourceOutput, RouteError> {
    Ok(source_text_analysis(entry, source)?.analyze())
}

pub(crate) fn source_text_analysis_with_std_options(
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
    options: &StdSourceOptions,
) -> Result<SourceTextAnalysis, RouteError> {
    let context =
        collect_local_source_text_with_std_context(entry.as_ref(), source.into(), options)?;
    source_text_analysis_from_files(
        context.files,
        context.focus_module,
        context.byte_offset_adjust,
    )
}

pub(crate) fn source_text_analysis(
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
) -> Result<SourceTextAnalysis, RouteError> {
    source_text_analysis_from_files(
        collect_local_source_text(entry, source.into())?,
        Path::default(),
        0,
    )
}

pub fn hover_entry_source_with_std_options(
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
    byte_offset: usize,
    options: &StdSourceOptions,
) -> Result<Option<SourceHover>, RouteError> {
    let context =
        collect_local_source_text_with_std_context(entry.as_ref(), source.into(), options)?;
    hover_from_sources(
        context.files,
        byte_offset + context.byte_offset_adjust,
        &context.focus_module,
    )
}

pub fn hover_entry_source(
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
    byte_offset: usize,
) -> Result<Option<SourceHover>, RouteError> {
    hover_from_sources(
        collect_local_source_text(entry, source.into())?,
        byte_offset,
        &Path::default(),
    )
}

pub fn definition_entry_source_with_std_options(
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
    byte_offset: usize,
    options: &StdSourceOptions,
) -> Result<Option<SourceDefinition>, RouteError> {
    let context =
        collect_local_source_text_with_std_context(entry.as_ref(), source.into(), options)?;
    definition_from_sources(
        context.files,
        byte_offset + context.byte_offset_adjust,
        &context.focus_module,
    )
}

pub fn definition_entry_source(
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
    byte_offset: usize,
) -> Result<Option<SourceDefinition>, RouteError> {
    definition_from_sources(
        collect_local_source_text(entry, source.into())?,
        byte_offset,
        &Path::default(),
    )
}

pub fn references_entry_source_with_std_options(
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
    byte_offset: usize,
    include_declaration: bool,
    options: &StdSourceOptions,
) -> Result<Vec<SourceLocation>, RouteError> {
    let context =
        collect_local_source_text_with_std_context(entry.as_ref(), source.into(), options)?;
    references_from_sources(
        context.files,
        byte_offset + context.byte_offset_adjust,
        &context.focus_module,
        include_declaration,
    )
}

pub fn references_entry_source(
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
    byte_offset: usize,
    include_declaration: bool,
) -> Result<Vec<SourceLocation>, RouteError> {
    references_from_sources(
        collect_local_source_text(entry, source.into())?,
        byte_offset,
        &Path::default(),
        include_declaration,
    )
}

pub fn prepare_rename_entry_source_with_std_options(
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
    byte_offset: usize,
    options: &StdSourceOptions,
) -> Result<Option<SourceRange>, RouteError> {
    let context =
        collect_local_source_text_with_std_context(entry.as_ref(), source.into(), options)?;
    prepare_rename_from_sources(
        context.files,
        byte_offset + context.byte_offset_adjust,
        &context.focus_module,
    )
}

pub fn prepare_rename_entry_source(
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
    byte_offset: usize,
) -> Result<Option<SourceRange>, RouteError> {
    prepare_rename_from_sources(
        collect_local_source_text(entry, source.into())?,
        byte_offset,
        &Path::default(),
    )
}

pub fn rename_entry_source_with_std_options(
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
    byte_offset: usize,
    new_name: &str,
    options: &StdSourceOptions,
) -> Result<Option<SourceRename>, RouteError> {
    let context =
        collect_local_source_text_with_std_context(entry.as_ref(), source.into(), options)?;
    rename_from_sources(
        context.files,
        byte_offset + context.byte_offset_adjust,
        &context.focus_module,
        new_name,
    )
}

pub fn rename_entry_source(
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
    byte_offset: usize,
    new_name: &str,
) -> Result<Option<SourceRename>, RouteError> {
    rename_from_sources(
        collect_local_source_text(entry, source.into())?,
        byte_offset,
        &Path::default(),
        new_name,
    )
}

/// entry file と近場の `lib/std.yu` を読み、指定 module の型付け状況だけを集計する。
pub fn check_poly_from_entry_with_std_in_module(
    entry: impl AsRef<FsPath>,
    module: &str,
) -> Result<CheckPolyOutput, RouteError> {
    check_poly_from_entry_with_std_in_module_options(entry, module, &StdSourceOptions::default())
}

pub fn check_poly_from_entry_with_std_in_module_options(
    entry: impl AsRef<FsPath>,
    module: &str,
    options: &StdSourceOptions,
) -> Result<CheckPolyOutput, RouteError> {
    let total_start = Instant::now();
    let collect_start = Instant::now();
    let files = collect_local_sources_with_std_options(entry, options)?;
    let collect = collect_start.elapsed();
    check_poly_from_sources(
        files,
        collect,
        total_start,
        CheckPolyKind::Module {
            title: "check-poly-std-in",
            module: parse_dump_module_path(module)?,
        },
    )
}

/// entry file と近場の `lib/std.yu` を読み、指定 module 直下の値だけを poly dump する。
pub fn dump_poly_from_entry_with_std_in_module(
    entry: impl AsRef<FsPath>,
    module: &str,
) -> Result<DumpPolyOutput, RouteError> {
    dump_poly_from_entry_with_std_in_module_options(entry, module, &StdSourceOptions::default())
}

pub fn dump_poly_from_entry_with_std_in_module_options(
    entry: impl AsRef<FsPath>,
    module: &str,
    options: &StdSourceOptions,
) -> Result<DumpPolyOutput, RouteError> {
    dump_poly_from_sources(
        collect_local_sources_with_std_options(entry, options)?,
        DumpPolyKind::Module {
            module: parse_dump_module_path(module)?,
            raw: false,
        },
    )
}

/// entry file と近場の `lib/std.yu` を読み、指定 module 直下の値だけを raw poly dump する。
pub fn dump_poly_raw_from_entry_with_std_in_module(
    entry: impl AsRef<FsPath>,
    module: &str,
) -> Result<DumpPolyOutput, RouteError> {
    dump_poly_raw_from_entry_with_std_in_module_options(entry, module, &StdSourceOptions::default())
}

pub fn dump_poly_raw_from_entry_with_std_in_module_options(
    entry: impl AsRef<FsPath>,
    module: &str,
    options: &StdSourceOptions,
) -> Result<DumpPolyOutput, RouteError> {
    dump_poly_from_sources(
        collect_local_sources_with_std_options(entry, options)?,
        DumpPolyKind::Module {
            module: parse_dump_module_path(module)?,
            raw: true,
        },
    )
}

/// `mod foo;` / `use mod foo::*` だけを辿って raw source file を集める。
pub fn collect_local_sources(
    entry: impl AsRef<FsPath>,
) -> Result<Vec<CollectedSource>, RouteError> {
    Collector::new().collect_entry(entry.as_ref(), false)
}

pub fn collect_local_sources_with_cache(
    entry: impl AsRef<FsPath>,
    cache: SourceCollectionCache,
) -> Result<Vec<CollectedSource>, RouteError> {
    Collector::new_with_cache(Some(cache)).collect_entry(entry.as_ref(), false)
}

pub fn collect_local_source_text(
    entry: impl AsRef<FsPath>,
    source: String,
) -> Result<Vec<CollectedSource>, RouteError> {
    Collector::new().collect_entry_source(entry.as_ref(), source, false)
}

/// 近場の `lib/std.yu` と local module file を集め、root source に implicit prelude を足す。
pub fn collect_local_sources_with_std(
    entry: impl AsRef<FsPath>,
) -> Result<Vec<CollectedSource>, RouteError> {
    collect_local_sources_with_std_options(entry, &StdSourceOptions::default())
}

pub fn collect_local_sources_with_std_options(
    entry: impl AsRef<FsPath>,
    options: &StdSourceOptions,
) -> Result<Vec<CollectedSource>, RouteError> {
    collect_local_sources_with_std_options_and_cache(entry, options, None)
}

pub fn collect_local_sources_with_std_options_and_cache(
    entry: impl AsRef<FsPath>,
    options: &StdSourceOptions,
    cache: Option<SourceCollectionCache>,
) -> Result<Vec<CollectedSource>, RouteError> {
    let entry = entry.as_ref();
    let std_root = resolve_std_root_for_entry(entry, options)?;

    let mut collector = Collector::new_with_cache(cache);
    collector.collect_std_root(&std_root)?;
    collector.collect_entry(entry, true)
}

pub fn resolve_std_root_for_entry(
    entry: impl AsRef<FsPath>,
    options: &StdSourceOptions,
) -> Result<PathBuf, RouteError> {
    let entry = entry.as_ref();
    let base = entry.parent().unwrap_or_else(|| FsPath::new("."));
    resolve_std_root(base, options)
}

pub fn collect_local_source_text_with_std_options(
    entry: impl AsRef<FsPath>,
    source: String,
    options: &StdSourceOptions,
) -> Result<Vec<CollectedSource>, RouteError> {
    Ok(collect_local_source_text_with_std_context(entry.as_ref(), source, options)?.files)
}

fn collect_local_source_text_with_std_context(
    entry: &FsPath,
    source: String,
    options: &StdSourceOptions,
) -> Result<SourceTextWithStdContext, RouteError> {
    let base = entry.parent().unwrap_or_else(|| FsPath::new("."));
    let std_root = resolve_std_root(base, options)?;

    if let Some(module_path) = std_module_path_for_file(&std_root, entry) {
        let mut collector = Collector::new();
        collector.collect_std_root_with_source_override(&std_root, entry, source)?;
        let mut files = collector.finish();
        files.push(CollectedSource::new(
            entry.to_path_buf(),
            Path::default(),
            source_with_implicit_std_prelude(String::new()),
        ));
        return Ok(SourceTextWithStdContext {
            files,
            focus_module: module_path,
            byte_offset_adjust: 0,
        });
    }

    let mut collector = Collector::new();
    collector.collect_std_root(&std_root)?;
    Ok(SourceTextWithStdContext {
        files: collector.collect_entry_source(entry, source, true)?,
        focus_module: Path::default(),
        byte_offset_adjust: IMPLICIT_STD_SOURCE_PREFIX_LEN,
    })
}

/// Browser / playground 向けに、root source と埋め込み std だけで source set を作る。
///
/// この入口はファイルシステムを読まない。root source 側の local `mod foo;` を辿る必要が
/// 出た場合は、呼び出し側で複数 source を渡す別 route を足す。
pub fn collect_source_text_with_embedded_std(
    entry: impl AsRef<FsPath>,
    source: String,
) -> Result<Vec<CollectedSource>, RouteError> {
    Ok(embedded_std_sources_with_root(entry.as_ref(), source))
}

/// Browser / playground 向けの小さい embedded std profile で source set を作る。
///
/// full std は意味上の fallback として残し、この入口は common playground examples が
/// source を切り替えるたびに parser/file/text-path まで含む std 全体を推論し直すのを避ける。
pub fn collect_source_text_with_embedded_playground_std(
    entry: impl AsRef<FsPath>,
    source: String,
) -> Result<Vec<CollectedSource>, RouteError> {
    Ok(embedded_playground_std_sources_with_root(
        entry.as_ref(),
        source,
    ))
}

pub fn load_source_text_with_embedded_std(
    entry: impl AsRef<FsPath>,
    source: String,
) -> Result<Vec<sources::LoadedFile>, RouteError> {
    Ok(embedded_std_loaded_with_root(entry.as_ref(), source))
}

pub fn load_source_text_with_embedded_playground_std(
    entry: impl AsRef<FsPath>,
    source: String,
) -> Result<Vec<sources::LoadedFile>, RouteError> {
    Ok(embedded_playground_std_loaded_with_root(
        entry.as_ref(),
        source,
    ))
}

pub fn analyze_source_text_with_embedded_std(
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
) -> Result<AnalyzeSourceOutput, RouteError> {
    analyze_from_loaded_files(load_source_text_with_embedded_std(entry, source.into())?)
}

pub fn check_poly_from_source_text_with_embedded_std(
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
) -> Result<CheckPolyOutput, RouteError> {
    let total_start = Instant::now();
    let collect_start = Instant::now();
    let source = source.into();
    let collect = collect_start.elapsed();
    let load_start = Instant::now();
    let loaded = load_source_text_with_embedded_std(entry, source)?;
    let load = load_start.elapsed();
    check_poly_from_loaded_files(
        loaded,
        collect,
        load,
        total_start,
        CheckPolyKind::All {
            title: "check-poly-embedded-std",
        },
    )
}

pub fn dump_poly_from_source_text_with_embedded_std(
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
) -> Result<DumpPolyOutput, RouteError> {
    dump_poly_from_loaded_files(
        load_source_text_with_embedded_std(entry, source.into())?,
        DumpPolyKind::Compact,
    )
}

pub fn dump_poly_raw_from_source_text_with_embedded_std(
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
) -> Result<DumpPolyOutput, RouteError> {
    dump_poly_from_loaded_files(
        load_source_text_with_embedded_std(entry, source.into())?,
        DumpPolyKind::Raw,
    )
}

pub fn dump_mono_from_source_text_with_embedded_std(
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
) -> Result<DumpMonoOutput, RouteError> {
    dump_mono_from_loaded_files(load_source_text_with_embedded_std(entry, source.into())?)
}

pub fn build_poly_from_source_text_with_embedded_std(
    _entry: impl AsRef<FsPath>,
    source: impl Into<String>,
) -> Result<BuildPolyOutput, RouteError> {
    let (lowering, file_count) = embedded_std_lowering_with_root(source.into())?;
    let errors = lowering
        .errors
        .iter()
        .map(format_body_lowering_error)
        .collect();
    let host_manifest = host_manifest_from_lowering(&lowering)?;
    Ok(BuildPolyOutput {
        arena: lowering.session.poly,
        labels: lowering.labels,
        host_manifest: Some(host_manifest),
        file_count,
        errors,
    })
}

pub fn build_poly_from_embedded_std_compiled_unit_artifact(
    artifact: crate::cache::CachedCompiledUnitArtifact,
    source: impl Into<String>,
) -> Result<BuildPolyOutput, RouteError> {
    let (lowering, file_count) = embedded_std_lowering_with_root_artifact(artifact, source.into())?;
    let errors = lowering
        .errors
        .iter()
        .map(format_body_lowering_error)
        .collect();
    let host_manifest = host_manifest_from_lowering(&lowering)?;
    Ok(BuildPolyOutput {
        arena: lowering.session.poly,
        labels: lowering.labels,
        host_manifest: Some(host_manifest),
        file_count,
        errors,
    })
}

pub fn build_poly_from_source_text_with_embedded_playground_std(
    _entry: impl AsRef<FsPath>,
    source: impl Into<String>,
) -> Result<BuildPolyOutput, RouteError> {
    let (lowering, file_count) = embedded_playground_std_lowering_with_root(source.into())?;
    let errors = lowering
        .errors
        .iter()
        .map(format_body_lowering_error)
        .collect();
    let host_manifest = host_manifest_from_lowering(&lowering)?;
    Ok(BuildPolyOutput {
        arena: lowering.session.poly,
        labels: lowering.labels,
        host_manifest: Some(host_manifest),
        file_count,
        errors,
    })
}

pub fn build_poly_from_embedded_playground_std_compiled_unit_artifact(
    artifact: crate::cache::CachedCompiledUnitArtifact,
    source: impl Into<String>,
) -> Result<BuildPolyOutput, RouteError> {
    let (lowering, file_count) =
        embedded_playground_std_lowering_with_root_artifact(artifact, source.into())?;
    let errors = lowering
        .errors
        .iter()
        .map(format_body_lowering_error)
        .collect();
    let host_manifest = host_manifest_from_lowering(&lowering)?;
    Ok(BuildPolyOutput {
        arena: lowering.session.poly,
        labels: lowering.labels,
        host_manifest: Some(host_manifest),
        file_count,
        errors,
    })
}

pub fn build_control_from_source_text_with_embedded_std(
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
) -> Result<BuildControlOutput, RouteError> {
    let output = build_poly_from_source_text_with_embedded_std(entry, source)?;
    build_control_from_poly_output(&output)
}

pub fn build_control_from_source_text_with_embedded_playground_std(
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
) -> Result<BuildControlOutput, RouteError> {
    let output = build_poly_from_source_text_with_embedded_playground_std(entry, source)?;
    build_control_from_poly_output(&output)
}

pub fn run_control_from_source_text_with_embedded_std(
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
) -> Result<RunControlOutput, RouteError> {
    let output = build_control_from_source_text_with_embedded_std(entry, source)?;
    run_built_control_program_with_labels(
        &output.program,
        output.file_count,
        output.errors.clone(),
        Some(&output.labels),
    )
}

/// `base` から上へ辿って、デバッグ用の近場 std package root を探す。
pub fn find_nearby_std_root(base: &FsPath) -> Option<PathBuf> {
    for ancestor in base.ancestors() {
        let candidate = ancestor.join("lib");
        if is_std_root(&candidate) {
            return Some(candidate);
        }
    }
    None
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DumpPolyOutput {
    pub text: String,
    pub file_count: usize,
    /// body lowering が報告したエラーの表示用整形。dump 本文とは別に stderr へ流す。
    pub errors: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DumpMonoOutput {
    pub text: String,
    pub file_count: usize,
    /// body lowering が報告したエラーの表示用整形。dump 本文とは別に stderr へ流す。
    pub errors: Vec<String>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct RunMonoOutput {
    pub text: String,
    pub file_count: usize,
    /// body lowering が報告したエラーの表示用整形。実行結果とは別に stderr へ流す。
    pub errors: Vec<String>,
    pub values: Vec<mono_runtime::Value>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct RunControlOutput {
    pub text: String,
    pub file_count: usize,
    /// body lowering が報告したエラーの表示用整形。実行結果とは別に stderr へ流す。
    pub errors: Vec<String>,
    pub values: Vec<control_vm::Value>,
    pub stdout: String,
    pub stats: control_vm::RuntimeStats,
    pub timings: ControlRunTimings,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ControlRunTimings {
    pub validate: Duration,
    pub init: Duration,
    pub execute: Duration,
    pub root_format: Duration,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckPolyOutput {
    pub text: String,
    pub file_count: usize,
    pub diagnostics: Vec<SourceDiagnostic>,
    pub diagnostic_source: Option<CheckDiagnosticSource>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckDiagnosticSource {
    pub source: String,
    pub range_offset: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AnalyzeSourceOutput {
    pub file_count: usize,
    pub diagnostics: Vec<SourceDiagnostic>,
}

pub(crate) struct SourceTextAnalysis {
    check: infer::check::PolyCheckOutput,
    source_index: SourceFileIndex,
    parse_diagnostics: Vec<SourceDiagnostic>,
    focus_module: Path,
    file_count: usize,
    byte_offset_adjust: usize,
    root_has_implicit_prelude: bool,
}

impl SourceTextAnalysis {
    pub(crate) fn analyze(&self) -> AnalyzeSourceOutput {
        let mut diagnostics = self.parse_diagnostics.clone();
        diagnostics.extend(source_diagnostics_for_check(
            &self.check,
            &self.check.report.diagnostics,
        ));
        AnalyzeSourceOutput {
            file_count: self.file_count,
            diagnostics,
        }
    }

    pub(crate) fn hover(&self, byte_offset: usize) -> Option<SourceHover> {
        source_hover_from_check(
            &self.check,
            self.loaded_byte_offset(byte_offset),
            &self.focus_module,
        )
    }

    pub(crate) fn definition(&self, byte_offset: usize) -> Option<SourceDefinition> {
        source_definition_from_check(
            &self.check,
            &self.source_index,
            self.loaded_byte_offset(byte_offset),
            &self.focus_module,
        )
    }

    pub(crate) fn references(
        &self,
        byte_offset: usize,
        include_declaration: bool,
    ) -> Vec<SourceLocation> {
        source_references_from_check(
            &self.check,
            &self.source_index,
            self.loaded_byte_offset(byte_offset),
            &self.focus_module,
            include_declaration,
        )
    }

    pub(crate) fn prepare_rename(&self, byte_offset: usize) -> Option<SourceRange> {
        source_prepare_rename_from_check(
            &self.check,
            self.loaded_byte_offset(byte_offset),
            &self.focus_module,
        )
    }

    pub(crate) fn rename(&self, byte_offset: usize, new_name: &str) -> Option<SourceRename> {
        source_rename_from_check(
            &self.check,
            &self.source_index,
            self.loaded_byte_offset(byte_offset),
            &self.focus_module,
            new_name,
        )
    }

    pub(crate) fn root_has_implicit_prelude(&self) -> bool {
        self.root_has_implicit_prelude
    }

    fn loaded_byte_offset(&self, root_byte_offset: usize) -> usize {
        root_byte_offset + self.byte_offset_adjust
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceHover {
    pub range: SourceRange,
    pub contents: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceDefinition {
    pub origin: SourceRange,
    pub target: SourceLocation,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceLocation {
    pub path: PathBuf,
    pub range: SourceRange,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceRename {
    pub range: SourceRange,
    pub edits: Vec<SourceTextEdit>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceTextEdit {
    pub location: SourceLocation,
    pub new_text: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceDiagnostic {
    pub severity: SourceDiagnosticSeverity,
    pub code: Option<String>,
    pub label: Option<String>,
    pub range: Option<SourceRange>,
    pub message: String,
    pub hint: Option<String>,
    pub related: Vec<SourceDiagnosticRelated>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceDiagnosticRelated {
    pub message: String,
    pub range: SourceRange,
    pub origin: Option<SourceDiagnosticRelatedOrigin>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SourceDiagnosticRelatedOrigin {
    TypeAnnotation,
    Expression,
    ImplCandidate,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SourceDiagnosticSeverity {
    Error,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BuildControlOutput {
    pub program: control_vm::Program,
    pub runtime_evidence: specialize::RuntimeEvidenceSurface,
    pub labels: poly::dump::DumpLabels,
    pub file_count: usize,
    /// body lowering が報告したエラーの表示用整形。artifact とは別に stderr へ流す。
    pub errors: Vec<String>,
}

pub struct BuildPolyOutput {
    pub arena: poly::expr::Arena,
    pub labels: poly::dump::DumpLabels,
    pub host_manifest: Option<poly::host_manifest::HostActManifest>,
    pub file_count: usize,
    /// body lowering が報告したエラーの表示用整形。artifact とは別に stderr へ流す。
    pub errors: Vec<String>,
}

impl BuildPolyOutput {
    pub fn ensure_runtime_ready(&self) -> Result<(), RouteError> {
        reject_runtime_lowering_errors(&self.errors)
    }
}

pub struct BuildPolyAndCompiledUnitOutput {
    pub poly: BuildPolyOutput,
    pub compiled_unit: crate::cache::CachedCompiledUnitArtifact,
}

fn reject_runtime_lowering_errors(errors: &[String]) -> Result<(), RouteError> {
    if errors.is_empty() {
        return Ok(());
    }
    Err(RouteError::LoweringDiagnostics {
        errors: errors.to_vec(),
    })
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CollectedSource {
    pub path: PathBuf,
    pub module_path: Path,
    pub band_path: Path,
    pub source: String,
    pub resolution_imports: Vec<sources::UseImport>,
}

impl CollectedSource {
    pub fn new(path: PathBuf, module_path: Path, source: String) -> Self {
        Self::with_band_path_and_resolution_imports(
            path,
            module_path,
            Path::default(),
            source,
            Vec::new(),
        )
    }

    pub fn with_band_path(
        path: PathBuf,
        module_path: Path,
        band_path: Path,
        source: String,
    ) -> Self {
        Self::with_band_path_and_resolution_imports(
            path,
            module_path,
            band_path,
            source,
            Vec::new(),
        )
    }

    pub fn with_resolution_imports(
        path: PathBuf,
        module_path: Path,
        source: String,
        resolution_imports: Vec<sources::UseImport>,
    ) -> Self {
        Self::with_band_path_and_resolution_imports(
            path,
            module_path,
            Path::default(),
            source,
            resolution_imports,
        )
    }

    pub fn with_band_path_and_resolution_imports(
        path: PathBuf,
        module_path: Path,
        band_path: Path,
        source: String,
        resolution_imports: Vec<sources::UseImport>,
    ) -> Self {
        Self {
            path,
            module_path,
            band_path,
            source,
            resolution_imports,
        }
    }
}

struct SourceTextWithStdContext {
    files: Vec<CollectedSource>,
    focus_module: Path,
    byte_offset_adjust: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum DumpPolyKind {
    Compact,
    Raw,
    Module { module: Path, raw: bool },
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum CheckPolyKind {
    All { title: &'static str },
    Module { title: &'static str, module: Path },
}

#[derive(Debug)]
pub enum RouteError {
    Io {
        path: PathBuf,
        error: io::Error,
    },
    StdRootNotFound {
        base: PathBuf,
    },
    StdRootInstall {
        root: PathBuf,
        error: io::Error,
    },
    InvalidStdRoot {
        root: PathBuf,
    },
    ModuleNotFound {
        current: PathBuf,
        module: Path,
        candidates: Vec<PathBuf>,
    },
    AmbiguousModuleFile {
        current: PathBuf,
        module: Path,
        candidates: Vec<PathBuf>,
    },
    RealmBandNotFound {
        root: PathBuf,
        band: Path,
        candidates: Vec<PathBuf>,
    },
    InvalidInstalledRealmImport {
        path: Path,
        reason: String,
    },
    InstalledRealmNotFound {
        name: Path,
        version: Option<String>,
        root: PathBuf,
        candidates: Vec<PathBuf>,
    },
    InstalledRealmVersionNotFound {
        name: Path,
        version: Option<String>,
        root: PathBuf,
    },
    DuplicateModulePath {
        module: Path,
        first: PathBuf,
        second: PathBuf,
    },
    DuplicateModuleFile {
        file: PathBuf,
        first_module: Path,
        first_band: Path,
        second_module: Path,
        second_band: Path,
    },
    CrossBandCycle {
        from: Path,
        to: Path,
    },
    LoweringDiagnostics {
        errors: Vec<String>,
    },
    InvalidDumpModulePath {
        module: String,
    },
    DumpModuleNotFound {
        module: Path,
    },
    CheckModuleNotFound {
        module: Path,
    },
    SyntaxMerge(sources::CompiledSyntaxMergeError),
    Lower(infer::LoadedFilesError),
    HostActManifest(infer::host_acts::HostActManifestBuildError),
    Specialize(specialize::SpecializeError),
    Runtime(mono_runtime::RuntimeError),
    Control(control_vm::RunError),
    ControlLower(control_vm::LowerError),
}

impl fmt::Display for RouteError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RouteError::Io { path, error } => {
                write!(f, "failed to read {}: {error}", path.display())
            }
            RouteError::StdRootNotFound { base } => {
                write!(
                    f,
                    "std root was not found near {} or in {YULANG_STD_ENV}",
                    base.display()
                )
            }
            RouteError::StdRootInstall { root, error } => {
                write!(f, "failed to install std root {}: {error}", root.display())
            }
            RouteError::InvalidStdRoot { root } => {
                write!(f, "std root {} does not contain std.yu", root.display())
            }
            RouteError::ModuleNotFound {
                current,
                module,
                candidates,
            } => {
                write!(
                    f,
                    "module {} requested from {} was not found",
                    format_module_path(module),
                    current.display()
                )?;
                write_candidates(f, candidates)
            }
            RouteError::AmbiguousModuleFile {
                current,
                module,
                candidates,
            } => {
                write!(
                    f,
                    "module {} requested from {} is ambiguous",
                    format_module_path(module),
                    current.display()
                )?;
                write_candidates(f, candidates)
            }
            RouteError::RealmBandNotFound {
                root,
                band,
                candidates,
            } => {
                write!(
                    f,
                    "band {} requested from realm {} was not found",
                    format_module_path(band),
                    root.display()
                )?;
                write_candidates(f, candidates)
            }
            RouteError::InvalidInstalledRealmImport { path, reason } => write!(
                f,
                "installed realm import {} is invalid: {reason}",
                format_module_path(path)
            ),
            RouteError::InstalledRealmNotFound {
                name,
                version,
                root,
                candidates,
            } => {
                write!(f, "installed local realm {}", format_module_path(name))?;
                if let Some(version) = version {
                    write!(f, " {version}")?;
                }
                write!(f, " was not found under {}", root.display())?;
                write_candidates(f, candidates)
            }
            RouteError::InstalledRealmVersionNotFound {
                name,
                version,
                root,
            } => {
                write!(f, "installed local realm {}", format_module_path(name))?;
                if let Some(version) = version {
                    write!(f, " {version}")?;
                }
                write!(f, " has no installed snapshot under {}", root.display())
            }
            RouteError::DuplicateModulePath {
                module,
                first,
                second,
            } => write!(
                f,
                "module {} was loaded from both {} and {}",
                format_module_path(module),
                first.display(),
                second.display()
            ),
            RouteError::DuplicateModuleFile {
                file,
                first_module,
                first_band,
                second_module,
                second_band,
            } => write!(
                f,
                "file {} was loaded as both module {} in band {} and module {} in band {}",
                file.display(),
                format_module_path(first_module),
                format_module_path(first_band),
                format_module_path(second_module),
                format_module_path(second_band)
            ),
            RouteError::CrossBandCycle { from, to } => write!(
                f,
                "cross-band import from {} to {} would create a cycle",
                format_module_path(from),
                format_module_path(to)
            ),
            RouteError::LoweringDiagnostics { errors } => {
                write!(
                    f,
                    "compile error [yulang.lowering]: source has lowering errors"
                )?;
                for error in errors {
                    write!(f, "\n  detail: {error}")?;
                }
                write!(
                    f,
                    "\n  hint: run `yulang check` to see source ranges before running"
                )
            }
            RouteError::InvalidDumpModulePath { module } => {
                write!(f, "dump module path `{module}` is invalid")
            }
            RouteError::DumpModuleNotFound { module } => write!(
                f,
                "dump module {} was not found",
                format_module_path(module)
            ),
            RouteError::CheckModuleNotFound { module } => write!(
                f,
                "check module {} was not found",
                format_module_path(module)
            ),
            RouteError::SyntaxMerge(sources::CompiledSyntaxMergeError::ConflictingOperator {
                module_path,
                name,
            }) => write!(
                f,
                "compile error [yulang.conflicting-operator]: operator `{}` from module {} conflicts with another compiled syntax surface",
                name.0,
                format_module_path(module_path)
            ),
            RouteError::Lower(error) => write!(f, "{error}"),
            RouteError::HostActManifest(error) => {
                write!(f, "failed to build host act manifest: {error:?}")
            }
            RouteError::Specialize(error) => write!(f, "{error}"),
            RouteError::Runtime(error) => write!(f, "{error}"),
            RouteError::Control(error) => write!(f, "{error}"),
            RouteError::ControlLower(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for RouteError {}

struct CheckPolyTimings {
    collect: Duration,
    load: Duration,
    infer: Duration,
    summarize: Duration,
    total: Duration,
    lowering: infer::lowering::BodyLoweringTiming,
}

fn check_poly_from_sources(
    files: Vec<CollectedSource>,
    collect: Duration,
    total_start: Instant,
    kind: CheckPolyKind,
) -> Result<CheckPolyOutput, RouteError> {
    let load_start = Instant::now();
    let loaded = load_collected_sources(files);
    let load = load_start.elapsed();
    check_poly_from_loaded_files(loaded, collect, load, total_start, kind)
}

fn check_poly_from_loaded_files(
    loaded: Vec<sources::LoadedFile>,
    collect: Duration,
    load: Duration,
    total_start: Instant,
    kind: CheckPolyKind,
) -> Result<CheckPolyOutput, RouteError> {
    let check = infer::check::check_loaded_files(&loaded).map_err(RouteError::Lower)?;
    let timing = CheckPolyTimings {
        collect,
        load,
        infer: check.timing.infer,
        summarize: check.timing.summarize,
        total: total_start.elapsed(),
        lowering: check.timing.lowering,
    };
    let mut diagnostics = parser_diagnostics_from_loaded(&loaded);
    diagnostics.extend(match &kind {
        CheckPolyKind::All { .. } => {
            source_diagnostics_for_check(&check, &check.report.diagnostics)
        }
        CheckPolyKind::Module { module, .. } => {
            let Some(module_check) = check
                .report
                .modules
                .iter()
                .find(|item| item.path == *module)
            else {
                return Err(RouteError::CheckModuleNotFound {
                    module: module.clone(),
                });
            };
            source_diagnostics_for_check(&check, &module_check.diagnostics)
        }
    });
    let diagnostic_source = check_diagnostic_source(&loaded);
    let text = match kind {
        CheckPolyKind::All { title } => {
            format_check_poly_output(loaded.len(), &check, &timing, title)
        }
        CheckPolyKind::Module { title, module } => {
            let Some(module_check) = check.report.modules.iter().find(|item| item.path == module)
            else {
                return Err(RouteError::CheckModuleNotFound { module });
            };
            format_check_poly_module_output(loaded.len(), &check, module_check, &timing, title)
        }
    };
    Ok(CheckPolyOutput {
        text,
        file_count: loaded.len(),
        diagnostics,
        diagnostic_source,
    })
}

fn check_diagnostic_source(loaded: &[sources::LoadedFile]) -> Option<CheckDiagnosticSource> {
    let root = loaded
        .iter()
        .find(|file| file.module_path.segments.is_empty())?;
    let source = root.source.as_str();
    let range_offset = if source.starts_with(IMPLICIT_PRELUDE_IMPORT)
        && source
            .get(IMPLICIT_PRELUDE_IMPORT.len()..)
            .is_some_and(|rest| rest.starts_with(IMPLICIT_STD_MODULE_DECL))
    {
        IMPLICIT_STD_SOURCE_PREFIX_LEN
    } else if source.starts_with(IMPLICIT_PRELUDE_IMPORT) {
        IMPLICIT_PRELUDE_IMPORT.len()
    } else {
        0
    };
    Some(CheckDiagnosticSource {
        source: source.get(range_offset..).unwrap_or_default().to_string(),
        range_offset,
    })
}

fn source_text_analysis_from_files(
    files: Vec<CollectedSource>,
    focus_module: Path,
    byte_offset_adjust: usize,
) -> Result<SourceTextAnalysis, RouteError> {
    let file_count = files.len();
    let source_index = SourceFileIndex::from_collected_sources(&files);
    let loaded = load_collected_sources(files);
    let parse_diagnostics = parser_diagnostics_from_loaded(&loaded);
    let check = infer::check::check_loaded_files(&loaded).map_err(RouteError::Lower)?;
    Ok(SourceTextAnalysis {
        check,
        source_index,
        parse_diagnostics,
        focus_module,
        file_count,
        byte_offset_adjust,
        root_has_implicit_prelude: byte_offset_adjust != 0,
    })
}

fn parser_diagnostics_from_loaded(loaded: &[sources::LoadedFile]) -> Vec<SourceDiagnostic> {
    let Some(root) = loaded
        .iter()
        .find(|file| file.module_path.segments.is_empty())
    else {
        return Vec::new();
    };
    let cst = rowan::SyntaxNode::<parser::sink::YulangLanguage>::new_root(root.cst.clone());
    cst.descendants()
        .filter(|node| node.kind() == parser::lex::SyntaxKind::InvalidToken)
        .map(|node| {
            let range = parser_diagnostic_range(&root.source, node.text_range());
            SourceDiagnostic {
                severity: SourceDiagnosticSeverity::Error,
                code: Some("yulang.syntax".to_string()),
                label: None,
                range: Some(range),
                message: if node.text().is_empty() {
                    "syntax error: unexpected end of input".to_string()
                } else {
                    "syntax error: unexpected token".to_string()
                },
                hint: None,
                related: Vec::new(),
            }
        })
        .collect()
}

fn parser_diagnostic_range(source: &str, range: rowan::TextRange) -> SourceRange {
    let mut start = usize::from(range.start());
    let mut end = usize::from(range.end());
    if start < end {
        end = start + source[start..end].trim_end().len();
    }
    if start == end && start >= source.len() {
        start = source.trim_end().len();
        end = start;
    }
    SourceRange { start, end }
}

fn analyze_from_loaded_files(
    loaded: Vec<sources::LoadedFile>,
) -> Result<AnalyzeSourceOutput, RouteError> {
    let check = infer::check::check_loaded_files(&loaded).map_err(RouteError::Lower)?;
    let diagnostics = source_diagnostics_for_check(&check, &check.report.diagnostics);
    Ok(AnalyzeSourceOutput {
        file_count: loaded.len(),
        diagnostics,
    })
}

fn hover_from_sources(
    files: Vec<CollectedSource>,
    byte_offset: usize,
    file: &Path,
) -> Result<Option<SourceHover>, RouteError> {
    hover_from_loaded_files(load_collected_sources(files), byte_offset, file)
}

fn hover_from_loaded_files(
    loaded: Vec<sources::LoadedFile>,
    byte_offset: usize,
    file: &Path,
) -> Result<Option<SourceHover>, RouteError> {
    let check = infer::check::check_loaded_files(&loaded).map_err(RouteError::Lower)?;
    Ok(source_hover_from_check(&check, byte_offset, file))
}

fn definition_from_sources(
    files: Vec<CollectedSource>,
    byte_offset: usize,
    file: &Path,
) -> Result<Option<SourceDefinition>, RouteError> {
    let source_index = SourceFileIndex::from_collected_sources(&files);
    definition_from_loaded_files(
        load_collected_sources(files),
        &source_index,
        byte_offset,
        file,
    )
}

fn definition_from_loaded_files(
    loaded: Vec<sources::LoadedFile>,
    source_index: &SourceFileIndex,
    byte_offset: usize,
    file: &Path,
) -> Result<Option<SourceDefinition>, RouteError> {
    let check = infer::check::check_loaded_files(&loaded).map_err(RouteError::Lower)?;
    Ok(source_definition_from_check(
        &check,
        source_index,
        byte_offset,
        file,
    ))
}

fn references_from_sources(
    files: Vec<CollectedSource>,
    byte_offset: usize,
    file: &Path,
    include_declaration: bool,
) -> Result<Vec<SourceLocation>, RouteError> {
    let source_index = SourceFileIndex::from_collected_sources(&files);
    references_from_loaded_files(
        load_collected_sources(files),
        &source_index,
        byte_offset,
        file,
        include_declaration,
    )
}

fn references_from_loaded_files(
    loaded: Vec<sources::LoadedFile>,
    source_index: &SourceFileIndex,
    byte_offset: usize,
    file: &Path,
    include_declaration: bool,
) -> Result<Vec<SourceLocation>, RouteError> {
    let check = infer::check::check_loaded_files(&loaded).map_err(RouteError::Lower)?;
    Ok(source_references_from_check(
        &check,
        source_index,
        byte_offset,
        file,
        include_declaration,
    ))
}

fn prepare_rename_from_sources(
    files: Vec<CollectedSource>,
    byte_offset: usize,
    file: &Path,
) -> Result<Option<SourceRange>, RouteError> {
    prepare_rename_from_loaded_files(load_collected_sources(files), byte_offset, file)
}

fn prepare_rename_from_loaded_files(
    loaded: Vec<sources::LoadedFile>,
    byte_offset: usize,
    file: &Path,
) -> Result<Option<SourceRange>, RouteError> {
    let check = infer::check::check_loaded_files(&loaded).map_err(RouteError::Lower)?;
    Ok(source_prepare_rename_from_check(&check, byte_offset, file))
}

fn rename_from_sources(
    files: Vec<CollectedSource>,
    byte_offset: usize,
    file: &Path,
    new_name: &str,
) -> Result<Option<SourceRename>, RouteError> {
    let source_index = SourceFileIndex::from_collected_sources(&files);
    rename_from_loaded_files(
        load_collected_sources(files),
        &source_index,
        byte_offset,
        file,
        new_name,
    )
}

fn rename_from_loaded_files(
    loaded: Vec<sources::LoadedFile>,
    source_index: &SourceFileIndex,
    byte_offset: usize,
    file: &Path,
    new_name: &str,
) -> Result<Option<SourceRename>, RouteError> {
    let check = infer::check::check_loaded_files(&loaded).map_err(RouteError::Lower)?;
    Ok(source_rename_from_check(
        &check,
        source_index,
        byte_offset,
        file,
        new_name,
    ))
}

fn source_hover_from_check(
    check: &infer::check::PolyCheckOutput,
    byte_offset: usize,
    file: &Path,
) -> Option<SourceHover> {
    let mut best = None;
    let format_context = HoverFormatContext::new(check, file);
    for (def, span) in check.lowering.modules.def_source_spans() {
        if &span.file != file || !source_range_contains(span.range, byte_offset) {
            continue;
        }
        push_best_hover(
            &mut best,
            hover_for_def(check, &format_context, def, span.range),
            span.range,
        );
    }
    for (def, span) in check.lowering.session.local_defs.source_spans() {
        if &span.file != file || !source_range_contains(span.range, byte_offset) {
            continue;
        }
        push_best_hover(
            &mut best,
            hover_for_def(check, &format_context, def, span.range),
            span.range,
        );
    }
    for (reference, use_site) in check.lowering.session.refs.iter() {
        let Some(span) = &use_site.source_span else {
            continue;
        };
        if &span.file != file || !source_range_contains(span.range, byte_offset) {
            continue;
        }
        let Some(target) = check.lowering.session.poly.ref_target(reference) else {
            continue;
        };
        push_best_hover(
            &mut best,
            hover_for_def(check, &format_context, target, span.range),
            span.range,
        );
    }
    for (select, span) in check.lowering.session.selections.source_spans() {
        if &span.file != file || !source_range_contains(span.range, byte_offset) {
            continue;
        }
        push_best_hover(
            &mut best,
            hover_for_select(check, &format_context, select, span.range),
            span.range,
        );
    }
    best
}

fn source_references_from_check(
    check: &infer::check::PolyCheckOutput,
    source_index: &SourceFileIndex,
    byte_offset: usize,
    file: &Path,
    include_declaration: bool,
) -> Vec<SourceLocation> {
    let Some(target) = reference_target_from_check(check, byte_offset, file) else {
        return Vec::new();
    };

    source_locations_for_target(check, source_index, target, include_declaration)
}

fn source_prepare_rename_from_check(
    check: &infer::check::PolyCheckOutput,
    byte_offset: usize,
    file: &Path,
) -> Option<SourceRange> {
    reference_target_candidate_from_check(check, byte_offset, file).map(|target| target.range)
}

fn source_rename_from_check(
    check: &infer::check::PolyCheckOutput,
    source_index: &SourceFileIndex,
    byte_offset: usize,
    file: &Path,
    new_name: &str,
) -> Option<SourceRename> {
    if !is_valid_rename_identifier(new_name) {
        return None;
    }
    let target = reference_target_candidate_from_check(check, byte_offset, file)?;
    let edits = source_locations_for_target(check, source_index, target.def, true)
        .into_iter()
        .filter_map(|location| {
            let source = source_index.source_for_location(&location)?;
            let span_text = source.get(location.range.start..location.range.end)?;
            Some(SourceTextEdit {
                location,
                new_text: rename_new_text_for_span(span_text, new_name),
            })
        })
        .collect::<Vec<_>>();
    (!edits.is_empty()).then_some(SourceRename {
        range: target.range,
        edits,
    })
}

fn source_locations_for_target(
    check: &infer::check::PolyCheckOutput,
    source_index: &SourceFileIndex,
    target: poly::expr::DefId,
    include_declaration: bool,
) -> Vec<SourceLocation> {
    let mut locations = Vec::new();
    if include_declaration
        && let Some(location) = source_location_for_def(check, source_index, target)
    {
        locations.push(location);
    }
    for (reference, use_site) in check.lowering.session.refs.iter() {
        let Some(reference_target) = check.lowering.session.poly.ref_target(reference) else {
            continue;
        };
        if reference_target != target {
            continue;
        }
        if let Some(span) = &use_site.source_span
            && let Some(location) = source_index.location_for_span(span)
        {
            locations.push(location);
        }
    }
    for (select, span) in check.lowering.session.selections.source_spans() {
        if select_target_def(check, select) != Some(target) {
            continue;
        }
        if let Some(location) = source_index.location_for_span(span) {
            locations.push(location);
        }
    }

    sort_source_locations(&mut locations);
    locations.dedup();
    locations
}

fn source_definition_from_check(
    check: &infer::check::PolyCheckOutput,
    source_index: &SourceFileIndex,
    byte_offset: usize,
    file: &Path,
) -> Option<SourceDefinition> {
    let mut best = None;
    for (reference, use_site) in check.lowering.session.refs.iter() {
        let Some(origin) = &use_site.source_span else {
            continue;
        };
        if &origin.file != file || !source_range_contains(origin.range, byte_offset) {
            continue;
        }
        let Some(target) = check.lowering.session.poly.ref_target(reference) else {
            continue;
        };
        push_best_definition(
            &mut best,
            definition_for_def(check, source_index, target, origin.range),
            origin.range,
        );
    }
    for (select, origin) in check.lowering.session.selections.source_spans() {
        if &origin.file != file || !source_range_contains(origin.range, byte_offset) {
            continue;
        }
        push_best_definition(
            &mut best,
            definition_for_select(check, source_index, select, origin.range),
            origin.range,
        );
    }
    for (def, origin) in check.lowering.modules.def_source_spans() {
        if &origin.file != file || !source_range_contains(origin.range, byte_offset) {
            continue;
        }
        push_best_definition(
            &mut best,
            definition_for_def(check, source_index, def, origin.range),
            origin.range,
        );
    }
    for (def, origin) in check.lowering.session.local_defs.source_spans() {
        if &origin.file != file || !source_range_contains(origin.range, byte_offset) {
            continue;
        }
        push_best_definition(
            &mut best,
            definition_for_def(check, source_index, def, origin.range),
            origin.range,
        );
    }
    best
}

fn reference_target_from_check(
    check: &infer::check::PolyCheckOutput,
    byte_offset: usize,
    file: &Path,
) -> Option<poly::expr::DefId> {
    reference_target_candidate_from_check(check, byte_offset, file).map(|candidate| candidate.def)
}

fn reference_target_candidate_from_check(
    check: &infer::check::PolyCheckOutput,
    byte_offset: usize,
    file: &Path,
) -> Option<ReferenceTargetCandidate> {
    let mut best = None;
    for (reference, use_site) in check.lowering.session.refs.iter() {
        let Some(span) = &use_site.source_span else {
            continue;
        };
        if &span.file != file || !source_range_contains(span.range, byte_offset) {
            continue;
        }
        let Some(target) = check.lowering.session.poly.ref_target(reference) else {
            continue;
        };
        push_best_reference_target(&mut best, target, span.range);
    }
    for (select, span) in check.lowering.session.selections.source_spans() {
        if &span.file != file || !source_range_contains(span.range, byte_offset) {
            continue;
        }
        let Some(target) = select_target_def(check, select) else {
            continue;
        };
        push_best_reference_target(&mut best, target, span.range);
    }
    for (def, span) in check.lowering.modules.def_source_spans() {
        if &span.file != file || !source_range_contains(span.range, byte_offset) {
            continue;
        }
        push_best_reference_target(&mut best, def, span.range);
    }
    for (def, span) in check.lowering.session.local_defs.source_spans() {
        if &span.file != file || !source_range_contains(span.range, byte_offset) {
            continue;
        }
        push_best_reference_target(&mut best, def, span.range);
    }
    best
}

#[derive(Debug, Clone, Copy)]
struct ReferenceTargetCandidate {
    def: poly::expr::DefId,
    range: SourceRange,
}

fn push_best_reference_target(
    best: &mut Option<ReferenceTargetCandidate>,
    def: poly::expr::DefId,
    range: SourceRange,
) {
    let candidate_len = range.end.saturating_sub(range.start);
    let best_len = best
        .as_ref()
        .map(|candidate| candidate.range.end.saturating_sub(candidate.range.start))
        .unwrap_or(usize::MAX);
    if candidate_len < best_len {
        *best = Some(ReferenceTargetCandidate { def, range });
    }
}

fn select_target_def(
    check: &infer::check::PolyCheckOutput,
    select: poly::expr::SelectId,
) -> Option<poly::expr::DefId> {
    match check.lowering.session.poly.select(select).resolution? {
        poly::expr::SelectResolution::Method { def } => Some(def),
        poly::expr::SelectResolution::TypeclassMethod { member } => Some(member),
        poly::expr::SelectResolution::RecordField => None,
    }
}

fn push_best_definition(
    best: &mut Option<SourceDefinition>,
    candidate: Option<SourceDefinition>,
    range: SourceRange,
) {
    let Some(candidate) = candidate else {
        return;
    };
    let candidate_len = range.end.saturating_sub(range.start);
    let best_len = best
        .as_ref()
        .map(|definition| {
            definition
                .origin
                .end
                .saturating_sub(definition.origin.start)
        })
        .unwrap_or(usize::MAX);
    if candidate_len < best_len {
        *best = Some(candidate);
    }
}

fn definition_for_select(
    check: &infer::check::PolyCheckOutput,
    source_index: &SourceFileIndex,
    select: poly::expr::SelectId,
    origin: SourceRange,
) -> Option<SourceDefinition> {
    let target = select_target_def(check, select)?;
    definition_for_def(check, source_index, target, origin)
}

fn definition_for_def(
    check: &infer::check::PolyCheckOutput,
    source_index: &SourceFileIndex,
    def: poly::expr::DefId,
    origin: SourceRange,
) -> Option<SourceDefinition> {
    Some(SourceDefinition {
        origin,
        target: source_location_for_def(check, source_index, def)?,
    })
}

fn source_location_for_def(
    check: &infer::check::PolyCheckOutput,
    source_index: &SourceFileIndex,
    def: poly::expr::DefId,
) -> Option<SourceLocation> {
    check
        .lowering
        .modules
        .def_source_span(def)
        .or_else(|| {
            check
                .lowering
                .session
                .local_defs
                .get(def)
                .and_then(|use_site| use_site.source_span.as_ref())
        })
        .and_then(|span| source_index.location_for_span(span))
}

fn sort_source_locations(locations: &mut [SourceLocation]) {
    locations.sort_by(|left, right| {
        left.path
            .cmp(&right.path)
            .then(left.range.start.cmp(&right.range.start))
            .then(left.range.end.cmp(&right.range.end))
    });
}

fn is_valid_rename_identifier(name: &str) -> bool {
    let mut chars = name.chars().peekable();
    let Some(first) = chars.next() else {
        return false;
    };
    if !(unicode_ident::is_xid_start(first) || first == '_') {
        return false;
    }
    let mut saw_suffix = false;
    while let Some(ch) = chars.next() {
        if saw_suffix {
            return false;
        }
        if unicode_ident::is_xid_continue(ch) {
            continue;
        }
        if (ch == '?' || ch == '!') && chars.peek().is_none() {
            saw_suffix = true;
            continue;
        }
        return false;
    }
    !is_rename_keyword(name)
}

fn is_rename_keyword(name: &str) -> bool {
    matches!(
        name,
        "do" | "if"
            | "else"
            | "elsif"
            | "case"
            | "catch"
            | "my"
            | "our"
            | "pub"
            | "use"
            | "type"
            | "struct"
            | "enum"
            | "error"
            | "role"
            | "impl"
            | "cast"
            | "act"
            | "mod"
            | "as"
            | "for"
            | "in"
            | "with"
            | "where"
            | "via"
            | "rule"
            | "prefix"
            | "infix"
            | "suffix"
            | "nullfix"
            | "lazy"
    )
}

fn rename_new_text_for_span(span_text: &str, name: &str) -> String {
    let prefix = span_text
        .chars()
        .next()
        .filter(|ch| matches!(ch, '$' | '&' | '_' | '\''));
    match prefix {
        Some(prefix) => format!("{prefix}{name}"),
        None => name.to_string(),
    }
}

fn push_best_hover(
    best: &mut Option<SourceHover>,
    candidate: Option<SourceHover>,
    range: SourceRange,
) {
    let Some(candidate) = candidate else {
        return;
    };
    let candidate_len = range.end.saturating_sub(range.start);
    let best_len = best
        .as_ref()
        .map(|hover| hover.range.end.saturating_sub(hover.range.start))
        .unwrap_or(usize::MAX);
    if candidate_len < best_len {
        *best = Some(candidate);
    }
}

fn hover_for_def(
    check: &infer::check::PolyCheckOutput,
    format_context: &HoverFormatContext<'_>,
    def: poly::expr::DefId,
    range: SourceRange,
) -> Option<SourceHover> {
    let Some(poly::expr::Def::Let {
        scheme: Some(scheme),
        ..
    }) = check.lowering.session.poly.defs.get(def)
    else {
        return hover_for_local_def(check, format_context, def, range);
    };
    let label = check.lowering.labels.def_label(def)?;
    if hover_label_is_hidden(label) {
        return None;
    }
    let label = format_context.format_value_label(label, def);
    let ty = format_context.format_scheme(scheme);
    Some(SourceHover {
        range,
        contents: format!("{label}: {ty}"),
    })
}

fn hover_for_local_def(
    check: &infer::check::PolyCheckOutput,
    format_context: &HoverFormatContext<'_>,
    def: poly::expr::DefId,
    range: SourceRange,
) -> Option<SourceHover> {
    let poly::expr::Def::Arg = check.lowering.session.poly.defs.get(def)? else {
        return None;
    };
    let label = check.lowering.labels.def_label(def)?;
    if hover_label_is_hidden(label) {
        return None;
    }
    let local = check.lowering.session.local_defs.get(def)?;
    let label = format_context.format_value_label(label, def);
    let ty = match local.role {
        infer::uses::LocalDefRole::Input => {
            infer::check::format_inferred_input_type_with_path_rewriter(
                &check.lowering,
                local.value,
                &|path| format_context.rewrite_type_path(path),
            )
        }
        infer::uses::LocalDefRole::Value => {
            infer::check::format_inferred_value_type_with_path_rewriter(
                &check.lowering,
                local.value,
                &|path| format_context.rewrite_type_path(path),
            )
        }
    };
    Some(SourceHover {
        range,
        contents: format!("{label}: {ty}"),
    })
}

fn hover_for_select(
    check: &infer::check::PolyCheckOutput,
    format_context: &HoverFormatContext<'_>,
    select: poly::expr::SelectId,
    range: SourceRange,
) -> Option<SourceHover> {
    match check.lowering.session.poly.select(select).resolution? {
        poly::expr::SelectResolution::Method { def } => {
            hover_for_selected_method(check, format_context, select, def, range)
        }
        poly::expr::SelectResolution::TypeclassMethod { member } => {
            hover_for_selected_method(check, format_context, select, member, range)
        }
        poly::expr::SelectResolution::RecordField => {
            hover_for_resolved_selection_value(check, format_context, select, range)
        }
    }
}

fn hover_for_resolved_selection_value(
    check: &infer::check::PolyCheckOutput,
    format_context: &HoverFormatContext<'_>,
    select: poly::expr::SelectId,
    range: SourceRange,
) -> Option<SourceHover> {
    let use_site = check.lowering.session.selections.resolved(select)?;
    Some(SourceHover {
        range,
        contents: format!(
            "{}: {}",
            check.lowering.session.poly.select(select).name,
            format_context.format_value_type(use_site.selected_value)
        ),
    })
}

fn hover_for_selected_method(
    check: &infer::check::PolyCheckOutput,
    format_context: &HoverFormatContext<'_>,
    select: poly::expr::SelectId,
    def: poly::expr::DefId,
    range: SourceRange,
) -> Option<SourceHover> {
    let Some(poly::expr::Def::Let {
        scheme: Some(scheme),
        ..
    }) = check.lowering.session.poly.defs.get(def)
    else {
        return None;
    };
    if let Some(hover) = hover_for_resolved_selection_value(check, format_context, select, range) {
        return Some(hover);
    }
    let raw_label = check.lowering.labels.def_label(def)?;
    let label = if hover_label_is_hidden(raw_label) {
        check.lowering.session.poly.select(select).name.clone()
    } else {
        format_context.format_value_label(raw_label, def)
    };
    Some(SourceHover {
        range,
        contents: format!("{label}: {}", format_context.format_scheme(scheme)),
    })
}

fn hover_label_is_hidden(label: &str) -> bool {
    label.split('.').any(|segment| {
        // `#` and `&` labels are generated by lowering for act copies, sub labels,
        // and mutable local refs. They carry internal type state, not source names.
        segment.starts_with('#') || segment.contains('#') || segment.starts_with('&')
    })
}

struct HoverFormatContext<'a> {
    check: &'a infer::check::PolyCheckOutput,
    module: infer::ModuleId,
    site: infer::ModuleOrder,
}

impl<'a> HoverFormatContext<'a> {
    fn new(check: &'a infer::check::PolyCheckOutput, file: &Path) -> Self {
        Self {
            check,
            module: check
                .lowering
                .modules
                .module_by_path(file)
                .unwrap_or_else(|| check.lowering.modules.root_id()),
            site: infer::ModuleOrder::from_index(u32::MAX),
        }
    }

    fn format_scheme(&self, scheme: &poly::types::Scheme) -> String {
        poly::dump::format_scheme_with_path_rewriter(
            &self.check.lowering.session.poly.typ,
            scheme,
            &|path| self.rewrite_type_path(path),
        )
    }

    fn format_value_type(&self, value: poly::types::TypeVar) -> String {
        infer::check::format_inferred_value_type_with_path_rewriter(
            &self.check.lowering,
            value,
            &|path| self.rewrite_type_path(path),
        )
    }

    fn rewrite_type_path(&self, path: &[String]) -> Vec<String> {
        if path.len() <= 1 {
            return path.to_vec();
        }
        let names = path.iter().cloned().map(Name).collect::<Vec<_>>();
        for start in (0..names.len()).rev() {
            let suffix = &names[start..];
            let Some(found) =
                self.check
                    .lowering
                    .modules
                    .type_path_at(self.module, suffix, self.site)
            else {
                continue;
            };
            if self.type_decl_matches_path(&found, path) {
                return suffix.iter().map(|name| name.0.clone()).collect();
            }
        }
        path.to_vec()
    }

    fn type_decl_matches_path(&self, decl: &infer::ModuleTypeDecl, path: &[String]) -> bool {
        let full = self.check.lowering.modules.type_decl_path(decl);
        full.segments.len() == path.len()
            && full
                .segments
                .iter()
                .map(|name| name.0.as_str())
                .eq(path.iter().map(String::as_str))
    }

    fn format_value_label(&self, label: &str, def: poly::expr::DefId) -> String {
        let parts = label.split('.').collect::<Vec<_>>();
        if parts.len() <= 1 {
            return label.to_string();
        }
        let names = parts
            .iter()
            .map(|part| Name((*part).to_string()))
            .collect::<Vec<_>>();
        for start in (0..names.len()).rev() {
            let suffix = &names[start..];
            if self
                .check
                .lowering
                .modules
                .value_path_at(self.module, suffix, self.site)
                .is_some_and(|found| found == def)
            {
                return suffix
                    .iter()
                    .map(|name| name.0.as_str())
                    .collect::<Vec<_>>()
                    .join(".");
            }
        }
        label.to_string()
    }
}

fn source_range_contains(range: SourceRange, byte_offset: usize) -> bool {
    if range.start == range.end {
        byte_offset == range.start
    } else {
        range.start <= byte_offset && byte_offset < range.end
    }
}

struct SourceFileIndex {
    paths_by_module: HashMap<Path, PathBuf>,
    sources_by_path: HashMap<PathBuf, String>,
}

impl SourceFileIndex {
    fn from_collected_sources(files: &[CollectedSource]) -> Self {
        let mut sources_by_path = HashMap::new();
        for file in files {
            sources_by_path
                .entry(file.path.clone())
                .or_insert_with(|| file.source.clone());
        }
        Self {
            paths_by_module: files
                .iter()
                .map(|file| (file.module_path.clone(), file.path.clone()))
                .collect(),
            sources_by_path,
        }
    }

    fn location_for_span(&self, span: &infer::SourceSpan) -> Option<SourceLocation> {
        Some(SourceLocation {
            path: self.paths_by_module.get(&span.file)?.clone(),
            range: span.range,
        })
    }

    fn source_for_location(&self, location: &SourceLocation) -> Option<&str> {
        self.sources_by_path.get(&location.path).map(String::as_str)
    }
}

fn source_diagnostics_from_check(
    check: &infer::check::PolyCheckOutput,
    diagnostics: &[infer::check::CheckDiagnostic],
) -> Vec<SourceDiagnostic> {
    diagnostics
        .iter()
        .map(|diagnostic| {
            let error = &check.lowering.errors[diagnostic.error_index];
            SourceDiagnostic {
                severity: SourceDiagnosticSeverity::Error,
                code: body_lowering_error_code(error).map(str::to_string),
                label: diagnostic.label.clone(),
                range: body_lowering_error_source_range(error).or_else(|| {
                    diagnostic
                        .def
                        .and_then(|def| check.lowering.modules.def_source_range(def))
                }),
                message: format_body_lowering_error(error),
                hint: body_lowering_error_hint(error),
                related: body_lowering_error_related(error),
            }
        })
        .collect()
}

fn source_diagnostics_for_check(
    check: &infer::check::PolyCheckOutput,
    diagnostics: &[infer::check::CheckDiagnostic],
) -> Vec<SourceDiagnostic> {
    let mut out = source_diagnostics_from_check(check, diagnostics);
    if check.lowering.errors.is_empty() {
        out.extend(role_method_diagnostics_from_specialize(check));
    }
    out
}

fn role_method_diagnostics_from_specialize(
    check: &infer::check::PolyCheckOutput,
) -> Vec<SourceDiagnostic> {
    // Role impl satisfaction currently belongs to specialization. Keep check/LSP
    // on the same oracle and only bridge source payload for role method failures.
    if !check.lowering.session.poly.selects().iter().any(|select| {
        matches!(
            select.resolution,
            Some(poly::expr::SelectResolution::TypeclassMethod { .. })
        )
    }) {
        return Vec::new();
    }
    match specialize::specialize(&check.lowering.session.poly) {
        Ok(_) => Vec::new(),
        Err(error) => source_diagnostic_from_role_method_specialize_error(check, &error)
            .into_iter()
            .collect(),
    }
}

fn source_diagnostic_from_role_method_specialize_error(
    check: &infer::check::PolyCheckOutput,
    error: &specialize::SpecializeError,
) -> Option<SourceDiagnostic> {
    match error {
        specialize::SpecializeError::UnresolvedTypeclassMethod {
            expr,
            receiver,
            ..
        } => Some(SourceDiagnostic {
            severity: SourceDiagnosticSeverity::Error,
            code: Some("yulang.unresolved-method".to_string()),
            label: role_method_diagnostic_label(check, *expr),
            range: role_method_expr_source_range(check, *expr),
            message: format!(
                "no role implementation satisfies this method call for receiver {}",
                specialize::mono::dump::dump_type(receiver)
            ),
            hint: Some(
                "add or import an impl for the receiver type, or call a method supported by that value"
                    .to_string(),
            ),
            related: Vec::new(),
        }),
        specialize::SpecializeError::AmbiguousTypeclassMethod {
            expr,
            receiver,
            candidates,
            ..
        } => Some(SourceDiagnostic {
            severity: SourceDiagnosticSeverity::Error,
            code: Some("yulang.ambiguous-method".to_string()),
            label: role_method_diagnostic_label(check, *expr),
            range: role_method_expr_source_range(check, *expr),
            message: format!(
                "more than one role implementation satisfies this method call for receiver {}",
                specialize::mono::dump::dump_type(receiver)
            ),
            hint: Some(
                "make the receiver type more specific or keep only one matching impl in scope"
                    .to_string(),
            ),
            related: role_method_candidate_related(check, candidates),
        }),
        _ => None,
    }
}

fn role_method_expr_select(
    check: &infer::check::PolyCheckOutput,
    expr: u32,
) -> Option<poly::expr::SelectId> {
    let expr = check.lowering.session.poly.exprs().get(expr as usize)?;
    match expr {
        poly::expr::Expr::Select(_, select) => Some(*select),
        _ => None,
    }
}

fn role_method_expr_source_range(
    check: &infer::check::PolyCheckOutput,
    expr: u32,
) -> Option<SourceRange> {
    let select = role_method_expr_select(check, expr)?;
    check
        .lowering
        .session
        .selections
        .source_span(select)
        .map(|span| span.range)
}

fn role_method_diagnostic_label(
    check: &infer::check::PolyCheckOutput,
    expr: u32,
) -> Option<String> {
    let select = role_method_expr_select(check, expr)?;
    Some(check.lowering.session.poly.select(select).name.clone())
}

fn role_method_candidate_related(
    check: &infer::check::PolyCheckOutput,
    candidates: &[specialize::mono::DefId],
) -> Vec<SourceDiagnosticRelated> {
    candidates
        .iter()
        .filter_map(|candidate| {
            let def = poly::expr::DefId(candidate.0);
            let range = check.lowering.modules.def_source_range(def)?;
            let label = check
                .lowering
                .labels
                .def_label(def)
                .map(str::to_string)
                .unwrap_or_else(|| format!("d{}", candidate.0));
            Some(SourceDiagnosticRelated {
                message: format!("matching impl method candidate: {label}"),
                range,
                origin: Some(SourceDiagnosticRelatedOrigin::ImplCandidate),
            })
        })
        .collect()
}

fn body_lowering_error_code(error: &infer::lowering::BodyLoweringError) -> Option<&'static str> {
    match error {
        infer::lowering::BodyLoweringError::Expr { error, .. }
        | infer::lowering::BodyLoweringError::RootExpr { error } => lowering_error_code(error),
        infer::lowering::BodyLoweringError::Analysis(_) => Some("yulang.analysis"),
        infer::lowering::BodyLoweringError::MissingBindingDecl { .. }
        | infer::lowering::BodyLoweringError::MissingModuleDecl { .. }
        | infer::lowering::BodyLoweringError::MissingBody { .. }
        | infer::lowering::BodyLoweringError::NonLetDef { .. } => Some("yulang.lowering"),
    }
}

fn lowering_error_code(error: &infer::lowering::LoweringError) -> Option<&'static str> {
    match error {
        infer::lowering::LoweringError::UnsupportedSyntax { .. } => {
            Some("yulang.unsupported-syntax")
        }
        infer::lowering::LoweringError::UnsupportedPatternSyntax { .. } => {
            Some("yulang.unsupported-pattern-syntax")
        }
        infer::lowering::LoweringError::TypeMismatch { .. } => Some("yulang.type-mismatch"),
        infer::lowering::LoweringError::InvalidNumber { .. } => Some("yulang.invalid-number"),
        infer::lowering::LoweringError::MissingLambdaBody => Some("yulang.missing-lambda-body"),
        infer::lowering::LoweringError::MissingIfCondition => Some("yulang.missing-if-condition"),
        infer::lowering::LoweringError::MissingIfBody => Some("yulang.missing-if-body"),
        infer::lowering::LoweringError::MissingCaseScrutinee { .. } => {
            Some("yulang.missing-case-scrutinee")
        }
        infer::lowering::LoweringError::MissingCaseArmPattern { .. } => {
            Some("yulang.missing-case-arm-pattern")
        }
        infer::lowering::LoweringError::MissingCaseArmBody { .. } => {
            Some("yulang.missing-case-arm-body")
        }
        infer::lowering::LoweringError::AnnotationBuild {
            error: infer::annotation::AnnBuildError::UnresolvedTypeName { .. },
            ..
        }
        | infer::lowering::LoweringError::NegSignatureBuild {
            error: infer::lowering::NegSignatureBuildError::UnresolvedTypeName { .. },
        } => Some("yulang.unresolved-type"),
        infer::lowering::LoweringError::AnnotationBuild {
            error: infer::annotation::AnnBuildError::UnsupportedSyntax { .. },
            ..
        } => Some("yulang.unsupported-type-syntax"),
        infer::lowering::LoweringError::AnnotationBuild { .. } => {
            Some("yulang.invalid-type-annotation")
        }
        infer::lowering::LoweringError::AnnotationConstraint { .. } => {
            Some("yulang.invalid-type-annotation")
        }
        infer::lowering::LoweringError::NegSignatureBuild { .. }
        | infer::lowering::LoweringError::SignatureConstraint { .. }
        | infer::lowering::LoweringError::SignatureShapeMismatch { .. }
        | infer::lowering::LoweringError::SignatureTypeMismatch { .. } => {
            Some("yulang.invalid-signature")
        }
        infer::lowering::LoweringError::UnresolvedName { .. } => Some("yulang.unresolved-value"),
        infer::lowering::LoweringError::UnsupportedTopLevelVarBinding { .. } => {
            Some("yulang.top-level-mutable-binding")
        }
        infer::lowering::LoweringError::UnsupportedRuleLazyQuantifier { .. } => {
            Some("yulang.unsupported-rule-lazy-quantifier")
        }
        infer::lowering::LoweringError::MissingCatchScrutinee { .. } => {
            Some("yulang.missing-catch-scrutinee")
        }
        infer::lowering::LoweringError::MissingCatchArmPattern { .. } => {
            Some("yulang.missing-catch-arm-pattern")
        }
        infer::lowering::LoweringError::MissingCatchArmBody { .. } => {
            Some("yulang.missing-catch-arm-body")
        }
        infer::lowering::LoweringError::MissingFieldName => Some("yulang.missing-field-name"),
        infer::lowering::LoweringError::MissingOpName => Some("yulang.missing-operation-name"),
        infer::lowering::LoweringError::MissingOpOperand => {
            Some("yulang.missing-operation-operand")
        }
        infer::lowering::LoweringError::MissingRecordFieldName => {
            Some("yulang.missing-record-field-name")
        }
        infer::lowering::LoweringError::MissingRecordFieldValue => {
            Some("yulang.missing-record-field-value")
        }
        infer::lowering::LoweringError::MissingIndexArgument { .. } => {
            Some("yulang.missing-index-argument")
        }
        infer::lowering::LoweringError::MissingLocalBindingName => {
            Some("yulang.missing-local-binding-name")
        }
        infer::lowering::LoweringError::MissingLocalBindingBody => {
            Some("yulang.missing-local-binding-body")
        }
        infer::lowering::LoweringError::MissingLocalVarAct { .. } => {
            Some("yulang.missing-local-var-act")
        }
        infer::lowering::LoweringError::MissingSubLabelAct { .. } => {
            Some("yulang.missing-sub-label-act")
        }
    }
}

fn body_lowering_error_source_range(
    error: &infer::lowering::BodyLoweringError,
) -> Option<SourceRange> {
    match error {
        infer::lowering::BodyLoweringError::Expr { error, .. }
        | infer::lowering::BodyLoweringError::RootExpr { error } => {
            lowering_error_source_range(error)
        }
        infer::lowering::BodyLoweringError::MissingBindingDecl { .. }
        | infer::lowering::BodyLoweringError::MissingModuleDecl { .. }
        | infer::lowering::BodyLoweringError::MissingBody { .. }
        | infer::lowering::BodyLoweringError::NonLetDef { .. }
        | infer::lowering::BodyLoweringError::Analysis(_) => None,
    }
}

fn body_lowering_error_related(
    error: &infer::lowering::BodyLoweringError,
) -> Vec<SourceDiagnosticRelated> {
    match error {
        infer::lowering::BodyLoweringError::Expr {
            error:
                infer::lowering::LoweringError::TypeMismatch {
                    actual,
                    expected,
                    actual_range,
                    expected_range,
                },
            ..
        }
        | infer::lowering::BodyLoweringError::RootExpr {
            error:
                infer::lowering::LoweringError::TypeMismatch {
                    actual,
                    expected,
                    actual_range,
                    expected_range,
                },
        } => {
            let mut related = Vec::new();
            if let Some(range) = expected_range {
                related.push(SourceDiagnosticRelated {
                    message: format!("expected type comes from this type annotation: {expected}"),
                    range: *range,
                    origin: Some(SourceDiagnosticRelatedOrigin::TypeAnnotation),
                });
            }
            if let Some(range) = actual_range {
                related.push(SourceDiagnosticRelated {
                    message: format!("actual type comes from this expression: {actual}"),
                    range: *range,
                    origin: Some(SourceDiagnosticRelatedOrigin::Expression),
                });
            }
            related
        }
        _ => Vec::new(),
    }
}

fn body_lowering_error_hint(error: &infer::lowering::BodyLoweringError) -> Option<String> {
    match error {
        infer::lowering::BodyLoweringError::Expr { error, .. }
        | infer::lowering::BodyLoweringError::RootExpr { error } => lowering_error_hint(error),
        _ => None,
    }
}

fn lowering_error_hint(error: &infer::lowering::LoweringError) -> Option<String> {
    match error {
        infer::lowering::LoweringError::UnsupportedSyntax { .. } => {
            Some("rewrite this form using supported expression syntax".to_string())
        }
        infer::lowering::LoweringError::UnsupportedPatternSyntax { .. } => {
            Some("rewrite this form using supported pattern syntax".to_string())
        }
        infer::lowering::LoweringError::UnsupportedRuleLazyQuantifier { .. } => {
            Some("use greedy `*` or `+`, then handle optional matching explicitly".to_string())
        }
        infer::lowering::LoweringError::UnresolvedName { name, .. } => Some(format!(
            "define `{}` before this use, or import the module that provides it",
            name.0
        )),
        infer::lowering::LoweringError::InvalidNumber { .. } => {
            Some("use a valid integer, float, or fraction literal".to_string())
        }
        infer::lowering::LoweringError::MissingLambdaBody => {
            Some("write a body expression after the lambda arrow".to_string())
        }
        infer::lowering::LoweringError::MissingIfCondition => {
            Some("write a condition after `if`".to_string())
        }
        infer::lowering::LoweringError::MissingIfBody => {
            Some("write the branch body expression".to_string())
        }
        infer::lowering::LoweringError::MissingCaseScrutinee { .. } => {
            Some("write `case <expr>:` before the arms".to_string())
        }
        infer::lowering::LoweringError::MissingCaseArmPattern { .. } => {
            Some("write a pattern before `->`".to_string())
        }
        infer::lowering::LoweringError::MissingCaseArmBody { .. } => {
            Some("write an expression after `->`".to_string())
        }
        infer::lowering::LoweringError::MissingCatchScrutinee { .. } => {
            Some("write `catch <expr>:` before the handler arms".to_string())
        }
        infer::lowering::LoweringError::MissingCatchArmPattern { .. } => {
            Some("write a value pattern or effect operation before `->`".to_string())
        }
        infer::lowering::LoweringError::MissingCatchArmBody { .. } => {
            Some("write an expression after `->`".to_string())
        }
        infer::lowering::LoweringError::MissingFieldName => {
            Some("write a field name after `.`".to_string())
        }
        infer::lowering::LoweringError::MissingOpName => {
            Some("write the effect operation name after the effect path".to_string())
        }
        infer::lowering::LoweringError::MissingOpOperand => {
            Some("write the operation argument expression".to_string())
        }
        infer::lowering::LoweringError::MissingRecordFieldName => {
            Some("write the record field name before `:`".to_string())
        }
        infer::lowering::LoweringError::MissingRecordFieldValue => {
            Some("write the record field value after `:`".to_string())
        }
        infer::lowering::LoweringError::MissingIndexArgument { .. } => {
            Some("write an index expression inside the brackets".to_string())
        }
        infer::lowering::LoweringError::MissingLocalBindingName => {
            Some("write a local binding name after `my`".to_string())
        }
        infer::lowering::LoweringError::MissingLocalBindingBody => {
            Some("write a body expression after `=`".to_string())
        }
        infer::lowering::LoweringError::UnsupportedTopLevelVarBinding { .. } => {
            Some("move the mutable binding into a block or function body".to_string())
        }
        infer::lowering::LoweringError::MissingLocalVarAct { .. } => Some(
            "let the mutable binding lower with its generated variable effect body".to_string(),
        ),
        infer::lowering::LoweringError::MissingSubLabelAct { .. } => {
            Some("let the labeled sub lower with its generated effect body".to_string())
        }
        infer::lowering::LoweringError::AnnotationBuild {
            error: infer::annotation::AnnBuildError::UnresolvedTypeName { path },
            ..
        }
        | infer::lowering::LoweringError::NegSignatureBuild {
            error: infer::lowering::NegSignatureBuildError::UnresolvedTypeName { path },
        } => Some(format!(
            "define type `{}` before this annotation, or import it",
            format_name_path(path)
        )),
        infer::lowering::LoweringError::AnnotationBuild { .. }
        | infer::lowering::LoweringError::AnnotationConstraint { .. } => Some(
            "use a supported type annotation form and keep effect rows in effect position"
                .to_string(),
        ),
        infer::lowering::LoweringError::NegSignatureBuild { .. }
        | infer::lowering::LoweringError::SignatureConstraint { .. }
        | infer::lowering::LoweringError::SignatureShapeMismatch { .. }
        | infer::lowering::LoweringError::SignatureTypeMismatch { .. } => {
            Some("check the declared signature shape and effect row".to_string())
        }
        infer::lowering::LoweringError::TypeMismatch { .. } => None,
    }
}

fn lowering_error_source_range(error: &infer::lowering::LoweringError) -> Option<SourceRange> {
    match error {
        infer::lowering::LoweringError::UnresolvedName { source_range, .. } => *source_range,
        infer::lowering::LoweringError::UnsupportedTopLevelVarBinding { source_range, .. } => {
            *source_range
        }
        infer::lowering::LoweringError::UnsupportedRuleLazyQuantifier { source_range, .. } => {
            Some(*source_range)
        }
        infer::lowering::LoweringError::MissingCaseScrutinee { source_range }
        | infer::lowering::LoweringError::MissingCaseArmPattern { source_range }
        | infer::lowering::LoweringError::MissingCaseArmBody { source_range }
        | infer::lowering::LoweringError::MissingCatchScrutinee { source_range }
        | infer::lowering::LoweringError::MissingCatchArmPattern { source_range }
        | infer::lowering::LoweringError::MissingCatchArmBody { source_range }
        | infer::lowering::LoweringError::MissingIndexArgument { source_range } => {
            Some(*source_range)
        }
        infer::lowering::LoweringError::AnnotationBuild { source_range, .. } => *source_range,
        _ => None,
    }
}

fn dump_poly_from_sources(
    files: Vec<CollectedSource>,
    kind: DumpPolyKind,
) -> Result<DumpPolyOutput, RouteError> {
    dump_poly_from_loaded_files(load_collected_sources(files), kind)
}

fn dump_poly_from_loaded_files(
    loaded: Vec<sources::LoadedFile>,
    kind: DumpPolyKind,
) -> Result<DumpPolyOutput, RouteError> {
    match kind {
        DumpPolyKind::Compact => {
            let dump = infer::dump::dump_loaded_files(&loaded).map_err(RouteError::Lower)?;
            let errors = dump
                .lowering
                .errors
                .iter()
                .map(format_body_lowering_error)
                .collect();
            Ok(DumpPolyOutput {
                text: dump.text,
                file_count: loaded.len(),
                errors,
            })
        }
        DumpPolyKind::Raw => {
            let dump = infer::dump::dump_loaded_files_raw(&loaded).map_err(RouteError::Lower)?;
            let errors = dump
                .lowering
                .errors
                .iter()
                .map(format_body_lowering_error)
                .collect();
            Ok(DumpPolyOutput {
                text: dump.text,
                file_count: loaded.len(),
                errors,
            })
        }
        DumpPolyKind::Module { module, raw } => {
            let Some(dump) = infer::dump::dump_loaded_files_in_module(&loaded, &module, raw)
                .map_err(RouteError::Lower)?
            else {
                return Err(RouteError::DumpModuleNotFound { module });
            };
            let local_defs = dump.defs.iter().copied().collect::<HashSet<_>>();
            let errors = dump
                .lowering
                .errors
                .iter()
                .filter(|error| {
                    infer::dump::body_error_def(error).is_some_and(|def| local_defs.contains(&def))
                })
                .map(format_body_lowering_error)
                .collect();
            Ok(DumpPolyOutput {
                text: dump.text,
                file_count: loaded.len(),
                errors,
            })
        }
    }
}

fn dump_mono_from_sources(files: Vec<CollectedSource>) -> Result<DumpMonoOutput, RouteError> {
    let output = specialize_mono_from_sources(files)?;
    Ok(DumpMonoOutput {
        text: specialize::mono::dump::dump_program(&output.program),
        file_count: output.file_count,
        errors: output.errors,
    })
}

fn dump_mono_from_loaded_files(
    loaded: Vec<sources::LoadedFile>,
) -> Result<DumpMonoOutput, RouteError> {
    let output = specialize_mono_from_loaded_files(loaded)?;
    Ok(DumpMonoOutput {
        text: specialize::mono::dump::dump_program(&output.program),
        file_count: output.file_count,
        errors: output.errors,
    })
}

fn run_mono_from_sources(files: Vec<CollectedSource>) -> Result<RunMonoOutput, RouteError> {
    let output = specialize_mono_from_sources(files)?;
    let values = mono_runtime::run_program(&output.program).map_err(RouteError::Runtime)?;
    Ok(RunMonoOutput {
        text: format_run_mono_values_with_labels(&values, Some(&output.labels)),
        file_count: output.file_count,
        errors: output.errors,
        values,
    })
}

fn run_control_from_sources(files: Vec<CollectedSource>) -> Result<RunControlOutput, RouteError> {
    let output = build_control_from_sources(files)?;
    run_built_control_program_with_labels(
        &output.program,
        output.file_count,
        output.errors.clone(),
        Some(&output.labels),
    )
}

fn build_control_from_sources(
    files: Vec<CollectedSource>,
) -> Result<BuildControlOutput, RouteError> {
    let output = build_poly_from_sources(files)?;
    build_control_from_poly_output(&output)
}

struct SpecializedMonoOutput {
    program: specialize::mono::Program,
    labels: poly::dump::DumpLabels,
    file_count: usize,
    errors: Vec<String>,
}

fn specialize_mono_from_sources(
    files: Vec<CollectedSource>,
) -> Result<SpecializedMonoOutput, RouteError> {
    let output = build_poly_from_sources(files)?;
    specialize_mono_from_poly_output(output)
}

fn specialize_mono_from_loaded_files(
    loaded: Vec<sources::LoadedFile>,
) -> Result<SpecializedMonoOutput, RouteError> {
    let output = build_poly_from_loaded_files(loaded)?;
    specialize_mono_from_poly_output(output)
}

fn specialize_mono_from_poly_output(
    output: BuildPolyOutput,
) -> Result<SpecializedMonoOutput, RouteError> {
    output.ensure_runtime_ready()?;
    let program = specialize::specialize(&output.arena).map_err(RouteError::Specialize)?;
    Ok(SpecializedMonoOutput {
        program,
        labels: output.labels,
        file_count: output.file_count,
        errors: output.errors,
    })
}

fn build_poly_from_sources(files: Vec<CollectedSource>) -> Result<BuildPolyOutput, RouteError> {
    build_poly_from_loaded_files(load_collected_sources(files))
}

pub fn build_poly_from_loaded_files(
    loaded: Vec<sources::LoadedFile>,
) -> Result<BuildPolyOutput, RouteError> {
    let lowering = infer::lowering::lower_loaded_files(&loaded).map_err(RouteError::Lower)?;
    let errors = lowering
        .errors
        .iter()
        .map(format_body_lowering_error)
        .collect();
    let host_manifest = host_manifest_from_lowering(&lowering)?;
    Ok(BuildPolyOutput {
        arena: lowering.session.poly,
        labels: lowering.labels,
        host_manifest: Some(host_manifest),
        file_count: loaded.len(),
        errors,
    })
}

fn load_collected_sources(files: Vec<CollectedSource>) -> Vec<sources::LoadedFile> {
    let mut source_files = Vec::with_capacity(files.len());
    let mut band_paths = Vec::with_capacity(files.len());
    for file in files {
        source_files.push(SourceFile {
            module_path: file.module_path,
            source: file.source,
        });
        band_paths.push(file.band_path);
    }
    sources::load_with_band_paths(source_files, band_paths)
}

fn collected_source_files_and_band_paths(
    files: Vec<CollectedSource>,
) -> (Vec<SourceFile>, Vec<Path>) {
    let mut source_files = Vec::with_capacity(files.len());
    let mut band_paths = Vec::with_capacity(files.len());
    for file in files {
        source_files.push(SourceFile {
            module_path: file.module_path,
            source: file.source,
        });
        band_paths.push(file.band_path);
    }
    (source_files, band_paths)
}
