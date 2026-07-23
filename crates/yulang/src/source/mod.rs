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

use serde::{Deserialize, Serialize};
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

/// Observation-only companion for CLI phase telemetry.
///
/// The ordinary build API intentionally keeps lowering timings out of its
/// artifact-shaped result. This entry point exposes the already-collected
/// timing without changing the default build path or its output.
#[doc(hidden)]
pub fn build_poly_from_collected_sources_with_lowering_timing(
    files: Vec<CollectedSource>,
) -> Result<(BuildPolyOutput, infer::lowering::BodyLoweringTiming), RouteError> {
    build_poly_from_sources_with_lowering_timing(files)
}

pub fn build_poly_and_compiled_unit_from_collected_sources(
    files: Vec<CollectedSource>,
) -> Result<BuildPolyAndCompiledUnitOutput, RouteError> {
    build_poly_and_compiled_unit_from_collected_sources_with_timing(files).map(|(output, _)| output)
}

/// Observation-only companion for CLI phase telemetry.
#[doc(hidden)]
pub fn build_poly_and_compiled_unit_from_collected_sources_with_lowering_timing(
    files: Vec<CollectedSource>,
) -> Result<
    (
        BuildPolyAndCompiledUnitOutput,
        infer::lowering::BodyLoweringTiming,
    ),
    RouteError,
> {
    build_poly_and_compiled_unit_from_collected_sources_with_timing(files)
}

fn build_poly_and_compiled_unit_from_collected_sources_with_timing(
    files: Vec<CollectedSource>,
) -> Result<
    (
        BuildPolyAndCompiledUnitOutput,
        infer::lowering::BodyLoweringTiming,
    ),
    RouteError,
> {
    let diagnostic_sources = RuntimeDiagnosticSources::from_collected_sources(&files);
    let loaded = load_collected_sources(files.clone());
    let lowering = infer::lowering::lower_loaded_files(&loaded).map_err(RouteError::Lower)?;
    let application_provenance = lowering.application_provenance().clone();
    let subtype_provenance = lowering.subtype_provenance().clone();
    let selection_provenance = selection_provenance_from_lowering(&lowering);
    let lowering_timing = lowering.timing;
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
    Ok((
        BuildPolyAndCompiledUnitOutput {
            poly: BuildPolyOutput {
                arena: lowering.session.poly,
                subtype_provenance,
                application_provenance,
                selection_provenance,
                diagnostic_sources,
                labels: lowering.labels,
                host_manifest: Some(host_manifest),
                file_count: loaded.len(),
                errors,
            },
            compiled_unit,
        },
        lowering_timing,
    ))
}

pub fn build_poly_from_compiled_unit_artifact(
    artifact: crate::cache::CachedCompiledUnitArtifact,
) -> BuildPolyOutput {
    BuildPolyOutput {
        arena: artifact.runtime.arena,
        subtype_provenance: poly::provenance::SubtypeProvenanceSidecar::empty(),
        application_provenance: infer::lowering::ApplicationProvenanceTable::default(),
        selection_provenance: infer::lowering::SelectionProvenanceTable::default(),
        diagnostic_sources: RuntimeDiagnosticSources::default(),
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
    let diagnostic_sources = RuntimeDiagnosticSources::from_collected_sources(&suffix);
    let output = lower_compiled_unit_prefix_suffix(prefix, suffix)?;
    let application_provenance = output.lowering.application_provenance().clone();
    let subtype_provenance = output.lowering.subtype_provenance().clone();
    let selection_provenance = selection_provenance_from_lowering(&output.lowering);
    let host_manifest = host_manifest_from_lowering(&output.lowering)?;
    Ok(BuildPolyOutput {
        arena: output.lowering.session.poly,
        subtype_provenance,
        application_provenance,
        selection_provenance,
        diagnostic_sources,
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
    build_poly_and_compiled_unit_from_compiled_unit_prefix_with_timing(prefix, files, suffix)
        .map(|(output, _)| output)
}

/// Observation-only companion for CLI phase telemetry.
#[doc(hidden)]
pub fn build_poly_and_compiled_unit_from_compiled_unit_prefix_and_collected_sources_with_lowering_timing(
    prefix: crate::cache::CachedCompiledUnitArtifact,
    files: Vec<CollectedSource>,
    suffix: Vec<CollectedSource>,
) -> Result<
    (
        BuildPolyAndCompiledUnitOutput,
        infer::lowering::BodyLoweringTiming,
    ),
    RouteError,
> {
    build_poly_and_compiled_unit_from_compiled_unit_prefix_with_timing(prefix, files, suffix)
}

fn build_poly_and_compiled_unit_from_compiled_unit_prefix_with_timing(
    prefix: crate::cache::CachedCompiledUnitArtifact,
    files: Vec<CollectedSource>,
    suffix: Vec<CollectedSource>,
) -> Result<
    (
        BuildPolyAndCompiledUnitOutput,
        infer::lowering::BodyLoweringTiming,
    ),
    RouteError,
> {
    let diagnostic_sources = RuntimeDiagnosticSources::from_collected_sources(&files);
    let output = lower_compiled_unit_prefix_suffix(prefix, suffix)?;
    debug_assert_eq!(output.file_count, files.len());
    let lowering_timing = output.lowering.timing;
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
    let application_provenance = output.lowering.application_provenance().clone();
    let subtype_provenance = output.lowering.subtype_provenance().clone();
    let selection_provenance = selection_provenance_from_lowering(&output.lowering);
    Ok((
        BuildPolyAndCompiledUnitOutput {
            poly: BuildPolyOutput {
                arena: output.lowering.session.poly,
                subtype_provenance,
                application_provenance,
                selection_provenance,
                diagnostic_sources,
                labels: output.lowering.labels,
                host_manifest: Some(host_manifest),
                file_count: output.file_count,
                errors: output.errors,
            },
            compiled_unit,
        },
        lowering_timing,
    ))
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

fn selection_provenance_from_lowering(
    lowering: &infer::lowering::BodyLowering,
) -> infer::lowering::SelectionProvenanceTable {
    infer::lowering::SelectionProvenanceTable::from_source_spans(
        lowering
            .session
            .selections
            .source_spans()
            .map(|(select, span)| (select, span.clone())),
        lowering
            .modules
            .def_source_spans()
            .map(|(def, span)| (def, span.clone())),
    )
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
    let mut specialized = specialize::specialize_with_runtime_evidence_and_source_provenance(
        &output.arena,
        &output.subtype_provenance,
        output.application_provenance.expr_ids(),
        output
            .selection_provenance
            .selection_spans()
            .map(|(select, _)| select),
    )
    .map_err(|error| specialize_route_error(error, output))?;
    specialized.runtime_evidence.host_manifest = output.host_manifest.clone();
    specialized
        .runtime_evidence
        .attach_static_route_profile(&output.arena, &specialized.program);
    let lowered = control_ir::lower_with_application_provenance(&specialized.program)
        .map_err(RouteError::ControlLower)?;
    Ok(BuildControlOutput {
        program: lowered.program,
        runtime_evidence: specialized.runtime_evidence,
        application_provenance: RuntimeApplicationProvenance::new(
            output.application_provenance.clone(),
            lowered.application_provenance,
        ),
        selection_provenance: RuntimeSelectionProvenance::new(
            output.selection_provenance.clone(),
            lowered.selection_provenance,
        ),
        diagnostic_sources: output.diagnostic_sources.clone(),
        labels: output.labels.clone(),
        file_count: output.file_count,
        errors: output.errors.clone(),
    })
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

pub fn source_text_needs_full_embedded_std_for_playground(source: &str) -> bool {
    std_sources::source_text_needs_full_embedded_std_for_playground(source)
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
        sources::SourceLoadTiming::default(),
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
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
) -> Result<BuildPolyOutput, RouteError> {
    let source = source.into();
    let diagnostic_sources =
        RuntimeDiagnosticSources::from_collected_sources(&[CollectedSource::new(
            entry.as_ref().to_path_buf(),
            Path::default(),
            source_with_implicit_prelude_only(source.clone()),
        )]);
    let (lowering, file_count) = embedded_std_lowering_with_root(source)?;
    let errors = lowering
        .errors
        .iter()
        .map(format_body_lowering_error)
        .collect();
    let host_manifest = host_manifest_from_lowering(&lowering)?;
    let application_provenance = lowering.application_provenance().clone();
    let subtype_provenance = lowering.subtype_provenance().clone();
    let selection_provenance = selection_provenance_from_lowering(&lowering);
    Ok(BuildPolyOutput {
        arena: lowering.session.poly,
        subtype_provenance,
        application_provenance,
        selection_provenance,
        diagnostic_sources,
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
    let application_provenance = lowering.application_provenance().clone();
    let subtype_provenance = lowering.subtype_provenance().clone();
    let selection_provenance = selection_provenance_from_lowering(&lowering);
    Ok(BuildPolyOutput {
        arena: lowering.session.poly,
        subtype_provenance,
        application_provenance,
        selection_provenance,
        diagnostic_sources: RuntimeDiagnosticSources::default(),
        labels: lowering.labels,
        host_manifest: Some(host_manifest),
        file_count,
        errors,
    })
}

pub fn warm_embedded_std_compiled_unit_artifact_prefix(
    artifact: crate::cache::CachedCompiledUnitArtifact,
) -> Result<(), RouteError> {
    warm_embedded_std_prefix_from_artifact(artifact)
}

pub fn build_poly_from_source_text_with_embedded_playground_std(
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
) -> Result<BuildPolyOutput, RouteError> {
    let source = source.into();
    let diagnostic_sources =
        RuntimeDiagnosticSources::from_collected_sources(&[CollectedSource::new(
            entry.as_ref().to_path_buf(),
            Path::default(),
            source_with_implicit_prelude_only(source.clone()),
        )]);
    let (lowering, file_count) = embedded_playground_std_lowering_with_root(source)?;
    let errors = lowering
        .errors
        .iter()
        .map(format_body_lowering_error)
        .collect();
    let host_manifest = host_manifest_from_lowering(&lowering)?;
    let application_provenance = lowering.application_provenance().clone();
    let subtype_provenance = lowering.subtype_provenance().clone();
    let selection_provenance = selection_provenance_from_lowering(&lowering);
    Ok(BuildPolyOutput {
        arena: lowering.session.poly,
        subtype_provenance,
        application_provenance,
        selection_provenance,
        diagnostic_sources,
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
    let application_provenance = lowering.application_provenance().clone();
    let subtype_provenance = lowering.subtype_provenance().clone();
    let selection_provenance = selection_provenance_from_lowering(&lowering);
    Ok(BuildPolyOutput {
        arena: lowering.session.poly,
        subtype_provenance,
        application_provenance,
        selection_provenance,
        diagnostic_sources: RuntimeDiagnosticSources::default(),
        labels: lowering.labels,
        host_manifest: Some(host_manifest),
        file_count,
        errors,
    })
}

pub fn warm_embedded_playground_std_compiled_unit_artifact_prefix(
    artifact: crate::cache::CachedCompiledUnitArtifact,
) -> Result<(), RouteError> {
    warm_embedded_playground_std_prefix_from_artifact(artifact)
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckPolyOutput {
    pub text: String,
    pub file_count: usize,
    pub diagnostics: Vec<SourceDiagnostic>,
    pub diagnostic_source: Option<CheckDiagnosticSource>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseDiagnosticsOutput {
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

    pub(crate) fn focus_file(&self) -> &SourceFileIdentity {
        &self.focus_module
    }

    pub(crate) fn source_file(&self, file: &SourceFileIdentity) -> Option<(&FsPath, &str, usize)> {
        let (path, source) = self.source_index.source_file(file)?;
        Some((path, source, implicit_source_prefix_len(source)))
    }

    fn loaded_byte_offset(&self, root_byte_offset: usize) -> usize {
        root_byte_offset + self.byte_offset_adjust
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceHover {
    pub range: SourceRange,
    pub contents: String,
    pub documentation: Option<SourceHoverDocumentationDraft>,
}

/// Static hover bytes plus an optional owned input for deferred Yumark rendering.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceHoverDocumentationDraft {
    pub fallback_markdown: String,
    pub lazy_render_input: Option<infer::doc_comment_render_input::DocCommentRenderInput>,
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

pub type SourceFileIdentity = sources::Path;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceDiagnostic {
    pub severity: SourceDiagnosticSeverity,
    pub code: Option<String>,
    pub label: Option<String>,
    pub file: Option<SourceFileIdentity>,
    pub range: Option<SourceRange>,
    pub message: String,
    pub hint: Option<String>,
    pub related: Vec<SourceDiagnosticRelated>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceDiagnosticRelated {
    pub message: String,
    pub file: SourceFileIdentity,
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
    pub program: control_ir::Program,
    pub runtime_evidence: specialize::RuntimeEvidenceSurface,
    pub application_provenance: RuntimeApplicationProvenance,
    pub selection_provenance: RuntimeSelectionProvenance,
    pub diagnostic_sources: RuntimeDiagnosticSources,
    pub labels: poly::dump::DumpLabels,
    pub file_count: usize,
    /// body lowering が報告したエラーの表示用整形。artifact とは別に stderr へ流す。
    pub errors: Vec<String>,
}

pub struct BuildPolyOutput {
    pub arena: poly::expr::Arena,
    pub subtype_provenance: poly::provenance::SubtypeProvenanceSidecar,
    pub application_provenance: infer::lowering::ApplicationProvenanceTable,
    pub selection_provenance: infer::lowering::SelectionProvenanceTable,
    pub diagnostic_sources: RuntimeDiagnosticSources,
    pub labels: poly::dump::DumpLabels,
    pub host_manifest: Option<poly::host_manifest::HostActManifest>,
    pub file_count: usize,
    /// body lowering が報告したエラーの表示用整形。artifact とは別に stderr へ流す。
    pub errors: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpecializeDiagnosticContext {
    pub source: CheckDiagnosticSource,
    pub file: SourceFileIdentity,
    pub range: SourceRange,
    pub related: Vec<SourceDiagnosticRelated>,
}

/// Sparse source identity retained alongside the runtime control program.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeApplicationProvenance {
    source: infer::lowering::ApplicationProvenanceTable,
    control: control_ir::ApplicationProvenanceTable,
}

impl RuntimeApplicationProvenance {
    pub fn new(
        source: infer::lowering::ApplicationProvenanceTable,
        control: control_ir::ApplicationProvenanceTable,
    ) -> Self {
        Self { source, control }
    }

    pub fn resolve(
        &self,
        site: control_ir::ExprId,
    ) -> Option<&infer::lowering::ApplicationProvenance> {
        let tag = self.control.get(site)?;
        self.source.get(poly::expr::ExprId(tag.poly_expr))
    }
}

/// Sparse source selection identity retained alongside the runtime control program.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeSelectionProvenance {
    source: infer::lowering::SelectionProvenanceTable,
    control: control_ir::SelectionProvenanceTable,
}

impl RuntimeSelectionProvenance {
    pub fn new(
        source: infer::lowering::SelectionProvenanceTable,
        control: control_ir::SelectionProvenanceTable,
    ) -> Self {
        Self { source, control }
    }

    pub fn resolve(&self, site: control_ir::ExprId) -> Option<&infer::SourceSpan> {
        let tag = self.control.get(site)?;
        self.source.selection_span(poly::expr::SelectId(tag.select))
    }
}

/// Source texts and filesystem identities used only when rendering runtime diagnostics.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct RuntimeDiagnosticSources {
    source_index: SourceFileIndex,
}

impl RuntimeDiagnosticSources {
    pub fn from_collected_sources(files: &[CollectedSource]) -> Self {
        Self {
            source_index: SourceFileIndex::from_collected_sources(files),
        }
    }

    pub fn source_for_span(&self, span: &infer::SourceSpan) -> Option<RuntimeDiagnosticSource> {
        let location = self.source_index.location_for_span(span)?;
        let source = self.source_index.source_for_location(&location)?;
        let range_offset = implicit_source_prefix_len(source);
        Some(RuntimeDiagnosticSource {
            path: location.path,
            source: CheckDiagnosticSource {
                source: source.get(range_offset..).unwrap_or_default().to_string(),
                range_offset,
            },
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeDiagnosticSource {
    pub path: PathBuf,
    pub source: CheckDiagnosticSource,
}

impl BuildPolyOutput {
    pub fn ensure_runtime_ready(&self) -> Result<(), RouteError> {
        reject_runtime_lowering_errors(&self.errors)
    }
}

pub fn specialize_route_error(
    error: specialize::SpecializeError,
    output: &BuildPolyOutput,
) -> RouteError {
    let Some(context) = specialize_diagnostic_context(&error, output) else {
        return RouteError::Specialize(error);
    };
    RouteError::SpecializeDiagnostic { error, context }
}

fn specialize_diagnostic_context(
    error: &specialize::SpecializeError,
    output: &BuildPolyOutput,
) -> Option<SpecializeDiagnosticContext> {
    if let Some(diagnostic) = source_diagnostic_from_specialize_implicit_cast_error(error, output) {
        let (Some(file), Some(range)) = (diagnostic.file, diagnostic.range) else {
            return None;
        };
        let source_span = infer::SourceSpan {
            file: file.clone(),
            range,
        };
        let source = output
            .diagnostic_sources
            .source_for_span(&source_span)?
            .source;
        return Some(SpecializeDiagnosticContext {
            source,
            file,
            range,
            related: diagnostic.related,
        });
    }
    if let Some(context) = general_subtype_diagnostic_context(error, output) {
        return Some(context);
    }
    let (select, candidates) = match error {
        specialize::SpecializeError::UnresolvedTypeclassMethod { expr, .. } => {
            let poly::expr::Expr::Select(_, select) = output.arena.exprs().get(*expr as usize)?
            else {
                return None;
            };
            (*select, &[][..])
        }
        specialize::SpecializeError::AmbiguousTypeclassMethod {
            expr, candidates, ..
        } => {
            let poly::expr::Expr::Select(_, select) = output.arena.exprs().get(*expr as usize)?
            else {
                return None;
            };
            (*select, candidates.as_slice())
        }
        specialize::SpecializeError::UnsatisfiedSubtype {
            origin:
                Some(specialize::UnsatisfiedSubtypeOrigin::MissingRecordField {
                    select: Some(select),
                    ..
                }),
            ..
        } => (*select, &[][..]),
        _ => return None,
    };
    let selection_span = output.selection_provenance.selection_span(select)?;
    let source = output
        .diagnostic_sources
        .source_for_span(selection_span)?
        .source;
    let related = candidates
        .iter()
        .map(|candidate| {
            let candidate = poly::expr::DefId(candidate.0);
            let span = output.selection_provenance.definition_span(candidate)?;
            Some(SourceDiagnosticRelated {
                message: role_method_candidate_message(&output.arena, &output.labels, candidate),
                file: span.file.clone(),
                range: span.range,
                origin: Some(SourceDiagnosticRelatedOrigin::ImplCandidate),
            })
        })
        .collect::<Option<Vec<_>>>()?;
    Some(SpecializeDiagnosticContext {
        source,
        file: selection_span.file.clone(),
        range: selection_span.range,
        related,
    })
}

fn general_subtype_diagnostic_context(
    error: &specialize::SpecializeError,
    output: &BuildPolyOutput,
) -> Option<SpecializeDiagnosticContext> {
    let specialize::SpecializeError::UnsatisfiedSubtype {
        lower,
        upper,
        origin: None,
        provenance: Some(provenance),
    } = error
    else {
        return None;
    };
    if provenance.completeness != poly::provenance::ProvenanceCompleteness::Complete {
        return None;
    }

    let mut related = Vec::new();
    append_complete_subtype_causes(
        &mut related,
        &output.subtype_provenance.snapshot,
        &provenance.lower,
        lower,
    );
    append_complete_subtype_causes(
        &mut related,
        &output.subtype_provenance.snapshot,
        &provenance.upper,
        upper,
    );
    let first = related.first()?;
    let source_span = infer::SourceSpan {
        file: first.file.clone(),
        range: first.range,
    };
    let source = output
        .diagnostic_sources
        .source_for_span(&source_span)?
        .source;
    Some(SpecializeDiagnosticContext {
        source,
        file: first.file.clone(),
        range: first.range,
        related,
    })
}

fn append_complete_subtype_causes(
    related: &mut Vec<SourceDiagnosticRelated>,
    snapshot: &poly::provenance::PortableProvenanceSnapshot,
    anchors: &[poly::provenance::ProvenanceAnchor],
    ty: &specialize::mono::Type,
) {
    if anchors.is_empty() {
        return;
    }
    // The public query reports completeness for both endpoint groups together. Supplying the same
    // roots to both groups isolates this endpoint without making an absent opposite endpoint turn a
    // complete contribution into `IncompleteProvenance`.
    let explanation = infer::constraints::explain_portable_subtype(
        snapshot,
        anchors,
        anchors,
        infer::constraints::PortableExplanationBudget::default(),
    );
    if explanation.completeness != infer::constraints::DiagnosticExplanationCompleteness::Complete
        || explanation.truncation.is_some()
    {
        return;
    }
    let rendered_type = specialize::mono::dump::dump_type(ty);
    for cause in explanation.lower_sites {
        if related.iter().any(|existing| {
            existing.file == cause.source_span.file && existing.range == cause.source_span.range
        }) {
            continue;
        }
        related.push(SourceDiagnosticRelated {
            message: subtype_cause_related_message(cause.role, &rendered_type),
            file: cause.source_span.file,
            range: cause.source_span.range,
            origin: Some(subtype_cause_related_origin(cause.role)),
        });
    }
}

fn subtype_cause_related_message(
    role: infer::constraints::DiagnosticTypeCauseRole,
    ty: &str,
) -> String {
    match role {
        infer::constraints::DiagnosticTypeCauseRole::InferredFromExpression => {
            format!("type `{ty}` is inferred from this expression")
        }
        infer::constraints::DiagnosticTypeCauseRole::RequiredByAnnotation => {
            format!("type `{ty}` is required by this annotation")
        }
        infer::constraints::DiagnosticTypeCauseRole::RequiredByPattern => {
            format!("this pattern requires a value compatible with `{ty}`")
        }
        infer::constraints::DiagnosticTypeCauseRole::RequiredByBodyUse(kind) => {
            body_requirement_related_message(kind, ty)
        }
        infer::constraints::DiagnosticTypeCauseRole::RequiredByApplication => {
            format!("this callee requires an argument compatible with `{ty}`")
        }
    }
}

fn subtype_cause_related_origin(
    role: infer::constraints::DiagnosticTypeCauseRole,
) -> SourceDiagnosticRelatedOrigin {
    match role {
        infer::constraints::DiagnosticTypeCauseRole::RequiredByAnnotation => {
            SourceDiagnosticRelatedOrigin::TypeAnnotation
        }
        infer::constraints::DiagnosticTypeCauseRole::InferredFromExpression
        | infer::constraints::DiagnosticTypeCauseRole::RequiredByPattern
        | infer::constraints::DiagnosticTypeCauseRole::RequiredByBodyUse(_)
        | infer::constraints::DiagnosticTypeCauseRole::RequiredByApplication => {
            SourceDiagnosticRelatedOrigin::Expression
        }
    }
}

fn source_diagnostic_from_specialize_implicit_cast_error(
    error: &specialize::SpecializeError,
    output: &BuildPolyOutput,
) -> Option<SourceDiagnostic> {
    let (code, hint, owner, candidates) = match error {
        specialize::SpecializeError::UnsatisfiedSubtype {
            origin: Some(specialize::UnsatisfiedSubtypeOrigin::MissingImplicitCast { owner, .. }),
            ..
        } => (
            "yulang.missing-implicit-cast",
            missing_implicit_cast_hint(error)?,
            *owner,
            &[][..],
        ),
        specialize::SpecializeError::AmbiguousImplicitCast {
            owner, candidates, ..
        } => (
            "yulang.ambiguous-implicit-cast",
            "declare or import only one matching `cast` for this pair".to_string(),
            *owner,
            candidates.as_slice(),
        ),
        _ => return None,
    };
    let span = owner.and_then(|owner| output.selection_provenance.definition_span(owner).cloned());
    Some(SourceDiagnostic {
        severity: SourceDiagnosticSeverity::Error,
        code: Some(code.to_string()),
        label: None,
        file: span.as_ref().map(|span| span.file.clone()),
        range: span.as_ref().map(|span| span.range),
        message: format_specialize_implicit_cast_error(error)?,
        hint: Some(hint),
        related: specialize_implicit_cast_candidate_related(output, candidates),
    })
}

fn missing_implicit_cast_hint(error: &specialize::SpecializeError) -> Option<String> {
    let specialize::SpecializeError::UnsatisfiedSubtype {
        origin:
            Some(specialize::UnsatisfiedSubtypeOrigin::MissingImplicitCast { source, target, .. }),
        ..
    } = error
    else {
        return None;
    };
    Some(format!(
        "declare a `cast` from `{}` to `{}`, or check whether a different type was intended",
        source.join("::"),
        target.join("::"),
    ))
}

fn specialize_implicit_cast_candidate_related(
    output: &BuildPolyOutput,
    candidates: &[poly::expr::DefId],
) -> Vec<SourceDiagnosticRelated> {
    candidates
        .iter()
        .filter_map(|candidate| {
            let span = output.selection_provenance.definition_span(*candidate)?;
            Some(SourceDiagnosticRelated {
                message: implicit_cast_candidate_message(&output.labels, *candidate),
                file: span.file.clone(),
                range: span.range,
                origin: None,
            })
        })
        .collect()
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
    SpecializeDiagnostic {
        error: specialize::SpecializeError,
        context: SpecializeDiagnosticContext,
    },
    Runtime(mono_runtime::RuntimeError),
    ControlLower(control_ir::LowerError),
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
                write!(f, "failed to build host act manifest: ")?;
                match error {
                    infer::host_acts::HostActManifestBuildError::MissingHostOperationScheme {
                        act_id,
                        operation_id,
                    } => write!(
                        f,
                        "host operation `{act_id}.{operation_id}` has no compiled type scheme"
                    ),
                    infer::host_acts::HostActManifestBuildError::UnknownRawCompatOverride {
                        act_id,
                        operation_id,
                    } => write!(
                        f,
                        "raw-compatible host operation `{act_id}.{operation_id}` is not declared"
                    ),
                    infer::host_acts::HostActManifestBuildError::Manifest(error) => match error {
                        poly::host_manifest::HostManifestError::DuplicateAct { act_id } => {
                            write!(f, "host act `{act_id}` is declared more than once")
                        }
                        poly::host_manifest::HostManifestError::DuplicateOperation {
                            act_id,
                            operation_id,
                        } => write!(
                            f,
                            "host operation `{act_id}.{operation_id}` is declared more than once"
                        ),
                        poly::host_manifest::HostManifestError::DuplicateOperationPath { path } => {
                            write!(
                                f,
                                "host operation path `{}` is used more than once",
                                path.join("::")
                            )
                        }
                        poly::host_manifest::HostManifestError::UnknownAct {
                            act_id,
                            operation_id,
                        } => write!(
                            f,
                            "host operation `{act_id}.{operation_id}` references undeclared host act `{act_id}`"
                        ),
                        poly::host_manifest::HostManifestError::OperationPathOutsideAct {
                            act_id,
                            operation_id,
                            act_path,
                            operation_path,
                        } => write!(
                            f,
                            "host operation `{act_id}.{operation_id}` path `{}` is outside host act path `{}`",
                            operation_path.join("::"),
                            act_path.join("::")
                        ),
                    },
                }
            }
            RouteError::Specialize(error) => write!(f, "{error}"),
            RouteError::SpecializeDiagnostic { error, .. } => write!(f, "{error}"),
            RouteError::Runtime(error) => write!(f, "{error}"),
            RouteError::ControlLower(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for RouteError {}

struct CheckPolyTimings {
    collect: Duration,
    load: Duration,
    source_load: sources::SourceLoadTiming,
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
    let (loaded, source_load) = load_collected_sources_timed(files);
    let load = load_start.elapsed();
    check_poly_from_loaded_files(loaded, collect, load, source_load, total_start, kind)
}

fn check_poly_from_loaded_files(
    loaded: Vec<sources::LoadedFile>,
    collect: Duration,
    load: Duration,
    source_load: sources::SourceLoadTiming,
    total_start: Instant,
    kind: CheckPolyKind,
) -> Result<CheckPolyOutput, RouteError> {
    let check = infer::check::check_loaded_files(&loaded).map_err(RouteError::Lower)?;
    let timing = CheckPolyTimings {
        collect,
        load,
        source_load,
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

pub fn parse_diagnostics_from_collected_sources(
    files: &[CollectedSource],
) -> ParseDiagnosticsOutput {
    let loaded = load_collected_sources(files.to_vec());
    ParseDiagnosticsOutput {
        diagnostics: parser_diagnostics_from_loaded(&loaded),
        diagnostic_source: check_diagnostic_source(&loaded),
    }
}

fn check_diagnostic_source(loaded: &[sources::LoadedFile]) -> Option<CheckDiagnosticSource> {
    let root = loaded
        .iter()
        .find(|file| file.module_path.segments.is_empty())?;
    let source = root.source.as_str();
    let range_offset = implicit_source_prefix_len(source);
    Some(CheckDiagnosticSource {
        source: source.get(range_offset..).unwrap_or_default().to_string(),
        range_offset,
    })
}

fn implicit_source_prefix_len(source: &str) -> usize {
    if source.starts_with(IMPLICIT_PRELUDE_IMPORT)
        && source
            .get(IMPLICIT_PRELUDE_IMPORT.len()..)
            .is_some_and(|rest| rest.starts_with(IMPLICIT_STD_MODULE_DECL))
    {
        IMPLICIT_STD_SOURCE_PREFIX_LEN
    } else if source.starts_with(IMPLICIT_PRELUDE_IMPORT) {
        IMPLICIT_PRELUDE_IMPORT.len()
    } else {
        0
    }
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
                file: Some(root.module_path.clone()),
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
        let range = effect_operation_reference_range(check, reference, target, span.range);
        push_best_hover(
            &mut best,
            hover_for_def(check, &format_context, target, range),
            range,
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
    if let Some(hover) = hover_for_effect_operation(check, format_context, def, range) {
        return Some(hover);
    }
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
        documentation: doc_comment_hover_draft(check, def),
    })
}

fn hover_for_effect_operation(
    check: &infer::check::PolyCheckOutput,
    format_context: &HoverFormatContext<'_>,
    def: poly::expr::DefId,
    range: SourceRange,
) -> Option<SourceHover> {
    let operation = check.lowering.session.poly.effect_operations.get(&def)?;
    let raw_label = check.lowering.labels.def_label(def)?;
    if hover_label_is_hidden(raw_label) {
        return None;
    }
    let poly::expr::Def::Let {
        scheme: Some(scheme),
        ..
    } = check.lowering.session.poly.defs.get(def)?
    else {
        return None;
    };
    let label = operation.path.last()?;
    let ty = format_context.format_scheme(scheme);
    Some(SourceHover {
        range,
        contents: format!("{label}: {ty}"),
        documentation: doc_comment_hover_draft(check, def),
    })
}

fn effect_operation_reference_range(
    check: &infer::check::PolyCheckOutput,
    reference: poly::expr::RefId,
    target: poly::expr::DefId,
    range: SourceRange,
) -> SourceRange {
    if !check
        .lowering
        .session
        .poly
        .effect_operations
        .contains_key(&target)
    {
        return range;
    }
    let Some(reference_label) = check
        .lowering
        .labels
        .ref_labels()
        .find_map(|(id, label)| (id == reference).then_some(label))
    else {
        return range;
    };
    let operation_label = reference_label
        .rsplit_once("::")
        .map(|(_, operation)| operation)
        .unwrap_or(reference_label);
    let Some(end) = range.start.checked_add(reference_label.len()) else {
        return range;
    };
    let Some(start) = end.checked_sub(operation_label.len()) else {
        return range;
    };
    if end > range.end {
        return range;
    }
    SourceRange { start, end }
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
        infer::uses::LocalDefRole::Input => format_context.format_input_type(local.value),
        infer::uses::LocalDefRole::Value => format_context.format_value_type(local.value),
    };
    Some(SourceHover {
        range,
        contents: format!("{label}: {ty}"),
        documentation: None,
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
        documentation: None,
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
        documentation: doc_comment_hover_draft(check, def),
    })
}

fn hover_label_is_hidden(label: &str) -> bool {
    label.split('.').any(|segment| {
        // `#` and `&` labels are generated by lowering for act copies, sub labels,
        // and mutable local refs. They carry internal type state, not source names.
        segment.starts_with('#') || segment.contains('#') || segment.starts_with('&')
    })
}

fn doc_comment_hover_draft(
    check: &infer::check::PolyCheckOutput,
    def: poly::expr::DefId,
) -> Option<SourceHoverDocumentationDraft> {
    let doc = check.lowering.modules.def_doc_comment(def)?;
    let fallback_markdown = infer::doc_comment_render::render_doc_comment_markdown(doc);
    if fallback_markdown.is_empty() {
        return None;
    }
    let lazy_render_input =
        infer::doc_comment_render::doc_comment_is_safe_for_yumark_literal_reparse(doc).then(|| {
            infer::doc_comment_render_input::DocCommentRenderInput::from_safe_doc_comment(doc)
        });
    Some(SourceHoverDocumentationDraft {
        fallback_markdown,
        lazy_render_input,
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
        poly::dump::format_scheme_public_with_path_rewriter(
            &self.check.lowering.session.poly.typ,
            scheme,
            &|path| self.rewrite_type_path(path),
        )
        .text
    }

    fn format_value_type(&self, value: poly::types::TypeVar) -> String {
        infer::check::format_inferred_value_type_public_with_path_rewriter(
            &self.check.lowering,
            value,
            &|path| self.rewrite_type_path(path),
        )
        .text
    }

    fn format_input_type(&self, value: poly::types::TypeVar) -> String {
        infer::check::format_inferred_input_type_public_with_path_rewriter(
            &self.check.lowering,
            value,
            &|path| self.rewrite_type_path(path),
        )
        .text
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

#[derive(Debug, Clone, Default, PartialEq, Eq)]
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

    fn source_file(&self, file: &Path) -> Option<(&FsPath, &str)> {
        let path = self.paths_by_module.get(file)?;
        let source = self.sources_by_path.get(path)?;
        Some((path.as_path(), source.as_str()))
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
            source_diagnostic_from_body_lowering_error(
                error,
                &check.lowering.modules,
                &check.lowering.labels,
                diagnostic.def,
                diagnostic.label.clone(),
            )
        })
        .collect()
}

fn source_diagnostic_from_body_lowering_error(
    error: &infer::lowering::BodyLoweringError,
    modules: &infer::ModuleTable,
    labels: &poly::dump::DumpLabels,
    def: Option<poly::expr::DefId>,
    label: Option<String>,
) -> SourceDiagnostic {
    let span = body_lowering_error_source_span(error, modules)
        .or_else(|| def.and_then(|def| modules.def_source_span(def).cloned()));
    let label = match error {
        infer::lowering::BodyLoweringError::RoleImplAssociatedTypeMismatch { method, .. } => {
            Some(method.clone())
        }
        _ => label,
    };
    SourceDiagnostic {
        severity: SourceDiagnosticSeverity::Error,
        code: body_lowering_error_code(error).map(str::to_string),
        label,
        file: span.as_ref().map(|span| span.file.clone()),
        range: span.as_ref().map(|span| span.range),
        message: format_body_lowering_error(error),
        hint: body_lowering_error_hint(error),
        related: body_lowering_error_related(error, modules, labels),
    }
}

fn source_diagnostics_for_check(
    check: &infer::check::PolyCheckOutput,
    diagnostics: &[infer::check::CheckDiagnostic],
) -> Vec<SourceDiagnostic> {
    let mut out = source_diagnostics_from_check(check, diagnostics);
    if check.lowering.errors.is_empty() {
        out.extend(role_method_diagnostics_from_check(check));
    }
    out
}

fn role_method_diagnostics_from_check(
    check: &infer::check::PolyCheckOutput,
) -> Vec<SourceDiagnostic> {
    specialize::role_method_check(
        &check.lowering.session.poly,
        check.lowering.subtype_provenance(),
    )
    .into_iter()
    .filter_map(|outcome| source_diagnostic_from_role_method_check_outcome(check, outcome))
    .collect()
}

fn source_diagnostic_from_role_method_check_outcome(
    check: &infer::check::PolyCheckOutput,
    outcome: specialize::RoleMethodCheckOutcome,
) -> Option<SourceDiagnostic> {
    let span = role_method_select_source_span(check, outcome.select);
    match outcome.resolution {
        specialize::RoleMethodCheckResolution::Unresolved => Some(SourceDiagnostic {
            severity: SourceDiagnosticSeverity::Error,
            code: Some("yulang.unresolved-method".to_string()),
            label: role_method_diagnostic_label(check, outcome.select),
            file: span.as_ref().map(|span| span.file.clone()),
            range: span.as_ref().map(|span| span.range),
            message: format!(
                "no role implementation satisfies this method call for receiver {}",
                specialize::mono::dump::dump_type(&outcome.receiver)
            ),
            hint: Some(
                "add or import an impl for the receiver type, or call a method supported by that value"
                    .to_string(),
            ),
            related: Vec::new(),
        }),
        specialize::RoleMethodCheckResolution::Ambiguous(candidates) => Some(SourceDiagnostic {
            severity: SourceDiagnosticSeverity::Error,
            code: Some("yulang.ambiguous-method".to_string()),
            label: role_method_diagnostic_label(check, outcome.select),
            file: span.as_ref().map(|span| span.file.clone()),
            range: span.as_ref().map(|span| span.range),
            message: format!(
                "more than one role implementation satisfies this method call for receiver {}",
                specialize::mono::dump::dump_type(&outcome.receiver)
            ),
            hint: Some(
                "make the receiver type more specific or keep only one matching impl in scope"
                    .to_string(),
            ),
            related: role_method_candidate_related(check, &candidates),
        }),
        specialize::RoleMethodCheckResolution::Resolved(_)
        | specialize::RoleMethodCheckResolution::DefaultBody => None,
    }
}

fn role_method_select_source_span(
    check: &infer::check::PolyCheckOutput,
    select: poly::expr::SelectId,
) -> Option<infer::SourceSpan> {
    check
        .lowering
        .session
        .selections
        .source_span(select)
        .cloned()
}

fn role_method_diagnostic_label(
    check: &infer::check::PolyCheckOutput,
    select: poly::expr::SelectId,
) -> Option<String> {
    Some(check.lowering.session.poly.select(select).name.clone())
}

fn role_method_candidate_related(
    check: &infer::check::PolyCheckOutput,
    candidates: &[poly::expr::DefId],
) -> Vec<SourceDiagnosticRelated> {
    candidates
        .iter()
        .filter_map(|candidate| {
            let span = check.lowering.modules.def_source_span(*candidate)?;
            Some(SourceDiagnosticRelated {
                message: role_method_candidate_message(
                    &check.lowering.session.poly,
                    &check.lowering.labels,
                    *candidate,
                ),
                file: span.file.clone(),
                range: span.range,
                origin: Some(SourceDiagnosticRelatedOrigin::ImplCandidate),
            })
        })
        .collect()
}

fn role_method_candidate_message(
    arena: &poly::expr::Arena,
    labels: &poly::dump::DumpLabels,
    candidate: poly::expr::DefId,
) -> String {
    let label = labels.def_label(candidate).or_else(|| {
        arena.role_impls.iter().find_map(|role_impl| {
            role_impl
                .methods
                .iter()
                .find(|method| method.implementation == candidate)
                .and_then(|method| labels.def_label(method.requirement))
        })
    });
    label.map_or_else(
        || "matching impl method candidate".to_string(),
        |label| format!("matching impl method candidate: {label}"),
    )
}

fn body_lowering_error_code(error: &infer::lowering::BodyLoweringError) -> Option<&'static str> {
    match error {
        infer::lowering::BodyLoweringError::Expr { error, .. }
        | infer::lowering::BodyLoweringError::RootExpr { error, .. } => lowering_error_code(error),
        infer::lowering::BodyLoweringError::RoleImplAssociatedTypeMismatch { .. } => {
            Some("yulang.role-impl-associated-type-mismatch")
        }
        infer::lowering::BodyLoweringError::Analysis(
            infer::analysis::AnalysisDiagnostic::MissingImplicitCast { .. },
        ) => Some("yulang.missing-implicit-cast"),
        infer::lowering::BodyLoweringError::Analysis(
            infer::analysis::AnalysisDiagnostic::AmbiguousImplicitCast { .. },
        ) => Some("yulang.ambiguous-implicit-cast"),
        infer::lowering::BodyLoweringError::Analysis(_) => Some("yulang.analysis"),
        infer::lowering::BodyLoweringError::MissingBody { .. } => {
            Some("yulang.missing-local-binding-body")
        }
        infer::lowering::BodyLoweringError::MissingBindingDecl { .. }
        | infer::lowering::BodyLoweringError::MissingModuleDecl { .. }
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
        infer::lowering::LoweringError::RuleRestMustBeLast { .. } => {
            Some("yulang.rule-rest-position")
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

fn body_lowering_error_source_span(
    error: &infer::lowering::BodyLoweringError,
    modules: &infer::ModuleTable,
) -> Option<infer::SourceSpan> {
    match error {
        infer::lowering::BodyLoweringError::Expr { def, error, .. } => {
            let range = lowering_error_source_range(error)?;
            let span = modules.def_source_span(*def)?;
            Some(infer::SourceSpan {
                file: span.file.clone(),
                range,
            })
        }
        infer::lowering::BodyLoweringError::RootExpr { file, error } => {
            lowering_error_source_range(error).map(|range| infer::SourceSpan {
                file: file.clone(),
                range,
            })
        }
        infer::lowering::BodyLoweringError::RoleImplAssociatedTypeMismatch {
            associated,
            impl_source,
            ..
        } => Some(
            associated
                .first()
                .map(|site| site.source.clone())
                .unwrap_or_else(|| impl_source.clone()),
        ),
        infer::lowering::BodyLoweringError::Analysis(
            infer::analysis::AnalysisDiagnostic::MissingImplicitCast { source_span, .. }
            | infer::analysis::AnalysisDiagnostic::AmbiguousImplicitCast { source_span, .. },
        ) => source_span.clone(),
        infer::lowering::BodyLoweringError::MissingBindingDecl { .. }
        | infer::lowering::BodyLoweringError::MissingModuleDecl { .. }
        | infer::lowering::BodyLoweringError::MissingBody { .. }
        | infer::lowering::BodyLoweringError::NonLetDef { .. }
        | infer::lowering::BodyLoweringError::Analysis(_) => None,
    }
}

fn body_lowering_error_related(
    error: &infer::lowering::BodyLoweringError,
    modules: &infer::ModuleTable,
    labels: &poly::dump::DumpLabels,
) -> Vec<SourceDiagnosticRelated> {
    let file = match error {
        infer::lowering::BodyLoweringError::Expr { def, .. } => {
            modules.def_source_span(*def).map(|span| span.file.clone())
        }
        infer::lowering::BodyLoweringError::RootExpr { file, .. } => Some(file.clone()),
        _ => None,
    };
    match error {
        infer::lowering::BodyLoweringError::RoleImplAssociatedTypeMismatch {
            method,
            associated,
            method_source,
            requirement_source,
            ..
        } => {
            let mut related = associated
                .iter()
                .skip(1)
                .map(|site| SourceDiagnosticRelated {
                    message: format!("explicit associated type `{}` is assigned here", site.name),
                    file: site.source.file.clone(),
                    range: site.source.range,
                    origin: Some(SourceDiagnosticRelatedOrigin::TypeAnnotation),
                })
                .collect::<Vec<_>>();
            related.push(SourceDiagnosticRelated {
                message: format!("impl method `{method}` is implemented here"),
                file: method_source.file.clone(),
                range: method_source.range,
                origin: Some(SourceDiagnosticRelatedOrigin::Expression),
            });
            if let Some(source) = requirement_source {
                related.push(SourceDiagnosticRelated {
                    message: format!("role requirement for `{method}` is declared here"),
                    file: source.file.clone(),
                    range: source.range,
                    origin: Some(SourceDiagnosticRelatedOrigin::TypeAnnotation),
                });
            }
            related
        }
        infer::lowering::BodyLoweringError::Analysis(
            infer::analysis::AnalysisDiagnostic::MissingImplicitCast {
                explanation: Some(explanation),
                ..
            },
        ) => {
            let mut related = explanation
                .related_sites
                .iter()
                .map(|site| {
                    let message = match site.role {
                    infer::analysis::DiagnosticTypeExplanationSiteRole::InferredExpression => {
                        format!(
                            "type `{}` is inferred from this argument",
                            explanation.source.join("::")
                        )
                    }
                    infer::analysis::DiagnosticTypeExplanationSiteRole::RequiredApplicationCallee =>
                    {
                        format!(
                            "this callee requires an argument compatible with `{}`",
                            explanation.target.join("::")
                        )
                    }
                    infer::analysis::DiagnosticTypeExplanationSiteRole::RequiredByBodyUse(kind) => {
                        body_requirement_related_message(
                            kind,
                            &explanation.target.join("::"),
                        )
                    }
                };
                    SourceDiagnosticRelated {
                        message,
                        file: site.source_span.file.clone(),
                        range: site.source_span.range,
                        origin: Some(SourceDiagnosticRelatedOrigin::Expression),
                    }
                })
                .collect::<Vec<_>>();
            if let Some(site) = &explanation.body_use {
                let infer::analysis::DiagnosticTypeExplanationSiteRole::RequiredByBodyUse(kind) =
                    site.role
                else {
                    return related;
                };
                related.push(SourceDiagnosticRelated {
                    message: body_requirement_related_message(kind, &explanation.target.join("::")),
                    file: site.source_span.file.clone(),
                    range: site.source_span.range,
                    origin: Some(SourceDiagnosticRelatedOrigin::Expression),
                });
            }
            related
        }
        infer::lowering::BodyLoweringError::Analysis(
            infer::analysis::AnalysisDiagnostic::AmbiguousImplicitCast { candidates, .. },
        ) => candidates
            .iter()
            .filter_map(|candidate| {
                let span = modules.def_source_span(*candidate)?;
                Some(SourceDiagnosticRelated {
                    message: implicit_cast_candidate_message(labels, *candidate),
                    file: span.file.clone(),
                    range: span.range,
                    origin: None,
                })
            })
            .collect(),
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
            ..
        } => {
            let Some(file) = file else {
                return Vec::new();
            };
            let mut related = Vec::new();
            if let Some(range) = expected_range {
                related.push(SourceDiagnosticRelated {
                    message: format!("expected type comes from this type annotation: {expected}"),
                    file: file.clone(),
                    range: *range,
                    origin: Some(SourceDiagnosticRelatedOrigin::TypeAnnotation),
                });
            }
            if let Some(range) = actual_range {
                related.push(SourceDiagnosticRelated {
                    message: format!("actual type comes from this expression: {actual}"),
                    file,
                    range: *range,
                    origin: Some(SourceDiagnosticRelatedOrigin::Expression),
                });
            }
            related
        }
        _ => Vec::new(),
    }
}

fn body_requirement_related_message(
    kind: infer::analysis::BodyRequirementDiagnosticKind,
    target: &str,
) -> String {
    let use_site = match kind {
        infer::analysis::BodyRequirementDiagnosticKind::BooleanCondition => "this condition",
        infer::analysis::BodyRequirementDiagnosticKind::OperatorOperand => "this operator operand",
        infer::analysis::BodyRequirementDiagnosticKind::PatternGuard => "this pattern guard",
        infer::analysis::BodyRequirementDiagnosticKind::CalleeArgument => "this argument",
    };
    format!("this parameter is required to be `{target}` because it is used as {use_site}")
}

fn body_lowering_error_hint(error: &infer::lowering::BodyLoweringError) -> Option<String> {
    match error {
        infer::lowering::BodyLoweringError::Expr { error, .. }
        | infer::lowering::BodyLoweringError::RootExpr { error, .. } => lowering_error_hint(error),
        infer::lowering::BodyLoweringError::RoleImplAssociatedTypeMismatch { .. } => Some(
            "change the associated type assignment or make the method signature and body satisfy it"
                .to_string(),
        ),
        infer::lowering::BodyLoweringError::MissingBody { .. } => {
            Some("write a body expression after `=`".to_string())
        }
        infer::lowering::BodyLoweringError::Analysis(
            infer::analysis::AnalysisDiagnostic::MissingImplicitCast { source, target, .. },
        ) => Some(format!(
            "declare a `cast` from `{}` to `{}`, or check whether a different type was intended",
            source.join("::"),
            target.join("::"),
        )),
        infer::lowering::BodyLoweringError::Analysis(
            infer::analysis::AnalysisDiagnostic::AmbiguousImplicitCast { .. },
        ) => Some("declare or import only one matching `cast` for this pair".to_string()),
        _ => None,
    }
}

fn implicit_cast_candidate_message(
    labels: &poly::dump::DumpLabels,
    candidate: poly::expr::DefId,
) -> String {
    labels.def_label(candidate).map_or_else(
        || "matching cast declaration".to_string(),
        |label| format!("matching cast declaration: {label}"),
    )
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
        infer::lowering::LoweringError::RuleRestMustBeLast { .. } => {
            Some("move `..` to the end of this rule branch".to_string())
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
        infer::lowering::LoweringError::UnsupportedRuleLazyQuantifier { source_range, .. }
        | infer::lowering::LoweringError::RuleRestMustBeLast { source_range } => {
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
    let program = specialize::specialize(
        &output.arena,
        &poly::provenance::SubtypeProvenanceSidecar::empty(),
    )
    .map_err(|error| specialize_route_error(error, &output))?;
    Ok(SpecializedMonoOutput {
        program,
        labels: output.labels,
        file_count: output.file_count,
        errors: output.errors,
    })
}

fn build_poly_from_sources(files: Vec<CollectedSource>) -> Result<BuildPolyOutput, RouteError> {
    let diagnostic_sources = RuntimeDiagnosticSources::from_collected_sources(&files);
    let mut output = build_poly_from_loaded_files(load_collected_sources(files))?;
    output.diagnostic_sources = diagnostic_sources;
    Ok(output)
}

fn build_poly_from_sources_with_lowering_timing(
    files: Vec<CollectedSource>,
) -> Result<(BuildPolyOutput, infer::lowering::BodyLoweringTiming), RouteError> {
    let diagnostic_sources = RuntimeDiagnosticSources::from_collected_sources(&files);
    let (mut output, timing) =
        build_poly_from_loaded_files_with_lowering_timing(load_collected_sources(files))?;
    output.diagnostic_sources = diagnostic_sources;
    Ok((output, timing))
}

pub fn build_poly_from_loaded_files(
    loaded: Vec<sources::LoadedFile>,
) -> Result<BuildPolyOutput, RouteError> {
    build_poly_from_loaded_files_with_lowering_timing(loaded).map(|(output, _)| output)
}

fn build_poly_from_loaded_files_with_lowering_timing(
    loaded: Vec<sources::LoadedFile>,
) -> Result<(BuildPolyOutput, infer::lowering::BodyLoweringTiming), RouteError> {
    let lowering = infer::lowering::lower_loaded_files(&loaded).map_err(RouteError::Lower)?;
    let lowering_timing = lowering.timing;
    let errors = lowering
        .errors
        .iter()
        .map(format_body_lowering_error)
        .collect();
    let host_manifest = host_manifest_from_lowering(&lowering)?;
    let application_provenance = lowering.application_provenance().clone();
    let subtype_provenance = lowering.subtype_provenance().clone();
    let selection_provenance = selection_provenance_from_lowering(&lowering);
    Ok((
        BuildPolyOutput {
            arena: lowering.session.poly,
            subtype_provenance,
            application_provenance,
            selection_provenance,
            diagnostic_sources: RuntimeDiagnosticSources::default(),
            labels: lowering.labels,
            host_manifest: Some(host_manifest),
            file_count: loaded.len(),
            errors,
        },
        lowering_timing,
    ))
}

fn load_collected_sources(files: Vec<CollectedSource>) -> Vec<sources::LoadedFile> {
    let (source_files, band_paths) = collected_source_files_and_band_paths(files);
    sources::load_with_band_paths(source_files, band_paths)
}

fn load_collected_sources_timed(
    files: Vec<CollectedSource>,
) -> (Vec<sources::LoadedFile>, sources::SourceLoadTiming) {
    let (source_files, band_paths) = collected_source_files_and_band_paths(files);
    sources::load_with_band_paths_timed(source_files, band_paths)
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
