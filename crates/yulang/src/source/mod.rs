//! 実ファイルから新 `sources` / `infer` route へ渡す source set を作る入口。
//!
//! `sources` crate は in-memory source set の parse/load 層に留め、FS traversal と
//! 実験中の std 取り込みはここへ置く。

mod collector;
mod compilation_units;
mod format;
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
use format::*;
use std_sources::*;

pub use format::{format_run_mono_values, format_run_mono_values_with_labels};
pub use sources::SourceRange;

pub const IMPLICIT_PRELUDE_IMPORT: &str = "use std::prelude::*\n";
pub(crate) const IMPLICIT_STD_MODULE_DECL: &str = "mod std;\n";

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct StdSourceOptions {
    pub std_root: Option<PathBuf>,
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
    let loaded = sources::load(collected_source_files(files.clone()));
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
    Ok(BuildPolyAndCompiledUnitOutput {
        poly: BuildPolyOutput {
            arena: lowering.session.poly,
            labels: lowering.labels,
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
        file_count: artifact.manifest.files.len(),
        errors: artifact.errors,
    }
}

pub fn build_poly_from_compiled_unit_prefix_and_collected_sources(
    prefix: crate::cache::CachedCompiledUnitArtifact,
    suffix: Vec<CollectedSource>,
) -> Result<BuildPolyOutput, RouteError> {
    let output = lower_compiled_unit_prefix_suffix(prefix, suffix)?;
    Ok(BuildPolyOutput {
        arena: output.lowering.session.poly,
        labels: output.lowering.labels,
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
    Ok(BuildPolyAndCompiledUnitOutput {
        poly: BuildPolyOutput {
            arena: output.lowering.session.poly,
            labels: output.lowering.labels,
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
    let loaded = sources::load_suffix_with_syntax_prefix(&syntax, collected_source_files(suffix));
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

/// principal poly artifact から control VM artifact 用 IR を作る。
pub fn build_control_from_poly_output(
    output: &BuildPolyOutput,
) -> Result<BuildControlOutput, RouteError> {
    let mono = specialize::specialize(&output.arena).map_err(RouteError::Specialize)?;
    let program = control_vm::lower(&mono).map_err(RouteError::ControlLower)?;
    Ok(BuildControlOutput {
        program,
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
    analyze_from_sources(
        collect_local_source_text_with_std_context(entry.as_ref(), source.into(), options)?.files,
    )
}

pub fn analyze_entry_source(
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
) -> Result<AnalyzeSourceOutput, RouteError> {
    analyze_from_sources(collect_local_source_text(entry, source.into())?)
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
    let entry = entry.as_ref();
    let base = entry.parent().unwrap_or_else(|| FsPath::new("."));
    let std_root = resolve_std_root(base, options)?;

    let mut collector = Collector::new();
    collector.collect_std_root(&std_root)?;
    collector.collect_entry(entry, true)
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
        files.push(CollectedSource {
            path: entry.to_path_buf(),
            module_path: Path::default(),
            source: source_with_implicit_std_prelude(String::new()),
        });
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
        byte_offset_adjust: IMPLICIT_PRELUDE_IMPORT.len() + IMPLICIT_STD_MODULE_DECL.len(),
    })
}

pub(crate) fn entry_source_with_std_has_implicit_prelude(
    entry: &FsPath,
    options: &StdSourceOptions,
) -> Result<bool, RouteError> {
    let base = entry.parent().unwrap_or_else(|| FsPath::new("."));
    let std_root = resolve_std_root(base, options)?;
    Ok(std_module_path_for_file(&std_root, entry).is_none())
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
    Ok(BuildPolyOutput {
        arena: lowering.session.poly,
        labels: lowering.labels,
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
    Ok(BuildPolyOutput {
        arena: lowering.session.poly,
        labels: lowering.labels,
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
    Ok(BuildPolyOutput {
        arena: lowering.session.poly,
        labels: lowering.labels,
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
    Ok(BuildPolyOutput {
        arena: lowering.session.poly,
        labels: lowering.labels,
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
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AnalyzeSourceOutput {
    pub file_count: usize,
    pub diagnostics: Vec<SourceDiagnostic>,
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
    pub label: Option<String>,
    pub range: Option<SourceRange>,
    pub message: String,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BuildControlOutput {
    pub program: control_vm::Program,
    pub labels: poly::dump::DumpLabels,
    pub file_count: usize,
    /// body lowering が報告したエラーの表示用整形。artifact とは別に stderr へ流す。
    pub errors: Vec<String>,
}

pub struct BuildPolyOutput {
    pub arena: poly::expr::Arena,
    pub labels: poly::dump::DumpLabels,
    pub file_count: usize,
    /// body lowering が報告したエラーの表示用整形。artifact とは別に stderr へ流す。
    pub errors: Vec<String>,
}

pub struct BuildPolyAndCompiledUnitOutput {
    pub poly: BuildPolyOutput,
    pub compiled_unit: crate::cache::CachedCompiledUnitArtifact,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CollectedSource {
    pub path: PathBuf,
    pub module_path: Path,
    pub source: String,
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
    DuplicateModulePath {
        module: Path,
        first: PathBuf,
        second: PathBuf,
    },
    DuplicateModuleFile {
        file: PathBuf,
        first_module: Path,
        second_module: Path,
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
                second_module,
            } => write!(
                f,
                "file {} was loaded as both module {} and {}",
                file.display(),
                format_module_path(first_module),
                format_module_path(second_module)
            ),
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
            RouteError::SyntaxMerge(error) => {
                write!(f, "compiled syntax surface merge failed: {error:?}")
            }
            RouteError::Lower(error) => write!(f, "{error}"),
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
    let loaded = sources::load(collected_source_files(files));
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
    let diagnostics = match &kind {
        CheckPolyKind::All { .. } => {
            source_diagnostics_from_check(&check, &check.report.diagnostics)
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
            source_diagnostics_from_check(&check, &module_check.diagnostics)
        }
    };
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
    })
}

fn analyze_from_sources(files: Vec<CollectedSource>) -> Result<AnalyzeSourceOutput, RouteError> {
    analyze_from_loaded_files(sources::load(collected_source_files(files)))
}

fn analyze_from_loaded_files(
    loaded: Vec<sources::LoadedFile>,
) -> Result<AnalyzeSourceOutput, RouteError> {
    let check = infer::check::check_loaded_files(&loaded).map_err(RouteError::Lower)?;
    let diagnostics = source_diagnostics_from_check(&check, &check.report.diagnostics);
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
    hover_from_loaded_files(
        sources::load(collected_source_files(files)),
        byte_offset,
        file,
    )
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
        sources::load(collected_source_files(files)),
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
        sources::load(collected_source_files(files)),
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
    prepare_rename_from_loaded_files(
        sources::load(collected_source_files(files)),
        byte_offset,
        file,
    )
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
        sources::load(collected_source_files(files)),
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
        poly::expr::SelectResolution::RecordField => None,
    }
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
                label: diagnostic.label.clone(),
                range: body_lowering_error_source_range(error).or_else(|| {
                    diagnostic
                        .def
                        .and_then(|def| check.lowering.modules.def_source_range(def))
                }),
                message: format_body_lowering_error(error),
            }
        })
        .collect()
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

fn lowering_error_source_range(error: &infer::lowering::LoweringError) -> Option<SourceRange> {
    match error {
        infer::lowering::LoweringError::UnresolvedName { source_range, .. } => *source_range,
        infer::lowering::LoweringError::UnsupportedTopLevelVarBinding { source_range, .. } => {
            *source_range
        }
        infer::lowering::LoweringError::UnsupportedRuleLazyQuantifier { source_range, .. } => {
            Some(*source_range)
        }
        _ => None,
    }
}

fn dump_poly_from_sources(
    files: Vec<CollectedSource>,
    kind: DumpPolyKind,
) -> Result<DumpPolyOutput, RouteError> {
    dump_poly_from_loaded_files(sources::load(collected_source_files(files)), kind)
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
    let program = specialize::specialize(&output.arena).map_err(RouteError::Specialize)?;
    Ok(SpecializedMonoOutput {
        program,
        labels: output.labels,
        file_count: output.file_count,
        errors: output.errors,
    })
}

fn build_poly_from_sources(files: Vec<CollectedSource>) -> Result<BuildPolyOutput, RouteError> {
    build_poly_from_loaded_files(sources::load(collected_source_files(files)))
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
    Ok(BuildPolyOutput {
        arena: lowering.session.poly,
        labels: lowering.labels,
        file_count: loaded.len(),
        errors,
    })
}

fn collected_source_files(files: Vec<CollectedSource>) -> Vec<SourceFile> {
    files
        .into_iter()
        .map(|file| SourceFile {
            module_path: file.module_path,
            source: file.source,
        })
        .collect()
}
