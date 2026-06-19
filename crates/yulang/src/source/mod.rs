//! 実ファイルから新 `sources` / `infer` route へ渡す source set を作る入口。
//!
//! `sources` crate は in-memory source set の parse/load 層に留め、FS traversal と
//! 実験中の std 取り込みはここへ置く。

mod collector;
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
    install_embedded_std,
};
use crate::time::{Duration, Instant};

#[cfg(test)]
mod tests;

use collector::*;
use format::*;
use std_sources::*;

pub use format::format_run_mono_values;
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

/// principal poly artifact から control VM artifact 用 IR を作る。
pub fn build_control_from_poly_output(
    output: &BuildPolyOutput,
) -> Result<BuildControlOutput, RouteError> {
    let mono = specialize::specialize(&output.arena).map_err(RouteError::Specialize)?;
    let program = control_vm::lower(&mono).map_err(RouteError::ControlLower)?;
    Ok(BuildControlOutput {
        program,
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
    let mut stdout = String::new();
    let (values, stats, runtime_timings) =
        control_vm::run_program_with_host_stats_and_timings(program, &mut |path, payload| {
            handle_control_host_effect(path, payload, &mut stdout)
        })
        .map_err(RouteError::Control)?;
    let format_start = Instant::now();
    let text = format!("run roots {}\n", control_vm::format_values(&values));
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
        let text = control_host_string_payload(payload)?;
        stdout.push_str(text);
        return Some(control_vm::Value::Unit);
    }
    None
}

fn control_host_string_payload(value: &control_vm::Value) -> Option<&str> {
    match value {
        control_vm::Value::Str(value) => Some(value.as_str()),
        control_vm::Value::Marked { value, .. } => control_host_string_payload(value),
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
    analyze_from_sources(collect_local_source_text_with_std_options(
        entry,
        source.into(),
        options,
    )?)
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
    let loaded_offset =
        byte_offset + IMPLICIT_PRELUDE_IMPORT.len() + IMPLICIT_STD_MODULE_DECL.len();
    hover_from_sources(
        collect_local_source_text_with_std_options(entry, source.into(), options)?,
        loaded_offset,
        &Path::default(),
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
    let entry = entry.as_ref();
    let base = entry.parent().unwrap_or_else(|| FsPath::new("."));
    let std_root = resolve_std_root(base, options)?;

    let mut collector = Collector::new();
    collector.collect_std_root(&std_root)?;
    collector.collect_entry_source(entry, source, true)
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
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
) -> Result<BuildPolyOutput, RouteError> {
    build_poly_from_loaded_files(load_source_text_with_embedded_std(entry, source.into())?)
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
    run_built_control_program(&output.program, output.file_count, output.errors)
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
pub struct SourceDiagnostic {
    pub label: Option<String>,
    pub range: Option<SourceRange>,
    pub message: String,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BuildControlOutput {
    pub program: control_vm::Program,
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CollectedSource {
    pub path: PathBuf,
    pub module_path: Path,
    pub source: String,
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

fn source_hover_from_check(
    check: &infer::check::PolyCheckOutput,
    byte_offset: usize,
    file: &Path,
) -> Option<SourceHover> {
    let mut best = None;
    for (def, span) in check.lowering.modules.def_source_spans() {
        if &span.file != file || !source_range_contains(span.range, byte_offset) {
            continue;
        }
        push_best_hover(&mut best, hover_for_def(check, def, span.range), span.range);
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
            hover_for_def(check, target, span.range),
            span.range,
        );
    }
    best
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
    let label = check.lowering.labels.def_label(def)?;
    if label.starts_with('#') {
        return None;
    }
    let ty = poly::dump::format_scheme(&check.lowering.session.poly.typ, scheme);
    Some(SourceHover {
        range,
        contents: format!("{label}: {ty}"),
    })
}

fn source_range_contains(range: SourceRange, byte_offset: usize) -> bool {
    if range.start == range.end {
        byte_offset == range.start
    } else {
        range.start <= byte_offset && byte_offset < range.end
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
        text: format_run_mono_values(&values),
        file_count: output.file_count,
        errors: output.errors,
        values,
    })
}

fn run_control_from_sources(files: Vec<CollectedSource>) -> Result<RunControlOutput, RouteError> {
    let output = build_control_from_sources(files)?;
    run_built_control_program(&output.program, output.file_count, output.errors)
}

fn build_control_from_sources(
    files: Vec<CollectedSource>,
) -> Result<BuildControlOutput, RouteError> {
    let output = build_poly_from_sources(files)?;
    build_control_from_poly_output(&output)
}

struct SpecializedMonoOutput {
    program: specialize::mono::Program,
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
