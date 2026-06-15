//! 実ファイルから新 `sources` / `infer` route へ渡す source set を作る入口。
//!
//! `sources` crate は in-memory source set の parse/load 層に留め、FS traversal と
//! 実験中の std 取り込みはここへ置く。

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

pub const IMPLICIT_PRELUDE_IMPORT: &str = "use std::prelude::*\n";
const IMPLICIT_STD_MODULE_DECL: &str = "mod std;\n";

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
    let values = control_vm::run_program(program).map_err(RouteError::Control)?;
    Ok(RunControlOutput {
        text: format!("run roots {}\n", control_vm::format_values(&values)),
        file_count,
        errors,
        values,
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

pub fn analyze_source_text_with_embedded_std(
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
) -> Result<AnalyzeSourceOutput, RouteError> {
    analyze_from_sources(collect_source_text_with_embedded_std(entry, source.into())?)
}

pub fn check_poly_from_source_text_with_embedded_std(
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
) -> Result<CheckPolyOutput, RouteError> {
    let total_start = Instant::now();
    let collect_start = Instant::now();
    let files = collect_source_text_with_embedded_std(entry, source.into())?;
    let collect = collect_start.elapsed();
    check_poly_from_sources(
        files,
        collect,
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
    dump_poly_from_sources(
        collect_source_text_with_embedded_std(entry, source.into())?,
        DumpPolyKind::Compact,
    )
}

pub fn dump_poly_raw_from_source_text_with_embedded_std(
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
) -> Result<DumpPolyOutput, RouteError> {
    dump_poly_from_sources(
        collect_source_text_with_embedded_std(entry, source.into())?,
        DumpPolyKind::Raw,
    )
}

pub fn dump_mono_from_source_text_with_embedded_std(
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
) -> Result<DumpMonoOutput, RouteError> {
    dump_mono_from_sources(collect_source_text_with_embedded_std(entry, source.into())?)
}

pub fn build_control_from_source_text_with_embedded_std(
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
) -> Result<BuildControlOutput, RouteError> {
    build_control_from_sources(collect_source_text_with_embedded_std(entry, source.into())?)
}

pub fn build_control_from_source_text_with_embedded_playground_std(
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
) -> Result<BuildControlOutput, RouteError> {
    build_control_from_sources(collect_source_text_with_embedded_playground_std(
        entry,
        source.into(),
    )?)
}

pub fn run_control_from_source_text_with_embedded_std(
    entry: impl AsRef<FsPath>,
    source: impl Into<String>,
) -> Result<RunControlOutput, RouteError> {
    run_control_from_sources(collect_source_text_with_embedded_std(entry, source.into())?)
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
pub struct SourceDiagnostic {
    pub label: Option<String>,
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

struct Collector {
    seen_files: HashSet<PathBuf>,
    module_files: HashMap<Path, PathBuf>,
    files: Vec<CollectedSource>,
}

impl Collector {
    fn new() -> Self {
        Self {
            seen_files: HashSet::new(),
            module_files: HashMap::new(),
            files: Vec::new(),
        }
    }

    fn collect_std_root(&mut self, std_root: &FsPath) -> Result<(), RouteError> {
        self.collect_module_tree(
            std_root.join("std.yu"),
            Path {
                segments: vec![Name("std".to_string())],
            },
        )
    }

    fn collect_entry(
        mut self,
        entry: &FsPath,
        implicit_prelude: bool,
    ) -> Result<Vec<CollectedSource>, RouteError> {
        self.collect_entry_inner(entry, None, implicit_prelude)
    }

    fn collect_entry_source(
        mut self,
        entry: &FsPath,
        source: String,
        implicit_prelude: bool,
    ) -> Result<Vec<CollectedSource>, RouteError> {
        self.collect_entry_inner(entry, Some(source), implicit_prelude)
    }

    fn collect_entry_inner(
        &mut self,
        entry: &FsPath,
        source: Option<String>,
        implicit_prelude: bool,
    ) -> Result<Vec<CollectedSource>, RouteError> {
        let mut queue = VecDeque::from([(entry.to_path_buf(), Path::default(), source)]);
        while let Some((path, module_path, source_override)) = queue.pop_front() {
            let canonical = canonicalize_for_dedupe(&path);
            self.record_module_file(&module_path, &canonical)?;
            if !self.seen_files.insert(canonical) {
                continue;
            }

            let mut source = match source_override {
                Some(source) => source,
                None => fs::read_to_string(&path).map_err(|error| RouteError::Io {
                    path: path.clone(),
                    error,
                })?,
            };
            if implicit_prelude && module_path.segments.is_empty() {
                source = format!("{IMPLICIT_STD_MODULE_DECL}{IMPLICIT_PRELUDE_IMPORT}{source}");
            }

            let requests = discover_module_loads(&module_path, &source);
            self.files.push(CollectedSource {
                path: path.clone(),
                module_path: module_path.clone(),
                source,
            });

            for request in requests {
                let requested_module = request.module_path();
                if self.module_files.contains_key(&requested_module) {
                    continue;
                }
                let child_path = resolve_module_file(&path, &module_path, &request)?;
                queue.push_back((child_path, requested_module, None));
            }
        }
        Ok(std::mem::take(&mut self.files))
    }

    fn collect_module_tree(
        &mut self,
        entry: PathBuf,
        entry_module_path: Path,
    ) -> Result<(), RouteError> {
        let mut queue = VecDeque::from([(entry, entry_module_path)]);
        while let Some((path, module_path)) = queue.pop_front() {
            let canonical = canonicalize_for_dedupe(&path);
            self.record_module_file(&module_path, &canonical)?;
            if !self.seen_files.insert(canonical) {
                continue;
            }

            let source = fs::read_to_string(&path).map_err(|error| RouteError::Io {
                path: path.clone(),
                error,
            })?;
            let requests = discover_module_loads(&module_path, &source);
            self.files.push(CollectedSource {
                path: path.clone(),
                module_path: module_path.clone(),
                source,
            });

            for request in requests {
                let requested_module = request.module_path();
                if self.module_files.contains_key(&requested_module) {
                    continue;
                }
                let child_path = resolve_module_file(&path, &module_path, &request)?;
                queue.push_back((child_path, requested_module));
            }
        }
        Ok(())
    }

    fn record_module_file(&mut self, module: &Path, file: &FsPath) -> Result<(), RouteError> {
        let Some(first) = self.module_files.get(module) else {
            self.module_files.insert(module.clone(), file.to_path_buf());
            return Ok(());
        };
        if first == file {
            return Ok(());
        }
        Err(RouteError::DuplicateModulePath {
            module: module.clone(),
            first: first.clone(),
            second: file.to_path_buf(),
        })
    }
}

struct CheckPolyTimings {
    collect: Duration,
    load: Duration,
    infer: Duration,
    summarize: Duration,
    total: Duration,
}

fn check_poly_from_sources(
    files: Vec<CollectedSource>,
    collect: Duration,
    total_start: Instant,
    kind: CheckPolyKind,
) -> Result<CheckPolyOutput, RouteError> {
    let source_files = files
        .iter()
        .map(|file| SourceFile {
            module_path: file.module_path.clone(),
            source: file.source.clone(),
        })
        .collect::<Vec<_>>();
    let load_start = Instant::now();
    let loaded = sources::load(source_files);
    let load = load_start.elapsed();
    let check = infer::check::check_loaded_files(&loaded).map_err(RouteError::Lower)?;
    let timing = CheckPolyTimings {
        collect,
        load,
        infer: check.timing.infer,
        summarize: check.timing.summarize,
        total: total_start.elapsed(),
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
    let source_files = files
        .iter()
        .map(|file| SourceFile {
            module_path: file.module_path.clone(),
            source: file.source.clone(),
        })
        .collect::<Vec<_>>();
    let loaded = sources::load(source_files);
    let check = infer::check::check_loaded_files(&loaded).map_err(RouteError::Lower)?;
    let diagnostics = source_diagnostics_from_check(&check, &check.report.diagnostics);
    Ok(AnalyzeSourceOutput {
        file_count: loaded.len(),
        diagnostics,
    })
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
                message: format_body_lowering_error(error),
            }
        })
        .collect()
}

fn dump_poly_from_sources(
    files: Vec<CollectedSource>,
    kind: DumpPolyKind,
) -> Result<DumpPolyOutput, RouteError> {
    let source_files = files
        .iter()
        .map(|file| SourceFile {
            module_path: file.module_path.clone(),
            source: file.source.clone(),
        })
        .collect::<Vec<_>>();
    let loaded = sources::load(source_files);
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
    let program = specialize::specialize(&output.arena).map_err(RouteError::Specialize)?;
    Ok(SpecializedMonoOutput {
        program,
        file_count: output.file_count,
        errors: output.errors,
    })
}

fn build_poly_from_sources(files: Vec<CollectedSource>) -> Result<BuildPolyOutput, RouteError> {
    let source_files = files
        .iter()
        .map(|file| SourceFile {
            module_path: file.module_path.clone(),
            source: file.source.clone(),
        })
        .collect::<Vec<_>>();
    let loaded = sources::load(source_files);
    let dump = infer::dump::dump_loaded_files(&loaded).map_err(RouteError::Lower)?;
    let errors = dump
        .lowering
        .errors
        .iter()
        .map(format_body_lowering_error)
        .collect();
    Ok(BuildPolyOutput {
        arena: dump.lowering.session.poly,
        labels: dump.lowering.labels,
        file_count: loaded.len(),
        errors,
    })
}

pub fn format_run_mono_values(values: &[mono_runtime::Value]) -> String {
    let mut out = String::new();
    let _ = write!(out, "run roots [");
    for (index, value) in values.iter().enumerate() {
        if index > 0 {
            let _ = write!(out, ", ");
        }
        let _ = write!(out, "{}", format_runtime_value(value));
    }
    let _ = writeln!(out, "]");
    out
}

fn format_runtime_value(value: &mono_runtime::Value) -> String {
    match value {
        mono_runtime::Value::Int(value) => value.to_string(),
        mono_runtime::Value::BigInt(value) => value.to_string(),
        mono_runtime::Value::Float(value) => value.to_string(),
        mono_runtime::Value::Str(value) => format!("{value:?}"),
        mono_runtime::Value::Bool(value) => value.to_string(),
        mono_runtime::Value::Unit => "()".to_string(),
        mono_runtime::Value::Tuple(values) => format_delimited_values("(", ")", values),
        mono_runtime::Value::List(values) => {
            let values = values
                .to_vec()
                .into_iter()
                .map(|value| (*value).clone())
                .collect::<Vec<_>>();
            format_delimited_values("[", "]", &values)
        }
        mono_runtime::Value::Record(fields) => {
            let mut out = String::new();
            out.push('{');
            for (index, field) in fields.iter().enumerate() {
                if index > 0 {
                    out.push_str(", ");
                }
                let _ = write!(
                    out,
                    "{}: {}",
                    field.name,
                    format_runtime_value(&field.value)
                );
            }
            out.push('}');
            out
        }
        mono_runtime::Value::PolyVariant { tag, payloads } => {
            if payloads.is_empty() {
                return tag.clone();
            }
            format!("{tag}{}", format_delimited_values("(", ")", payloads))
        }
        mono_runtime::Value::DataConstructor { def, payloads } => {
            if payloads.is_empty() {
                return format!("<ctor d{}>", def.0);
            }
            format!(
                "<ctor d{}>{}",
                def.0,
                format_delimited_values("(", ")", payloads)
            )
        }
        mono_runtime::Value::ConstructorFunction(constructor) => {
            format!(
                "<ctor-fn d{} {}/{}>",
                constructor.def.0,
                constructor.args.len(),
                constructor.arity
            )
        }
        mono_runtime::Value::PrimitiveOp(primitive) => {
            format!(
                "<prim {:?} {}/{}>",
                primitive.op,
                primitive.args.len(),
                primitive.op.arity()
            )
        }
        mono_runtime::Value::Closure(_) | mono_runtime::Value::RecursiveClosure { .. } => {
            "<closure>".to_string()
        }
        mono_runtime::Value::Thunk(_) => "<thunk>".to_string(),
        mono_runtime::Value::FunctionAdapter(_) => "<function-adapter>".to_string(),
        mono_runtime::Value::EffectOp { path } => format!("<effect-op {}>", path.join("::")),
        mono_runtime::Value::Continuation(id) => format!("<continuation {}>", id.0),
        mono_runtime::Value::Marked { value, .. } => format_runtime_value(value),
    }
}

fn format_delimited_values(open: &str, close: &str, values: &[mono_runtime::Value]) -> String {
    let mut out = String::new();
    out.push_str(open);
    for (index, value) in values.iter().enumerate() {
        if index > 0 {
            out.push_str(", ");
        }
        out.push_str(&format_runtime_value(value));
    }
    if values.len() == 1 && open == "(" {
        out.push(',');
    }
    out.push_str(close);
    out
}

fn format_check_poly_output(
    file_count: usize,
    check: &infer::check::PolyCheckOutput,
    timing: &CheckPolyTimings,
    title: &str,
) -> String {
    let report = &check.report;
    let totals = &report.totals;
    let mut out = String::new();
    let _ = writeln!(out, "{title}");
    let _ = writeln!(out, "files: {file_count}");
    write_check_timing(&mut out, timing);
    let _ = writeln!(out, "summary:");
    let _ = writeln!(out, "  modules: {}", totals.modules);
    let _ = writeln!(out, "  module values: {}", totals.module_values);
    let _ = writeln!(out, "  type decls: {}", totals.type_decls);
    let _ = writeln!(out, "  child modules: {}", totals.child_modules);
    let _ = writeln!(out, "  let defs: {}", totals.let_defs);
    let _ = writeln!(out, "  typed lets: {}", totals.typed_lets);
    let _ = writeln!(out, "  missing schemes: {}", totals.missing_schemes);
    let _ = writeln!(out, "  bodyless declarations: {}", totals.bodyless_decls);
    let _ = writeln!(out, "  stack schemes: {}", totals.stack_schemes);
    let _ = writeln!(out, "  lowering errors: {}", totals.lowering_errors);
    if totals.unowned_errors > 0 {
        let _ = writeln!(out, "  unowned errors: {}", totals.unowned_errors);
    }

    let _ = writeln!(out, "modules:");
    for module in &report.modules {
        let _ = writeln!(
            out,
            "  {}: values {} typed {} missing_schemes {} bodyless {} stack_schemes {} errors {} types {} child_modules {}",
            infer::check::format_path(&module.path),
            module.value_count,
            module.typed_lets,
            module.missing_schemes,
            module.bodyless_decls,
            module.stack_schemes,
            module.local_errors,
            module.type_count,
            module.child_module_count
        );
    }

    if !report.missing_schemes.is_empty() {
        let _ = writeln!(out, "missing schemes:");
        for item in &report.missing_schemes {
            let _ = writeln!(out, "  d{}: {}", item.def.0, item.label);
        }
    }

    if !report.bodyless_decls.is_empty() {
        let _ = writeln!(out, "bodyless declarations:");
        for item in &report.bodyless_decls {
            let _ = writeln!(out, "  d{}: {}", item.def.0, item.label);
        }
    }

    write_check_diagnostics(&mut out, check, &report.diagnostics);

    out
}

fn format_check_poly_module_output(
    file_count: usize,
    check: &infer::check::PolyCheckOutput,
    module: &infer::check::ModuleCheck,
    timing: &CheckPolyTimings,
    title: &str,
) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "{} {}", title, infer::check::format_path(&module.path));
    let _ = writeln!(out, "files: {file_count}");
    write_check_timing(&mut out, timing);
    let _ = writeln!(out, "summary:");
    let _ = writeln!(out, "  values: {}", module.value_count);
    let _ = writeln!(out, "  typed lets: {}", module.typed_lets);
    let _ = writeln!(out, "  missing schemes: {}", module.missing_schemes);
    let _ = writeln!(out, "  bodyless declarations: {}", module.bodyless_decls);
    let _ = writeln!(out, "  stack schemes: {}", module.stack_schemes);
    let _ = writeln!(
        out,
        "  lowering errors: {} local / {} total",
        module.local_errors, check.report.totals.lowering_errors
    );
    let _ = writeln!(out, "  types: {}", module.type_count);
    let _ = writeln!(out, "  child modules: {}", module.child_module_count);

    if !module.missing_scheme_defs.is_empty() {
        let _ = writeln!(out, "missing schemes:");
        for item in &module.missing_scheme_defs {
            let _ = writeln!(out, "  d{}: {}", item.def.0, item.label);
        }
    }

    if !module.bodyless_defs.is_empty() {
        let _ = writeln!(out, "bodyless declarations:");
        for item in &module.bodyless_defs {
            let _ = writeln!(out, "  d{}: {}", item.def.0, item.label);
        }
    }

    write_check_diagnostics(&mut out, check, &module.diagnostics);

    out
}

fn write_check_timing(out: &mut String, timing: &CheckPolyTimings) {
    let _ = writeln!(out, "timing:");
    let _ = writeln!(out, "  collect: {}", format_duration(timing.collect));
    let _ = writeln!(out, "  load: {}", format_duration(timing.load));
    let _ = writeln!(out, "  infer: {}", format_duration(timing.infer));
    let _ = writeln!(out, "  summarize: {}", format_duration(timing.summarize));
    let _ = writeln!(out, "  total: {}", format_duration(timing.total));
}

fn write_check_diagnostics(
    out: &mut String,
    check: &infer::check::PolyCheckOutput,
    diagnostics: &[infer::check::CheckDiagnostic],
) {
    if diagnostics.is_empty() {
        return;
    }
    let _ = writeln!(out, "lowering errors:");
    for diagnostic in diagnostics {
        let label = diagnostic.label.as_deref().unwrap_or("<unowned>");
        let error = &check.lowering.errors[diagnostic.error_index];
        let _ = writeln!(out, "  {label}: {}", format_body_lowering_error(error));
    }
}

fn format_body_lowering_error(error: &infer::lowering::BodyLoweringError) -> String {
    match error {
        infer::lowering::BodyLoweringError::Expr {
            error: infer::lowering::LoweringError::TypeMismatch { actual, expected },
            ..
        } => format!("type mismatch: {actual} is not {expected}"),
        infer::lowering::BodyLoweringError::Expr {
            error:
                infer::lowering::LoweringError::AnnotationBuild {
                    error: infer::annotation::AnnBuildError::UnresolvedTypeName { path },
                },
            ..
        } => format!("unresolved type name: {}", format_name_path(path)),
        infer::lowering::BodyLoweringError::Expr {
            error:
                infer::lowering::LoweringError::NegSignatureBuild {
                    error: infer::lowering::NegSignatureBuildError::UnresolvedTypeName { path },
                },
            ..
        } => format!("unresolved type name: {}", format_name_path(path)),
        infer::lowering::BodyLoweringError::Expr {
            error: infer::lowering::LoweringError::UnresolvedName { name },
            ..
        } => format!("unresolved value name: {}", name.0),
        infer::lowering::BodyLoweringError::RootExpr {
            error: infer::lowering::LoweringError::UnresolvedName { name },
        } => format!("unresolved value name in root expression: {}", name.0),
        infer::lowering::BodyLoweringError::RootExpr { error } => {
            format!("root expression lowering error: {error:?}")
        }
        infer::lowering::BodyLoweringError::Analysis(
            infer::analysis::AnalysisDiagnostic::ComputedFetchCycle {
                component,
                parent,
                target,
            },
        ) => format!(
            "computed value fetch in recursive component: component {}, edge d{} -> d{}",
            component
                .iter()
                .map(|def| format!("d{}", def.0))
                .collect::<Vec<_>>()
                .join(","),
            parent.0,
            target.0
        ),
        _ => format!("{error:?}"),
    }
}

fn format_name_path(path: &[Name]) -> String {
    path.iter()
        .map(|name| name.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

fn format_duration(duration: Duration) -> String {
    let seconds = duration.as_secs_f64();
    if seconds >= 1.0 {
        return format!("{seconds:.3}s");
    }
    let millis = seconds * 1000.0;
    if millis >= 1.0 {
        return format!("{millis:.1}ms");
    }
    let micros = seconds * 1_000_000.0;
    format!("{micros:.0}us")
}

fn resolve_std_root(base: &FsPath, options: &StdSourceOptions) -> Result<PathBuf, RouteError> {
    if let Some(std_root) = options.std_root.as_ref() {
        if is_std_root(std_root) {
            return Ok(std_root.clone());
        }
        return Err(RouteError::InvalidStdRoot {
            root: std_root.clone(),
        });
    }

    resolve_auto_std_root(base)
}

fn resolve_nearby_std_root(base: &FsPath) -> Option<PathBuf> {
    find_nearby_std_root(base).or_else(|| env_std_root().filter(|root| is_std_root(root)))
}

fn parse_dump_module_path(module: &str) -> Result<Path, RouteError> {
    let separator = if module.contains("::") { "::" } else { "." };
    let raw_segments = module.split(separator).map(str::trim).collect::<Vec<_>>();
    if raw_segments.is_empty() || raw_segments.iter().any(|segment| segment.is_empty()) {
        return Err(RouteError::InvalidDumpModulePath {
            module: module.to_string(),
        });
    }
    let segments = raw_segments
        .into_iter()
        .map(|segment| Name(segment.to_string()))
        .collect::<Vec<_>>();
    Ok(Path { segments })
}

fn resolve_auto_std_root(base: &FsPath) -> Result<PathBuf, RouteError> {
    if let Some(root) = resolve_nearby_std_root(base) {
        return Ok(root);
    }

    let root = default_versioned_std_root();
    install_embedded_std(&root).map_err(|error| RouteError::StdRootInstall {
        root: root.clone(),
        error,
    })?;
    if is_std_root(&root) {
        return Ok(root);
    }

    Err(RouteError::StdRootNotFound {
        base: base.to_path_buf(),
    })
}

fn embedded_std_sources_with_root(entry: &FsPath, source: String) -> Vec<CollectedSource> {
    let mut files = embedded_std_sources();
    files.push(CollectedSource {
        path: entry.to_path_buf(),
        module_path: Path::default(),
        source: format!("{IMPLICIT_STD_MODULE_DECL}{IMPLICIT_PRELUDE_IMPORT}{source}"),
    });
    files
}

fn embedded_playground_std_sources_with_root(
    entry: &FsPath,
    source: String,
) -> Vec<CollectedSource> {
    let mut files = crate::playground_std::embedded_playground_std_sources();
    files.push(CollectedSource {
        path: entry.to_path_buf(),
        module_path: Path::default(),
        source: format!("{IMPLICIT_STD_MODULE_DECL}{IMPLICIT_PRELUDE_IMPORT}{source}"),
    });
    files
}

fn embedded_std_sources() -> Vec<CollectedSource> {
    embedded_std_files()
        .iter()
        .map(|file| CollectedSource {
            path: PathBuf::from("<embedded-std>").join(file.relative_path),
            module_path: embedded_std_module_path(file.relative_path),
            source: file.source.to_string(),
        })
        .collect()
}

fn embedded_std_module_path(relative_path: &str) -> Path {
    let module = relative_path
        .strip_suffix(".yu")
        .unwrap_or(relative_path)
        .trim_matches('/');
    Path {
        segments: module
            .split('/')
            .filter(|segment| !segment.is_empty())
            .map(|segment| Name(segment.to_string()))
            .collect(),
    }
}

fn is_std_root(path: &FsPath) -> bool {
    crate::stdlib::is_std_root(path)
}

fn discover_module_loads(module_path: &Path, source: &str) -> Vec<ModuleLoadRequest> {
    let loaded = sources::load(vec![SourceFile {
        module_path: module_path.clone(),
        source: source.to_string(),
    }]);
    loaded
        .into_iter()
        .next()
        .map(|file| file.module_loads)
        .unwrap_or_default()
}

fn resolve_module_file(
    current: &FsPath,
    current_module: &Path,
    request: &ModuleLoadRequest,
) -> Result<PathBuf, RouteError> {
    let requested_module = request.module_path();
    let relative = relative_module_segments(current_module, &requested_module);
    let candidates = module_file_candidates(current, relative);
    let existing = candidates
        .iter()
        .filter(|path| path.is_file())
        .cloned()
        .collect::<Vec<_>>();

    match existing.as_slice() {
        [path] => Ok(path.clone()),
        [] => Err(RouteError::ModuleNotFound {
            current: current.to_path_buf(),
            module: requested_module,
            candidates,
        }),
        _ => Err(RouteError::AmbiguousModuleFile {
            current: current.to_path_buf(),
            module: requested_module,
            candidates: existing,
        }),
    }
}

fn relative_module_segments<'a>(current: &Path, requested: &'a Path) -> &'a [Name] {
    requested
        .segments
        .strip_prefix(current.segments.as_slice())
        .unwrap_or(requested.segments.as_slice())
}

fn module_file_candidates(current: &FsPath, relative: &[Name]) -> Vec<PathBuf> {
    let mut relative_file = relative_path(relative);
    relative_file.set_extension("yu");

    let parent = current.parent().unwrap_or_else(|| FsPath::new("."));
    let direct = parent.join(&relative_file);
    let nested = current.with_extension("").join(&relative_file);
    if direct == nested {
        vec![direct]
    } else {
        vec![direct, nested]
    }
}

fn relative_path(segments: &[Name]) -> PathBuf {
    let mut path = PathBuf::new();
    for segment in segments {
        path.push(&segment.0);
    }
    path
}

fn format_module_path(path: &Path) -> String {
    if path.segments.is_empty() {
        return "<root>".to_string();
    }
    path.segments
        .iter()
        .map(|name| name.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

fn write_candidates(f: &mut fmt::Formatter<'_>, candidates: &[PathBuf]) -> fmt::Result {
    if candidates.is_empty() {
        return Ok(());
    }
    write!(f, " (candidates: ")?;
    for (idx, candidate) in candidates.iter().enumerate() {
        if idx != 0 {
            write!(f, ", ")?;
        }
        write!(f, "{}", candidate.display())?;
    }
    write!(f, ")")
}

fn canonicalize_for_dedupe(path: &FsPath) -> PathBuf {
    path.canonicalize().unwrap_or_else(|_| path.to_path_buf())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn temp_root(name: &str) -> PathBuf {
        std::env::temp_dir().join(format!(
            "yulang-{name}-{}",
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ))
    }

    #[cfg(unix)]
    fn symlink_repo_lib(root: &FsPath) {
        let repo_lib = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../lib");
        std::os::unix::fs::symlink(repo_lib, root.join("lib")).unwrap();
    }

    fn write_main(name: &str, source: &str) -> PathBuf {
        let root = temp_root(name);
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        let entry = root.join("main.yu");
        fs::write(&entry, source).unwrap();
        entry
    }

    #[cfg(unix)]
    fn write_main_with_std(name: &str, source: &str) -> PathBuf {
        let root = temp_root(name);
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        symlink_repo_lib(&root);
        let entry = root.join("main.yu");
        fs::write(&entry, source).unwrap();
        entry
    }

    #[cfg(unix)]
    fn run_with_std_main(name: &str, source: &str) -> (RunMonoOutput, RunControlOutput) {
        let entry = write_main_with_std(name, source);
        let mono = run_mono_from_entry_with_std(&entry).unwrap();
        let control = run_control_from_entry_with_std(&entry).unwrap();
        (mono, control)
    }

    fn assert_dump_has_line_starting_with(output: &DumpPolyOutput, expected: &str) {
        assert!(
            output.text.lines().any(|line| line.starts_with(expected)),
            "missing line starting with {expected:?} in:\n{}",
            output.text
        );
    }

    fn assert_dump_contains(output: &DumpPolyOutput, expected: &str) {
        assert!(
            output.text.contains(expected),
            "missing {expected:?} in:\n{}",
            output.text
        );
    }

    fn assert_mono_dump_contains(output: &DumpMonoOutput, expected: &str) {
        assert!(
            output.text.contains(expected),
            "missing {expected:?} in:\n{}",
            output.text
        );
    }

    fn assert_check_contains(output: &CheckPolyOutput, expected: &str) {
        assert!(
            output.text.contains(expected),
            "missing {expected:?} in:\n{}",
            output.text
        );
    }

    #[test]
    fn dump_poly_reads_mod_files() {
        let root = temp_root("dump-poly-reads-mod");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(root.join("main.yu"), "mod child;\nmy x = 1\n").unwrap();
        fs::write(root.join("child.yu"), "my y = 2\n").unwrap();

        let output = dump_poly_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 2);
        assert_eq!(
            output.text,
            "roots d0:child d1:x\nd0:child mod {\n  my d2:\"child.y\": int = e1:2\n}\nmy d1:x: int = e0:1\n"
        );
    }

    #[test]
    fn dump_poly_without_std_infers_identity_function() {
        let root = temp_root("dump-poly-identity");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(root.join("main.yu"), "my id x = x\n").unwrap();

        let output = dump_poly_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_dump_has_line_starting_with(&output, "my d0:id: 'a -> 'a = ");
        assert!(!output.text.contains("std::"));
    }

    #[test]
    fn dump_mono_without_std_ignores_unused_generic_binding() {
        let root = temp_root("dump-mono-unused-generic");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(root.join("main.yu"), "my id x = x\n").unwrap();

        let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_mono_dump_contains(&output, "mono roots []");
        assert!(!output.text.contains("d0"));
    }

    #[test]
    fn dump_poly_without_std_keeps_root_expression() {
        let root = temp_root("dump-poly-root-expr");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(root.join("main.yu"), "1\n").unwrap();

        let output = dump_poly_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_eq!(output.text, "roots\nroot exprs e0:1\nruntime roots e0:1\n");
    }

    #[test]
    fn dump_mono_without_std_keeps_root_expression() {
        let root = temp_root("dump-mono-root-expr");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(root.join("main.yu"), "1\n").unwrap();

        let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_mono_dump_contains(&output, "mono roots [1]");
    }

    #[test]
    fn dump_mono_without_std_specializes_root_expression_call() {
        let root = temp_root("dump-mono-root-call");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(root.join("main.yu"), "my id x = x\nid(1)\n").unwrap();

        let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_mono_dump_contains(&output, "mono roots [(m0 1)]");
        assert_mono_dump_contains(&output, "m0 = d0 : int -> int");
    }

    #[test]
    fn dump_mono_without_std_lowers_apply_colon_indent_block_argument() {
        let root = temp_root("dump-mono-apply-colon-block-arg");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(root.join("main.yu"), "my id x = x\nid:\n  my x = 1\n  x\n").unwrap();

        let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_mono_dump_contains(&output, "mono roots [(m0 {");
        assert_mono_dump_contains(&output, " = 1;");
        assert_mono_dump_contains(&output, "m0 = d0 : int -> int");
        assert!(!output.text.contains("(m0 ())"), "{}", output.text);
    }

    #[test]
    fn dump_mono_without_std_forces_effectful_root_expression() {
        let root = temp_root("dump-mono-effectful-root");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("main.yu"),
            "act out:\n  our say: int -> unit\nout::say(1)\n",
        )
        .unwrap();

        let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_mono_dump_contains(
            &output,
            "mono roots [force-thunk[thunk[[out], unit] => unit ! [out]]((<effect-op out::say> 1))]",
        );
    }

    #[test]
    fn dump_mono_without_std_passes_argument_effect_through_pure_function() {
        let root = temp_root("dump-mono-pure-function-argument-effect");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("main.yu"),
            "act out:\n  our read: unit -> int\nmy id x = x\nid(out::read(()))\n",
        )
        .unwrap();

        let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_mono_dump_contains(
            &output,
            "mono roots [force-thunk[thunk[[out], int] => int ! [out]]",
        );
        assert_mono_dump_contains(&output, "m0 = d2 : int -> int");
    }

    #[test]
    fn dump_mono_without_std_rejects_root_case_without_concrete_join() {
        let root = temp_root("dump-mono-root-case-ambiguous");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(root.join("main.yu"), "case true: true -> 1, false -> 2.0\n").unwrap();

        let err = dump_mono_from_entry(root.join("main.yu")).unwrap_err();

        assert!(matches!(
            err,
            RouteError::Specialize(specialize::SpecializeError::ConflictingTypeCandidates { .. })
        ));
    }

    #[test]
    fn dump_mono_without_std_specializes_root_case_with_direct_cast_join() {
        let root = temp_root("dump-mono-root-case-cast-join");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("main.yu"),
            "cast(x: int): float = 0.0\ncase true: true -> 1, false -> 2.0\n",
        )
        .unwrap();

        let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_mono_dump_contains(&output, "mono roots [case true:");
        assert_mono_dump_contains(&output, "coerce[int => float](1)");
        assert!(!output.text.contains("int | float"), "{}", output.text);
    }

    #[test]
    fn dump_mono_without_std_runs_computed_top_level_binding() {
        let root = temp_root("dump-mono-computed-binding");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(root.join("main.yu"), "my id x = x\nmy a = id(1)\n").unwrap();

        let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_mono_dump_contains(&output, "mono roots [eval m0]");
        assert_mono_dump_contains(&output, "m0 = d1 : int");
        assert_mono_dump_contains(&output, "m1 = d0 : int -> int");
    }

    #[test]
    fn run_control_without_std_evaluates_computed_top_level_binding_without_result() {
        let root = temp_root("run-control-computed-binding-no-result");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(root.join("main.yu"), "my id x = x\nmy a = id(1)\n").unwrap();

        let mono = run_mono_from_entry(root.join("main.yu")).unwrap();
        let control = run_control_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(mono.file_count, 1);
        assert_eq!(mono.values, Vec::<mono_runtime::Value>::new());
        assert_eq!(mono.text, "run roots []\n");
        assert_eq!(control.file_count, 1);
        assert_eq!(control.values, Vec::<control_vm::Value>::new());
        assert_eq!(control.text, mono.text);
    }

    #[test]
    fn dump_mono_without_std_lowers_direct_effect_handler() {
        let root = temp_root("dump-mono-direct-effect-handler");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("main.yu"),
            "act out:\n  our say: int -> unit\n\
             catch out::say(1):\n\
             \x20 out::say msg, k -> k(())\n\
             \x20 value -> value\n",
        )
        .unwrap();

        let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_mono_dump_contains(
            &output,
            "catch force-thunk[thunk[[out], unit] => unit ! [out]]",
        );
        assert_mono_dump_contains(&output, "out::say d");
        assert_mono_dump_contains(&output, "<effect-op out::say>");
        assert_mono_dump_contains(
            &output,
            "force-thunk[thunk[[out], unit] => unit ! [out]]((<effect-op out::say>",
        );
        assert!(!output.text.contains("adapter["), "{}", output.text);
    }

    #[test]
    fn dump_mono_without_std_lowers_generic_direct_effect_handler() {
        let root = temp_root("dump-mono-generic-direct-effect-handler");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("main.yu"),
            "act var 't:\n  our get: unit -> 't\n\
             catch var::get():\n\
             \x20 var::get(), k -> k(1)\n\
             \x20 value -> value\n",
        )
        .unwrap();

        let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_mono_dump_contains(
            &output,
            "catch force-thunk[thunk[[var(int)], int] => int ! [var(int)]]",
        );
        assert_mono_dump_contains(&output, "var::get _");
        assert_mono_dump_contains(&output, "<effect-op var::get>");
        assert_mono_dump_contains(
            &output,
            "force-thunk[thunk[[var(int)], int] => int ! [var(int)]]((<effect-op var::get>",
        );
    }

    #[test]
    fn dump_mono_without_std_lowers_wildcard_stack_handler_annotation() {
        let root = temp_root("dump-mono-wildcard-stack-handler-annotation");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("main.yu"),
            "act signal:\n  our ping: () -> int\n\n\
             my handle(x: [_] int): int = catch x:\n\
             \x20 signal::ping(), k -> k 1\n\
             \x20 v -> v\n\n\
             handle(signal::ping())\n",
        )
        .unwrap();

        let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_mono_dump_contains(&output, "mono roots [(m0 (<effect-op signal::ping> ()))");
        assert_mono_dump_contains(&output, "m0 = d2 : thunk[");
        assert_mono_dump_contains(&output, "marker[signal]");
        assert_mono_dump_contains(&output, " -> int");
        assert!(!output.text.contains("stack("), "{}", output.text);
    }

    #[test]
    fn dump_mono_without_std_lowers_apply_colon_polymorphic_stack_handler_call() {
        let root = temp_root("dump-mono-apply-colon-stack-handler");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("main.yu"),
            "pub act sub 'a:\n\
             \x20 pub return: 'a -> never\n\
             \x20 pub sub(x: [_] 'a): 'a = catch x:\n\
             \x20 \x20 return a, _ -> a\n\
             \x20 \x20 a -> a\n\n\
             sub::sub:\n\
             \x20 sub::return 0\n",
        )
        .unwrap();

        let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_mono_dump_contains(&output, "mono roots [(m0 make-thunk");
        assert_mono_dump_contains(&output, "m0 = d2 : thunk[[sub(int)], int] -> int");
        assert_mono_dump_contains(&output, "marker[sub]");
        assert_mono_dump_contains(&output, "sub::return d");
    }

    #[test]
    fn run_mono_without_std_runs_root_expression() {
        let root = temp_root("run-mono-root-expr");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(root.join("main.yu"), "1\n").unwrap();

        let output = run_mono_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_eq!(output.values, vec![mono_runtime::Value::Int(1)]);
        assert_eq!(output.text, "run roots [1]\n");
    }

    #[test]
    fn run_mono_without_std_runs_apply_colon_block_argument() {
        let root = temp_root("run-mono-apply-colon-block-arg");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(root.join("main.yu"), "my id x = x\nid:\n  my x = 1\n  x\n").unwrap();

        let output = run_mono_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_eq!(output.values, vec![mono_runtime::Value::Int(1)]);
        assert_eq!(output.text, "run roots [1]\n");
    }

    #[test]
    fn run_control_without_std_runs_apply_colon_block_argument() {
        let root = temp_root("run-control-apply-colon-block-arg");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(root.join("main.yu"), "my id x = x\nid:\n  my x = 1\n  x\n").unwrap();

        let output = run_control_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_eq!(output.values, vec![control_vm::Value::Int(1)]);
        assert_eq!(output.text, "run roots [1]\n");
    }

    #[test]
    fn run_without_std_matches_control_on_record_case_and_handler_smoke() {
        let entry = write_main(
            "run-record-case-handler-smoke",
            "case { width: 1, height: 2 }:\n\
             \x20 { width, height } -> height\n\
             \x20 _ -> 0\n\n\
             enum opt 'a:\n\
             \x20 none\n\
             \x20 some 'a\n\
             act eff:\n\
             \x20 our send: opt int -> int\n\
             catch eff::send(opt::some 1):\n\
             \x20 eff::send(opt::some x), k -> k(x)\n\
             \x20 value -> value\n",
        );

        let mono = run_mono_from_entry(&entry).unwrap();
        let control = run_control_from_entry(&entry).unwrap();

        assert_eq!(mono.text, "run roots [2, 1]\n");
        assert_eq!(control.text, mono.text);
    }

    #[test]
    fn run_without_std_matches_control_on_struct_field_projection() {
        let entry = write_main(
            "run-struct-field-projection",
            "struct User { age: int }\nUser({ age: 1 }).age\n",
        );

        let mono = run_mono_from_entry(&entry).unwrap();
        let control = run_control_from_entry(&entry).unwrap();

        assert_eq!(mono.text, "run roots [1]\n");
        assert_eq!(control.text, mono.text);
    }

    #[cfg(unix)]
    #[test]
    fn run_with_std_matches_control_on_core_smoke_suite() {
        let (mono, control) = run_with_std_main(
            "run-std-core-smoke-suite",
            "1 + 2 * 3\n\
             [1, 2, 3].map(\\x -> x + 1).filter(\\x -> x > 2).rev\n\
             \"sum=%{1 + 2}\"\n\
             \"hex=%x{255}\"\n\
             \"debug=%?{[1, 2]}\"\n\
             \"pad=%04{7}\"\n\
             for i in 0..3:\n\
             \x20 if i == 1: std::control::flow::loop::last()\n\
             1\n",
        );

        assert_eq!(
            mono.text,
            "run roots [7, [4, 3], \"sum=3\", \"hex=ff\", \"debug=[1, 2]\", \"pad=0007\", 1]\n"
        );
        assert_eq!(control.text, mono.text);
    }

    #[cfg(unix)]
    #[test]
    fn run_with_std_runs_list_view_raw_node() {
        let root = temp_root("run-std-list-view-raw-node");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        symlink_repo_lib(&root);
        fs::write(root.join("main.yu"), "std::data::list::view_raw [1, 2]\n").unwrap();

        let mono = run_mono_from_entry_with_std(root.join("main.yu")).unwrap();
        let control = run_control_from_entry_with_std(root.join("main.yu")).unwrap();

        assert!(mono.text.contains("([1], [2])"), "{}", mono.text);
        assert!(control.text.contains("([1], [2])"), "{}", control.text);
    }

    #[cfg(unix)]
    #[test]
    fn dump_mono_with_std_specializes_list_display() {
        let root = temp_root("dump-mono-std-list-display");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        symlink_repo_lib(&root);
        fs::write(root.join("main.yu"), "[1].show\n").unwrap();

        let output = dump_mono_from_entry_with_std(root.join("main.yu")).unwrap();

        assert_mono_dump_contains(&output, "std::data::list::list(int) -> std::text::str::str");
        assert_mono_dump_contains(&output, "std::data::list::list_view(int)");
    }

    #[cfg(unix)]
    #[test]
    fn run_mono_with_std_collects_nondet_each_list() {
        let root = temp_root("run-mono-std-nondet-each-list");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        symlink_repo_lib(&root);
        fs::write(
            root.join("main.yu"),
            "std::control::nondet::each(1..3).list\n",
        )
        .unwrap();

        let output = run_mono_from_entry_with_std(root.join("main.yu")).unwrap();

        assert_eq!(output.text, "run roots [[1, 2, 3]]\n");
    }

    #[cfg(unix)]
    #[test]
    fn run_control_with_std_collects_nondet_each_list() {
        let root = temp_root("run-control-std-nondet-each-list");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        symlink_repo_lib(&root);
        fs::write(
            root.join("main.yu"),
            "std::control::nondet::each(1..3).list\n",
        )
        .unwrap();

        let output = run_control_from_entry_with_std(root.join("main.yu")).unwrap();

        assert_eq!(output.text, "run roots [[1, 2, 3]]\n");
    }

    #[cfg(unix)]
    #[test]
    fn run_with_std_collects_nondet_sum_list_benchmark() {
        let root = temp_root("run-std-nondet-sum-list-benchmark");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        symlink_repo_lib(&root);
        fs::write(
            root.join("main.yu"),
            "(std::control::nondet::each(1..3) + std::control::nondet::each(1..2)).list\n",
        )
        .unwrap();

        let mono = run_mono_from_entry_with_std(root.join("main.yu")).unwrap();
        let control = run_control_from_entry_with_std(root.join("main.yu")).unwrap();

        assert_eq!(mono.text, "run roots [[2, 3, 3, 4, 4, 5]]\n");
        assert_eq!(control.text, mono.text);
    }

    #[cfg(unix)]
    #[test]
    fn run_with_std_handles_effectful_thunk_returned_from_function() {
        let (mono, control) = run_with_std_main(
            "run-std-effectful-function-thunk-handler",
            "pub act out:\n\
             \x20 pub say: str -> ()\n\n\
             our add_and_say() =\n\
             \x20 my a = 1 + 2\n\
             \x20 out::say a.show\n\
             \x20 my b = a + 3\n\
             \x20 out::say b.show\n\
             \x20 a + b\n\n\
             our listen(x: [_] _, log: str): (_, str) = catch x:\n\
             \x20 out::say o, k -> listen(k (), log + o + \"\\n\")\n\
             \x20 v -> (v, log)\n\n\
             listen add_and_say() \"\"\n",
        );

        assert_eq!(mono.text, "run roots [(9, \"3\\n6\\n\")]\n");
        assert_eq!(control.text, mono.text);
    }

    #[cfg(unix)]
    #[test]
    fn dump_mono_with_std_specializes_nondet_sum_list_say_benchmark() {
        let root = temp_root("dump-mono-std-nondet-sum-list-say-benchmark");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        symlink_repo_lib(&root);
        fs::write(
            root.join("main.yu"),
            "(std::control::nondet::each(1..3) + std::control::nondet::each(1..2)).list.say\n",
        )
        .unwrap();

        let output = dump_mono_from_entry_with_std(root.join("main.yu")).unwrap();

        assert_mono_dump_contains(
            &output,
            "mono roots [force-thunk[thunk[[std::io::console::out], unit]",
        );
        assert_mono_dump_contains(&output, ".list <method>).say <method>");
        assert_mono_dump_contains(&output, "<effect-op std::io::console::out::write>");
        assert_mono_dump_contains(&output, "std::control::nondet::nondet");
    }

    #[cfg(unix)]
    #[test]
    fn run_with_std_nondet_sum_list_say_reports_unhandled_out() {
        let root = temp_root("run-std-nondet-sum-list-say-unhandled-out");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        symlink_repo_lib(&root);
        fs::write(
            root.join("main.yu"),
            "(std::control::nondet::each(1..3) + std::control::nondet::each(1..2)).list.say\n",
        )
        .unwrap();

        let mono = run_mono_from_entry_with_std(root.join("main.yu"));
        let control = run_control_from_entry_with_std(root.join("main.yu"));

        match mono {
            Err(RouteError::Runtime(mono_runtime::RuntimeError::UnhandledEffect { path })) => {
                assert_eq!(path, vec!["std", "io", "console", "out", "write"]);
            }
            other => panic!("expected mono unhandled out effect, got {other:?}"),
        }
        match control {
            Err(RouteError::Control(control_vm::RunError::Runtime(
                control_vm::RuntimeError::UnhandledEffect { path },
            ))) => {
                assert_eq!(path, vec!["std", "io", "console", "out", "write"]);
            }
            other => panic!("expected control unhandled out effect, got {other:?}"),
        }
    }

    #[test]
    fn run_mono_without_std_runs_polymorphic_stack_handler_call() {
        let root = temp_root("run-mono-stack-handler");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("main.yu"),
            "pub act sub 'a:\n\
             \x20 pub return: 'a -> never\n\
             \x20 pub sub(x: [_] 'a): 'a = catch x:\n\
             \x20 \x20 return a, _ -> a\n\
             \x20 \x20 a -> a\n\n\
             sub::sub:\n\
             \x20 sub::return 0\n",
        )
        .unwrap();

        let output = run_mono_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_eq!(output.values, vec![mono_runtime::Value::Int(0)]);
        assert_eq!(output.text, "run roots [0]\n");
    }

    #[test]
    fn run_mono_without_std_keeps_stack_handler_hygiene() {
        let root = temp_root("run-mono-stack-handler-hygiene");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("main.yu"),
            "pub act sub 'a:\n\
             \x20 pub return: 'a -> never\n\
             \x20 pub sub(x: [_] 'a): 'a = catch x:\n\
             \x20 \x20 return a, _ -> a\n\
             \x20 \x20 a -> a\n\n\
             our g h = sub::sub:\n\
             \x20 h 0\n\
             \x20 sub::return 1\n\n\
             sub::sub:\n\
             \x20 g \\i -> sub::return i\n\
             \x20 sub::return 2\n",
        )
        .unwrap();

        let output = run_mono_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_eq!(output.values, vec![mono_runtime::Value::Int(0)]);
        assert_eq!(output.text, "run roots [0]\n");
    }

    #[test]
    fn run_control_without_std_keeps_stack_handler_hygiene() {
        let root = temp_root("run-control-stack-handler-hygiene");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("main.yu"),
            "pub act sub 'a:\n\
             \x20 pub return: 'a -> never\n\
             \x20 pub sub(x: [_] 'a): 'a = catch x:\n\
             \x20 \x20 return a, _ -> a\n\
             \x20 \x20 a -> a\n\n\
             our g h = sub::sub:\n\
             \x20 h 0\n\
             \x20 sub::return 1\n\n\
             sub::sub:\n\
             \x20 g \\i -> sub::return i\n\
             \x20 sub::return 2\n",
        )
        .unwrap();

        let output = run_control_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_eq!(output.values, vec![control_vm::Value::Int(0)]);
        assert_eq!(output.text, "run roots [0]\n");
    }

    #[test]
    fn dump_mono_without_std_lowers_constructor_payload_effect_handler() {
        let root = temp_root("dump-mono-constructor-payload-effect-handler");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("main.yu"),
            "enum opt 'a:\n  none\n  some 'a\n\
             act eff:\n  our send: opt int -> int\n\
             catch eff::send(opt::some 1):\n\
             \x20 eff::send(opt::some x), k -> k(x)\n\
             \x20 value -> value\n",
        )
        .unwrap();

        let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_mono_dump_contains(&output, "<effect-op eff::send>");
        assert_mono_dump_contains(&output, "eff::send d2 d");
        assert_mono_dump_contains(&output, "force-thunk[thunk[[eff], int] => int ! [eff]]");
    }

    #[test]
    fn dump_mono_without_std_computed_effect_binding_escapes_later_handler() {
        let root = temp_root("dump-mono-computed-effect-escapes-handler");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("main.yu"),
            "act out:\n  our say: int -> unit\n\
             my run = out::say(1)\n\
             my handled = catch run:\n\
             \x20 out::say msg, k -> k(())\n\
             \x20 value -> value\n",
        )
        .unwrap();

        let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_mono_dump_contains(&output, "mono roots [eval m0, eval m1]");
        assert_mono_dump_contains(
            &output,
            "m0 = d2 : unit\n  force-thunk[thunk[[out], unit] => unit ! [out]]((<effect-op out::say> 1))",
        );
        assert_mono_dump_contains(&output, "m1 = d3 : unit\n  catch m0: out::say d");
        assert!(
            !output.text.contains("catch force-thunk"),
            "{}",
            output.text
        );
    }

    #[test]
    fn dump_mono_without_std_binds_constructor_case_payload_type() {
        let root = temp_root("dump-mono-constructor-case-payload");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("main.yu"),
            "enum opt 'a:\n  none\n  some 'a\n\
             my id x = x\n\
             case opt::some 1:\n\
             \x20 opt::some x -> id(x)\n\
             \x20 _ -> 0\n",
        )
        .unwrap();

        let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_mono_dump_contains(
            &output,
            "mono roots [case (<ctor d2 / 1> 1): d2 d6 -> (m0 d6), _ -> 0]",
        );
        assert_mono_dump_contains(&output, "m0 = d3 : int -> int");
    }

    #[test]
    fn dump_mono_without_std_binds_record_case_field_type() {
        let root = temp_root("dump-mono-record-case-field");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("main.yu"),
            "my id x = x\n\
             case { width: 1 }:\n\
             \x20 { width } -> id(width)\n\
             \x20 _ -> 0\n",
        )
        .unwrap();

        let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_mono_dump_contains(
            &output,
            "mono roots [case {width: 1}: {width: d3} -> (m0 d3), _ -> 0]",
        );
        assert_mono_dump_contains(&output, "m0 = d0 : int -> int");
    }

    #[test]
    fn dump_mono_without_std_specializes_record_field_select() {
        let root = temp_root("dump-mono-record-select");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("main.yu"),
            "my id x = x\nid(({ width: 1 }).width)\n",
        )
        .unwrap();

        let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_mono_dump_contains(&output, "mono roots [(m0 {width: 1}.width)]");
        assert_mono_dump_contains(&output, "m0 = d0 : int -> int");
    }

    #[test]
    fn dump_mono_without_std_specializes_record_select_from_case_local() {
        let root = temp_root("dump-mono-record-select-case-local");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("main.yu"),
            "my id x = x\n\
             case { width: 1 }:\n\
             \x20 row -> id(row.width)\n",
        )
        .unwrap();

        let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_mono_dump_contains(&output, "mono roots [case {width: 1}: d3 -> (m0 d3.width)]");
        assert_mono_dump_contains(&output, "m0 = d0 : int -> int");
    }

    #[test]
    fn run_control_without_std_applies_record_pattern_default() {
        let entry = write_main(
            "run-control-record-pattern-default",
            "my f({x = 1}) = x\nf {}\nf {x: 2}\n",
        );

        let output = run_control_from_entry(entry).unwrap();

        assert_eq!(output.file_count, 1);
        assert_eq!(output.text, "run roots [1, 2]\n");
    }

    #[test]
    fn run_control_without_std_record_pattern_default_reads_earlier_field() {
        let entry = write_main(
            "run-control-record-pattern-default-previous-field",
            "my f({x = 1, y = x}) = y\nf {x: 3}\nf {}\n",
        );

        let output = run_control_from_entry(entry).unwrap();

        assert_eq!(output.file_count, 1);
        assert_eq!(output.text, "run roots [3, 1]\n");
    }

    #[test]
    fn run_control_without_std_record_pattern_default_handles_effect() {
        let entry = write_main(
            "run-control-record-pattern-default-effect",
            "act signal:\n\
             \x20 our ping: () -> int\n\n\
             my f({x = signal::ping()}): int = x\n\n\
             catch (f {}):\n\
             \x20 signal::ping(), _ -> 7\n\
             \x20 value -> value\n",
        );

        let mono = run_mono_from_entry(&entry).unwrap();
        let control = run_control_from_entry(entry).unwrap();

        assert_eq!(mono.file_count, 1);
        assert_eq!(mono.values, vec![mono_runtime::Value::Int(7)]);
        assert_eq!(mono.text, "run roots [7]\n");
        assert_eq!(control.file_count, 1);
        assert_eq!(control.text, mono.text);
    }

    #[test]
    fn dump_mono_without_std_specializes_method_select_result() {
        let root = temp_root("dump-mono-method-select-result");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("main.yu"),
            "type User with:\n\
             \x20 our x.id = x\n\
             my u: User = 1\n\
             my keep x = x\n\
             keep(u.id)\n",
        )
        .unwrap();

        let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_mono_dump_contains(&output, ".id <method>");
        assert_mono_dump_contains(&output, "m0 = d3 : User -> User");
        assert_mono_dump_contains(&output, "m2 = d1 : User -> User");
    }

    #[test]
    fn dump_mono_without_std_specializes_method_select_remaining_function() {
        let root = temp_root("dump-mono-method-select-function");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("main.yu"),
            "type User with:\n\
             \x20 our x.pick y = y\n\
             my u: User = 1\n\
             my keep x = x\n\
             keep(u.pick(1))\n",
        )
        .unwrap();

        let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_mono_dump_contains(&output, ".pick <method>");
        assert_mono_dump_contains(&output, "m0 = d3 : int -> int");
        assert_mono_dump_contains(&output, "m2 = d1 : User -> int -> int");
    }

    #[test]
    fn dump_poly_without_std_infers_local_constructor_application() {
        let root = temp_root("dump-poly-local-constructor");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("main.yu"),
            "enum opt 'a:\n    none\n    some 'a\n\nmy wrap x = opt::some x\n",
        )
        .unwrap();

        let output = dump_poly_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_dump_has_line_starting_with(&output, "  d2:\"opt.some\": 'a -> opt 'a = ");
        assert_dump_has_line_starting_with(&output, "my d3:wrap: 'a -> opt 'a = ");
        assert!(!output.text.contains("std::"));
    }

    #[test]
    fn dump_poly_without_std_lowers_value_catch() {
        let root = temp_root("dump-poly-value-catch");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(root.join("main.yu"), "my handle x = catch x:\n    v -> v\n").unwrap();

        let output = dump_poly_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_dump_has_line_starting_with(&output, "my d0:handle: 'a -> 'a = ");
        assert_dump_contains(&output, "catch ");
        assert!(!output.text.contains("std::"));
    }

    #[test]
    fn dump_poly_without_std_lowers_local_effect_handler() {
        let root = temp_root("dump-poly-local-effect-handler");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("main.yu"),
            "act signal:\n    pub ping: () -> int\n\nmy handle x = catch x:\n    signal::ping(), k -> k 1\n    v -> v\n",
        )
        .unwrap();

        let output = dump_poly_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_dump_has_line_starting_with(&output, "my d2:handle: 'a -> 'a = ");
        assert_dump_contains(&output, "catch ");
        assert_dump_contains(&output, "\"signal.ping\"");
        assert!(!output.text.contains("std::"));
    }

    #[test]
    fn dump_poly_without_std_lowers_file_handle_builtin_type() {
        let root = temp_root("dump-poly-file-handle");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("main.yu"),
            "act file:\n    my get: file_handle -> file_handle\n",
        )
        .unwrap();

        let output = dump_poly_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_dump_contains(&output, "file_handle -> [file] file_handle");
        assert_eq!(output.errors, Vec::<String>::new());
    }

    #[test]
    fn dump_poly_without_std_keeps_annotated_shallow_handler_type_clean() {
        let root = temp_root("dump-poly-clean-shallow-handler");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("main.yu"),
            "act signal:\n    pub ping: () -> int\n\nmy handle(x: [signal] _) = catch x:\n    signal::ping(), k -> k 1\n    v -> v\n",
        )
        .unwrap();

        let output = dump_poly_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_eq!(output.errors, Vec::<String>::new());
        assert_dump_has_line_starting_with(
            &output,
            "my d2:handle: 'a ['b & [signal; 'b]] -> ['b] 'a = ",
        );
        assert!(!output.text.contains("stack("));
        assert!(!output.text.contains("std::"));
    }

    #[test]
    fn dump_poly_without_std_handles_local_effect_call() {
        let root = temp_root("dump-poly-handle-effect-call");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("main.yu"),
            "act signal:\n    pub ping: () -> int\n\nmy handled() = catch signal::ping():\n    signal::ping(), k -> k 1\n",
        )
        .unwrap();

        let output = dump_poly_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_eq!(output.errors, Vec::<String>::new());
        assert_dump_has_line_starting_with(&output, "my d2:handled: () -> [signal] int = ");
        assert_dump_contains(&output, "catch ");
        assert_dump_contains(&output, "\"signal::ping\"");
        assert_dump_contains(&output, "\"signal.ping\"");
        assert_dump_contains(&output, ":k ->");
        assert!(!output.text.contains("std::"));
    }

    #[test]
    fn dump_poly_without_std_reports_type_annotation_mismatch() {
        let root = temp_root("dump-poly-type-error");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(root.join("main.yu"), "my x: bool = 1\n").unwrap();

        let output = dump_poly_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_eq!(
            output.errors,
            vec!["type mismatch: int is not bool".to_string()]
        );
        assert!(!output.text.contains("std::"));
    }

    #[test]
    fn dump_poly_raw_without_std_includes_type_and_expr_graphs() {
        let root = temp_root("dump-poly-raw");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(root.join("main.yu"), "my id x = x\n").unwrap();

        let output = dump_poly_raw_from_entry(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 1);
        assert_eq!(output.errors, Vec::<String>::new());
        assert_dump_contains(&output, "raw roots [d0:id]");
        assert_dump_contains(&output, "scheme {");
        assert_dump_contains(&output, "types:");
        assert_dump_contains(&output, "exprs {");
        assert_dump_contains(&output, "pats {");
        assert_dump_contains(&output, "Lambda(");
        assert!(!output.text.contains("std::"));
    }

    #[test]
    fn collect_local_sources_with_std_reads_nearby_lib_std() {
        let root = temp_root("nearby-std");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(root.join("lib").join("std")).unwrap();
        fs::write(root.join("main.yu"), "my x = 1\n").unwrap();
        fs::write(root.join("lib").join("std.yu"), "mod prelude;\nmod var;\n").unwrap();
        fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();
        fs::write(root.join("lib").join("std").join("var.yu"), "my y = 2\n").unwrap();

        let files = collect_local_sources_with_std(root.join("main.yu")).unwrap();

        assert!(
            files
                .iter()
                .any(|file| file.module_path.segments == vec![Name("std".into())])
        );
        assert!(
            files.iter().any(|file| file.module_path.segments
                == vec![Name("std".into()), Name("prelude".into())])
        );
        assert!(
            files
                .iter()
                .any(|file| file.module_path.segments
                    == vec![Name("std".into()), Name("var".into())])
        );
        let root_source = files
            .iter()
            .find(|file| file.module_path.segments.is_empty())
            .unwrap();
        assert!(root_source.source.starts_with(IMPLICIT_STD_MODULE_DECL));
        assert!(root_source.source.contains(IMPLICIT_PRELUDE_IMPORT));
    }

    #[test]
    fn collect_source_text_with_embedded_std_uses_embedded_package() {
        let files =
            collect_source_text_with_embedded_std("playground.yu", "my x = 1\n".to_string())
                .unwrap();

        assert_eq!(files.len(), embedded_std_files().len() + 1);
        assert!(
            files
                .iter()
                .any(|file| file.module_path.segments == vec![Name("std".into())])
        );
        assert!(files.iter().any(|file| file.module_path.segments
            == vec![
                Name("std".into()),
                Name("control".into()),
                Name("nondet".into())
            ]));
        let root_source = files
            .iter()
            .find(|file| file.module_path.segments.is_empty())
            .unwrap();
        assert!(root_source.source.starts_with(IMPLICIT_STD_MODULE_DECL));
        assert!(root_source.source.contains(IMPLICIT_PRELUDE_IMPORT));
    }

    #[test]
    fn collect_source_text_with_embedded_playground_std_uses_compact_package() {
        let files = collect_source_text_with_embedded_playground_std(
            "playground.yu",
            "my x = 1\n".to_string(),
        )
        .unwrap();

        assert!(files.len() < embedded_std_files().len() + 1);
        assert!(
            files
                .iter()
                .any(|file| file.module_path.segments == vec![Name("std".into())])
        );
        assert!(files.iter().any(|file| file.module_path.segments
            == vec![
                Name("std".into()),
                Name("control".into()),
                Name("nondet".into())
            ]));
        assert!(!files.iter().any(|file| file.module_path.segments
            == vec![Name("std".into()), Name("io".into()), Name("file".into())]));
        let root_source = files
            .iter()
            .find(|file| file.module_path.segments.is_empty())
            .unwrap();
        assert!(root_source.source.starts_with(IMPLICIT_STD_MODULE_DECL));
        assert!(root_source.source.contains(IMPLICIT_PRELUDE_IMPORT));
    }

    #[test]
    fn run_control_source_text_with_embedded_playground_std_runs_arithmetic() {
        let build =
            build_control_from_source_text_with_embedded_playground_std("playground.yu", "1 + 2\n")
                .unwrap();
        assert!(build.errors.is_empty(), "{:?}", build.errors);
        let output =
            run_built_control_program(&build.program, build.file_count, build.errors).unwrap();

        assert_eq!(output.text, "run roots [3]\n");
    }

    #[test]
    fn run_control_source_text_with_embedded_playground_std_runs_struct_method_example() {
        let source = "\
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

point { x: 3, y: 4 } .norm2
";
        let build =
            build_control_from_source_text_with_embedded_playground_std("playground.yu", source)
                .unwrap();
        assert!(build.errors.is_empty(), "{:?}", build.errors);
        let output =
            run_built_control_program(&build.program, build.file_count, build.errors).unwrap();

        assert_eq!(output.text, "run roots [25]\n");
    }

    #[test]
    fn run_control_source_text_with_embedded_playground_std_runs_local_change_example() {
        let source = "\
{
    my $total = 0
    for x in 1..5:
        &total = $total + x
    $total
}
";
        let build =
            build_control_from_source_text_with_embedded_playground_std("playground.yu", source)
                .unwrap();
        assert!(build.errors.is_empty(), "{:?}", build.errors);
        let output =
            run_built_control_program(&build.program, build.file_count, build.errors).unwrap();

        assert_eq!(output.text, "run roots [15]\n");
    }

    #[test]
    fn run_control_source_text_with_embedded_playground_std_runs_list_update_example() {
        let source = "\
{
    my $xs = [
        2
        3
        4
    ]
    &xs[1] = 6
    $xs
}
";
        let build =
            build_control_from_source_text_with_embedded_playground_std("playground.yu", source)
                .unwrap();
        assert!(build.errors.is_empty(), "{:?}", build.errors);
        let output =
            run_built_control_program(&build.program, build.file_count, build.errors).unwrap();

        assert_eq!(output.text, "run roots [[2, 6, 4]]\n");
    }

    #[test]
    fn run_control_source_text_with_embedded_playground_std_runs_sub_return_example() {
        let source = "\
my first_over limit = sub:
    for x in 0..: if x * x > limit: return x
    0

first_over 40
";
        let build =
            build_control_from_source_text_with_embedded_playground_std("playground.yu", source)
                .unwrap();
        assert!(build.errors.is_empty(), "{:?}", build.errors);
        let output =
            run_built_control_program(&build.program, build.file_count, build.errors).unwrap();

        assert_eq!(output.text, "run roots [7]\n");
    }

    #[test]
    fn run_control_source_text_with_embedded_std_runs_root_expression() {
        let output =
            run_control_from_source_text_with_embedded_std("playground.yu", "1 + 2\n").unwrap();

        assert_eq!(output.file_count, embedded_std_files().len() + 1);
        assert_eq!(output.text, "run roots [3]\n");
    }

    #[test]
    fn run_control_source_text_with_embedded_std_imports_prelude_reexports() {
        let output =
            run_control_from_source_text_with_embedded_std("playground.yu", "each(1..3).list\n")
                .unwrap();

        assert_eq!(output.file_count, embedded_std_files().len() + 1);
        assert_eq!(output.text, "run roots [[1, 2, 3]]\n");
    }

    #[test]
    fn run_control_source_text_with_embedded_std_runs_junction_tour_example() {
        let output = run_control_from_source_text_with_embedded_std(
            "playground.yu",
            "if all [1, 2, 3] < any [2, 3, 4]:\n  1\nelse:\n  0\n",
        )
        .unwrap();

        assert_eq!(output.file_count, embedded_std_files().len() + 1);
        assert_eq!(output.text, "run roots [1]\n");
    }

    #[test]
    fn run_control_source_text_with_embedded_std_keeps_std_instances_unmarked_between_roots() {
        let output = run_control_from_source_text_with_embedded_std(
            "playground.yu",
            "{\n  my a = each 1..3\n  a\n}.list\nif all [1, 2, 3] < any [3, 4, 5]:\n  1\nelse:\n  0\n",
        )
        .unwrap();

        assert_eq!(output.file_count, embedded_std_files().len() + 1);
        assert_eq!(output.text, "run roots [[1, 2, 3], 1]\n");
    }

    #[test]
    fn run_control_source_text_with_embedded_std_forces_effectful_block_let() {
        let output = run_control_from_source_text_with_embedded_std(
            "playground.yu",
            "{\n  my a = each 1..3\n  (a, 1)\n}.list\n",
        )
        .unwrap();

        assert_eq!(output.file_count, embedded_std_files().len() + 1);
        assert_eq!(output.text, "run roots [[(1, 1), (2, 1), (3, 1)]]\n");
    }

    #[test]
    fn run_control_source_text_with_embedded_std_runs_nondet_triples() {
        let output = std::thread::Builder::new()
            .stack_size(16 * 1024 * 1024)
            .spawn(|| {
                let output = run_control_from_source_text_with_embedded_std(
                    "playground.yu",
                    "{\n  my a = each 1..15\n  my b = each a..15\n  my c = each b..15\n  guard: a * a + b * b == c * c\n  (a, b, c)\n}.list\n",
                )
                .unwrap();
                (output.file_count, output.text)
            })
            .unwrap()
            .join()
            .unwrap();

        assert_eq!(output.0, embedded_std_files().len() + 1);
        assert_eq!(
            output.1,
            "run roots [[(3, 4, 5), (5, 12, 13), (6, 8, 10), (9, 12, 15)]]\n"
        );
    }

    #[test]
    fn run_control_source_text_with_embedded_std_runs_poly_variant_list() {
        let output =
            run_control_from_source_text_with_embedded_std("playground.yu", "[:a, :b]\n").unwrap();

        assert_eq!(output.file_count, embedded_std_files().len() + 1);
        assert_eq!(output.text, "run roots [[a, b]]\n");
    }

    #[test]
    fn run_control_source_text_with_embedded_std_reuses_record_default_function() {
        let output = run_control_from_source_text_with_embedded_std(
            "playground.yu",
            "my f({x = 1}) = x\n[f {}, f {x: 2}]\n",
        )
        .unwrap();

        assert_eq!(output.file_count, embedded_std_files().len() + 1);
        assert_eq!(output.text, "run roots [[1, 2]]\n");
    }

    #[test]
    fn run_control_source_text_with_embedded_std_lowers_sub_syntax_return() {
        let output =
            run_control_from_source_text_with_embedded_std("playground.yu", "sub:\n  return 1\n")
                .unwrap();

        assert_eq!(output.file_count, embedded_std_files().len() + 1);
        assert_eq!(output.text, "run roots [1]\n");
    }

    #[test]
    fn run_control_source_text_with_embedded_std_lowers_labeled_sub_syntax_return() {
        let output = run_control_from_source_text_with_embedded_std(
            "playground.yu",
            "my x = sub 'outer:\n  'outer.return 1\nx\n",
        )
        .unwrap();

        assert_eq!(output.file_count, embedded_std_files().len() + 1);
        assert_eq!(output.text, "run roots [1]\n");
    }

    #[test]
    fn run_control_source_text_with_embedded_std_lowers_root_labeled_sub_syntax_return() {
        let output = run_control_from_source_text_with_embedded_std(
            "playground.yu",
            "sub 'outer:\n  'outer.return 1\n",
        )
        .unwrap();

        assert_eq!(output.file_count, embedded_std_files().len() + 1);
        assert_eq!(output.text, "run roots [1]\n");
    }

    #[test]
    fn run_control_source_text_with_embedded_std_lowers_sub_lambda_return() {
        let output = run_control_from_source_text_with_embedded_std(
            "playground.yu",
            "my f = \\sub x -> return x\nf 7\n",
        )
        .unwrap();

        assert_eq!(output.file_count, embedded_std_files().len() + 1);
        assert_eq!(output.text, "run roots [7]\n");
    }

    #[test]
    fn run_control_source_text_with_embedded_std_lowers_labeled_sub_lambda_return() {
        let output = run_control_from_source_text_with_embedded_std(
            "playground.yu",
            "my f = \\sub 'out x -> 'out.return x\nf 7\n",
        )
        .unwrap();

        assert_eq!(output.file_count, embedded_std_files().len() + 1);
        assert_eq!(output.text, "run roots [7]\n");
    }

    #[test]
    fn run_control_source_text_with_embedded_std_labeled_sub_lambda_handles_inner_return() {
        let output = run_control_from_source_text_with_embedded_std(
            "playground.yu",
            "sub 'outer:\n  my f = \\sub 'inner x -> 'inner.return x\n  f 7\n",
        )
        .unwrap();

        assert_eq!(output.file_count, embedded_std_files().len() + 1);
        assert_eq!(output.text, "run roots [7]\n");
    }

    #[test]
    fn run_control_source_text_with_embedded_std_labeled_sub_lambda_lets_outer_return_escape() {
        let output = run_control_from_source_text_with_embedded_std(
            "playground.yu",
            "sub 'outer:\n  my f = \\sub 'inner x -> 'outer.return x\n  f 7\n  'outer.return 1\n",
        )
        .unwrap();

        assert_eq!(output.file_count, embedded_std_files().len() + 1);
        assert_eq!(output.text, "run roots [7]\n");
    }

    #[test]
    fn run_control_source_text_with_embedded_std_keeps_sub_syntax_hygiene() {
        let output = run_control_from_source_text_with_embedded_std(
            "playground.yu",
            "our g h = sub:\n  h 0\n  return 1\n\nsub:\n  g \\i -> return i\n  return 2\n",
        )
        .unwrap();

        assert_eq!(output.file_count, embedded_std_files().len() + 1);
        assert_eq!(output.text, "run roots [0]\n");
    }

    #[test]
    fn check_poly_source_text_with_embedded_std_reports_type_error() {
        let output =
            check_poly_from_source_text_with_embedded_std("playground.yu", "my x: int = true\n")
                .unwrap();

        assert_eq!(output.file_count, embedded_std_files().len() + 1);
        assert_check_contains(&output, "check-poly-embedded-std\n");
        assert_check_contains(&output, "lowering errors:\n");
        assert_check_contains(&output, "x: type mismatch: bool is not int\n");
    }

    #[test]
    fn dump_poly_with_std_uses_nearby_prelude() {
        let root = temp_root("dump-poly-with-std");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(root.join("lib").join("std")).unwrap();
        fs::write(root.join("main.yu"), "my x = 1\n").unwrap();
        fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
        fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

        let output = dump_poly_from_entry_with_std(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 3);
        assert!(output.text.contains("my d"));
        assert!(output.text.contains(": int = "));
    }

    #[test]
    fn check_poly_std_reports_summary_and_type_errors_without_dumping_defs() {
        let root = temp_root("check-poly-std");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(root.join("lib").join("std")).unwrap();
        fs::write(root.join("main.yu"), "my x = 1\n").unwrap();
        fs::write(root.join("lib").join("std.yu"), "mod prelude;\nmod foo;\n").unwrap();
        fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();
        fs::write(
            root.join("lib").join("std").join("foo.yu"),
            "my good x = x\nmy bad: bool = 1\n",
        )
        .unwrap();

        let output = check_poly_from_entry_with_std(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 4);
        assert_check_contains(&output, "check-poly-std\n");
        assert_check_contains(&output, "files: 4\n");
        assert_check_contains(&output, "timing:\n");
        assert_check_contains(&output, "summary:\n");
        assert_check_contains(&output, "  lowering errors: 1\n");
        assert_check_contains(
            &output,
            "std::foo: values 2 typed 1 missing_schemes 1 bodyless 1",
        );
        assert_check_contains(&output, "missing schemes:\n");
        assert_check_contains(&output, "std.foo.bad\n");
        assert_check_contains(&output, "lowering errors:\n");
        assert_check_contains(&output, "std.foo.bad: type mismatch: int is not bool\n");
        assert!(!output.text.contains(" = Let {"));
    }

    #[cfg(unix)]
    #[test]
    fn analyze_entry_source_uses_in_memory_root_source() {
        let root = temp_root("analyze-entry-source");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(root.join("lib").join("std")).unwrap();
        fs::write(root.join("main.yu"), "my x: int = 1\n").unwrap();
        fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
        fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

        let output = analyze_entry_source_with_std_options(
            root.join("main.yu"),
            "my x: int = true\n",
            &StdSourceOptions {
                std_root: Some(root.join("lib")),
            },
        )
        .unwrap();

        assert_eq!(output.file_count, 3);
        assert_eq!(
            output.diagnostics,
            vec![SourceDiagnostic {
                label: Some("x".to_string()),
                message: "type mismatch: bool is not int".to_string(),
            }]
        );
    }

    #[test]
    fn check_poly_std_in_filters_to_requested_module() {
        let root = temp_root("check-poly-std-in");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(root.join("lib").join("std")).unwrap();
        fs::write(root.join("main.yu"), "my x = 1\n").unwrap();
        fs::write(
            root.join("lib").join("std.yu"),
            "mod prelude;\nmod foo;\nmod bar;\n",
        )
        .unwrap();
        fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();
        fs::write(
            root.join("lib").join("std").join("foo.yu"),
            "my good x = x\nmy bad: bool = 1\n",
        )
        .unwrap();
        fs::write(
            root.join("lib").join("std").join("bar.yu"),
            "my bad2: bool = 1\n",
        )
        .unwrap();

        let output =
            check_poly_from_entry_with_std_in_module(root.join("main.yu"), "std::foo").unwrap();

        assert_eq!(output.file_count, 5);
        assert_check_contains(&output, "check-poly-std-in std::foo\n");
        assert_check_contains(&output, "  values: 2\n");
        assert_check_contains(&output, "  missing schemes: 1\n");
        assert_check_contains(&output, "  bodyless declarations: 1\n");
        assert_check_contains(&output, "  lowering errors: 1 local / 2 total\n");
        assert_check_contains(&output, "std.foo.bad: type mismatch: int is not bool\n");
        assert!(!output.text.contains("std.bar.bad2"));
    }

    #[test]
    fn dump_poly_std_in_filters_to_requested_module_and_local_errors() {
        let root = temp_root("dump-poly-std-in");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(root.join("lib").join("std")).unwrap();
        fs::write(root.join("main.yu"), "my x = 1\n").unwrap();
        fs::write(
            root.join("lib").join("std.yu"),
            "mod prelude;\nmod foo;\nmod bar;\n",
        )
        .unwrap();
        fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();
        fs::write(
            root.join("lib").join("std").join("foo.yu"),
            "my good x = x\nmy bad: bool = 1\n",
        )
        .unwrap();
        fs::write(
            root.join("lib").join("std").join("bar.yu"),
            "my bad2: bool = 1\n",
        )
        .unwrap();

        let output =
            dump_poly_from_entry_with_std_in_module(root.join("main.yu"), "std::foo").unwrap();

        assert_eq!(output.file_count, 5);
        assert_dump_contains(&output, "module std::foo\n");
        assert_dump_contains(&output, "values: 2\n");
        assert_dump_contains(&output, "lowering errors: 1 local / 2 total\n");
        assert_dump_contains(&output, "\"std.foo.good\"");
        assert_dump_contains(&output, "\"std.foo.bad\"");
        assert!(!output.text.contains("\"std.bar.bad2\""));
        assert_eq!(
            output.errors,
            vec!["type mismatch: int is not bool".to_string()]
        );
    }

    #[test]
    fn dump_poly_std_in_raw_filters_to_requested_module() {
        let root = temp_root("dump-poly-std-in-raw");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(root.join("lib").join("std")).unwrap();
        fs::write(root.join("main.yu"), "my x = 1\n").unwrap();
        fs::write(root.join("lib").join("std.yu"), "mod prelude;\nmod foo;\n").unwrap();
        fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();
        fs::write(root.join("lib").join("std").join("foo.yu"), "my id x = x\n").unwrap();

        let output =
            dump_poly_raw_from_entry_with_std_in_module(root.join("main.yu"), "std.foo").unwrap();

        assert_eq!(output.file_count, 4);
        assert_eq!(output.errors, Vec::<String>::new());
        assert_dump_contains(&output, "module std::foo\n");
        assert_dump_contains(&output, "raw roots [");
        assert_dump_contains(&output, "\"std.foo.id\"");
        assert_dump_contains(&output, "scheme {");
        assert_dump_contains(&output, "exprs {");
        assert!(!output.text.contains("main"));
    }

    #[test]
    fn use_mod_loads_module_file_but_plain_use_does_not() {
        let root = temp_root("use-mod-loads");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(root.join("main.yu"), "use mod math::*\nmy x = 1\n").unwrap();
        fs::write(root.join("plain.yu"), "use math::*\nmy x = 1\n").unwrap();
        fs::write(root.join("math.yu"), "my y = 2\n").unwrap();

        let use_mod = collect_local_sources(root.join("main.yu")).unwrap();
        let plain_use = collect_local_sources(root.join("plain.yu")).unwrap();

        assert_eq!(use_mod.len(), 2);
        assert_eq!(plain_use.len(), 1);
    }

    #[test]
    fn reports_ambiguous_module_file() {
        let root = temp_root("ambiguous-module");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(root.join("main")).unwrap();
        fs::write(root.join("main.yu"), "mod child;\n").unwrap();
        fs::write(root.join("child.yu"), "my y = 1\n").unwrap();
        fs::write(root.join("main").join("child.yu"), "my y = 2\n").unwrap();

        let err = collect_local_sources(root.join("main.yu")).unwrap_err();

        assert!(matches!(err, RouteError::AmbiguousModuleFile { .. }));
    }
}
