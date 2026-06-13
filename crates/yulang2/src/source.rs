//! 実ファイルから新 `sources` / `infer` route へ渡す source set を作る入口。
//!
//! `sources` crate は in-memory source set の parse/load 層に留め、FS traversal と
//! 実験中の std 取り込みはここへ置く。

use std::collections::{HashMap, HashSet, VecDeque};
use std::env;
use std::fmt;
use std::fmt::Write as _;
use std::fs;
use std::io;
use std::path::{Path as FsPath, PathBuf};
use std::time::{Duration, Instant};

use sources::{ModuleLoadRequest, Name, Path, SourceFile};

pub const IMPLICIT_PRELUDE_IMPORT: &str = "use std::prelude::*\n";
const IMPLICIT_STD_MODULE_DECL: &str = "mod std;\n";
const YULANG_STD_ENV: &str = "YULANG_STD";

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

/// entry file と近場の `lib/std.yu` を読み、implicit prelude 付きで poly dump を返す。
///
/// デバッグ用の暫定入口。install 済み std ではなく、entry の親から上へ辿って見つかる
/// `lib/std.yu` を優先する。
pub fn dump_poly_from_entry_with_std(
    entry: impl AsRef<FsPath>,
) -> Result<DumpPolyOutput, RouteError> {
    dump_poly_from_sources(
        collect_local_sources_with_std(entry)?,
        DumpPolyKind::Compact,
    )
}

/// entry file と近場の `lib/std.yu` を読み、implicit prelude 付きで raw poly debug dump を返す。
pub fn dump_poly_raw_from_entry_with_std(
    entry: impl AsRef<FsPath>,
) -> Result<DumpPolyOutput, RouteError> {
    dump_poly_from_sources(collect_local_sources_with_std(entry)?, DumpPolyKind::Raw)
}

/// entry file と近場の `lib/std.yu` を読み、implicit prelude 付きで mono dump を返す。
pub fn dump_mono_from_entry_with_std(
    entry: impl AsRef<FsPath>,
) -> Result<DumpMonoOutput, RouteError> {
    dump_mono_from_sources(collect_local_sources_with_std(entry)?)
}

/// entry file と近場の `lib/std.yu` を読み、dump なしで型付け状況を集計する。
pub fn check_poly_from_entry_with_std(
    entry: impl AsRef<FsPath>,
) -> Result<CheckPolyOutput, RouteError> {
    let total_start = Instant::now();
    let collect_start = Instant::now();
    let files = collect_local_sources_with_std(entry)?;
    let collect = collect_start.elapsed();
    check_poly_from_sources(files, collect, total_start, None)
}

/// entry file と近場の `lib/std.yu` を読み、指定 module の型付け状況だけを集計する。
pub fn check_poly_from_entry_with_std_in_module(
    entry: impl AsRef<FsPath>,
    module: &str,
) -> Result<CheckPolyOutput, RouteError> {
    let total_start = Instant::now();
    let collect_start = Instant::now();
    let files = collect_local_sources_with_std(entry)?;
    let collect = collect_start.elapsed();
    check_poly_from_sources(
        files,
        collect,
        total_start,
        Some(parse_dump_module_path(module)?),
    )
}

/// entry file と近場の `lib/std.yu` を読み、指定 module 直下の値だけを poly dump する。
pub fn dump_poly_from_entry_with_std_in_module(
    entry: impl AsRef<FsPath>,
    module: &str,
) -> Result<DumpPolyOutput, RouteError> {
    dump_poly_from_sources(
        collect_local_sources_with_std(entry)?,
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
    dump_poly_from_sources(
        collect_local_sources_with_std(entry)?,
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

/// 近場の `lib/std.yu` と local module file を集め、root source に implicit prelude を足す。
pub fn collect_local_sources_with_std(
    entry: impl AsRef<FsPath>,
) -> Result<Vec<CollectedSource>, RouteError> {
    let entry = entry.as_ref();
    let base = entry.parent().unwrap_or_else(|| FsPath::new("."));
    let std_root = resolve_nearby_std_root(base).ok_or_else(|| RouteError::StdRootNotFound {
        base: base.to_path_buf(),
    })?;

    let mut collector = Collector::new();
    collector.collect_std_root(&std_root)?;
    collector.collect_entry(entry, true)
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckPolyOutput {
    pub text: String,
    pub file_count: usize,
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

#[derive(Debug)]
pub enum RouteError {
    Io {
        path: PathBuf,
        error: io::Error,
    },
    StdRootNotFound {
        base: PathBuf,
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
        let mut queue = VecDeque::from([(entry.to_path_buf(), Path::default())]);
        while let Some((path, module_path)) = queue.pop_front() {
            let canonical = canonicalize_for_dedupe(&path);
            self.record_module_file(&module_path, &canonical)?;
            if !self.seen_files.insert(canonical) {
                continue;
            }

            let mut source = fs::read_to_string(&path).map_err(|error| RouteError::Io {
                path: path.clone(),
                error,
            })?;
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
                queue.push_back((child_path, requested_module));
            }
        }
        Ok(self.files)
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
    module: Option<Path>,
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
    let text = if let Some(module_path) = module {
        let Some(module_check) = check
            .report
            .modules
            .iter()
            .find(|item| item.path == module_path)
        else {
            return Err(RouteError::CheckModuleNotFound {
                module: module_path,
            });
        };
        format_check_poly_module_output(loaded.len(), &check, module_check, &timing)
    } else {
        format_check_poly_output(loaded.len(), &check, &timing)
    };
    Ok(CheckPolyOutput {
        text,
        file_count: loaded.len(),
    })
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
    let program =
        specialize::specialize(&dump.lowering.session.poly).map_err(RouteError::Specialize)?;
    Ok(DumpMonoOutput {
        text: specialize::mono::dump::dump_program(&program),
        file_count: loaded.len(),
        errors,
    })
}

fn format_check_poly_output(
    file_count: usize,
    check: &infer::check::PolyCheckOutput,
    timing: &CheckPolyTimings,
) -> String {
    let report = &check.report;
    let totals = &report.totals;
    let mut out = String::new();
    let _ = writeln!(out, "check-poly-std");
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
) -> String {
    let mut out = String::new();
    let _ = writeln!(
        out,
        "check-poly-std-in {}",
        infer::check::format_path(&module.path)
    );
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

fn env_std_root() -> Option<PathBuf> {
    let value = env::var_os(YULANG_STD_ENV)?;
    if value.is_empty() {
        return None;
    }
    Some(PathBuf::from(value))
}

fn is_std_root(path: &FsPath) -> bool {
    path.join("std.yu").is_file()
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
            "yulang2-{name}-{}",
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ))
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
        assert_mono_dump_contains(&output, "mono roots [m0]");
        assert_mono_dump_contains(&output, "m0 = d1 : int");
        assert_mono_dump_contains(&output, "m1 = d0 : int -> int");
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
        assert_mono_dump_contains(&output, "mono roots [m0, m1]");
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
            "mono roots [case (d2 1): d2 d6 -> (m0 d6), _ -> 0]",
        );
        assert_mono_dump_contains(&output, "m0 = d3 : int -> int");
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
