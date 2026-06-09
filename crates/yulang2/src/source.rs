//! 実ファイルから新 `sources` / `infer` route へ渡す source set を作る入口。
//!
//! `sources` crate は in-memory source set の parse/load 層に留め、FS traversal と
//! 実験中の std 取り込みはここへ置く。

use std::collections::{HashMap, HashSet, VecDeque};
use std::env;
use std::fmt;
use std::fs;
use std::io;
use std::path::{Path as FsPath, PathBuf};

use sources::{ModuleLoadRequest, Name, Path, SourceFile};

pub const IMPLICIT_PRELUDE_IMPORT: &str = "use std::prelude::*\n";
const YULANG_STD_ENV: &str = "YULANG_STD";

/// entry file から local module file を読み、1つの module tree として poly dump を返す。
pub fn dump_poly_from_entry(entry: impl AsRef<FsPath>) -> Result<DumpPolyOutput, RouteError> {
    dump_poly_from_sources(collect_local_sources(entry)?)
}

/// entry file と近場の `lib/std` を読み、implicit prelude 付きで poly dump を返す。
///
/// デバッグ用の暫定入口。install 済み std ではなく、entry の親から上へ辿って見つかる
/// `lib/std` を優先する。
pub fn dump_poly_from_entry_with_std(
    entry: impl AsRef<FsPath>,
) -> Result<DumpPolyOutput, RouteError> {
    dump_poly_from_sources(collect_local_sources_with_std(entry)?)
}

/// `mod foo;` / `use mod foo::*` だけを辿って raw source file を集める。
pub fn collect_local_sources(
    entry: impl AsRef<FsPath>,
) -> Result<Vec<CollectedSource>, RouteError> {
    Collector::new().collect_entry(entry.as_ref(), false)
}

/// 近場の `lib/std` と local module file を集め、root source に implicit prelude を足す。
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

/// `base` から上へ辿って、デバッグ用の近場 std root を探す。
pub fn find_nearby_std_root(base: &FsPath) -> Option<PathBuf> {
    for ancestor in base.ancestors() {
        let candidate = ancestor.join("lib").join("std");
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
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CollectedSource {
    pub path: PathBuf,
    pub module_path: Path,
    pub source: String,
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
    Lower(infer::LoadedFilesError),
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
            RouteError::Lower(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for RouteError {}

struct Collector {
    seen_files: HashSet<PathBuf>,
    module_files: HashMap<Path, PathBuf>,
    files: Vec<CollectedSource>,
    std_modules: Vec<Name>,
}

impl Collector {
    fn new() -> Self {
        Self {
            seen_files: HashSet::new(),
            module_files: HashMap::new(),
            files: Vec::new(),
            std_modules: Vec::new(),
        }
    }

    fn collect_std_root(&mut self, std_root: &FsPath) -> Result<(), RouteError> {
        let mut files = fs::read_dir(std_root)
            .map_err(|error| RouteError::Io {
                path: std_root.to_path_buf(),
                error,
            })?
            .map(|entry| {
                entry
                    .map(|entry| entry.path())
                    .map_err(|error| RouteError::Io {
                        path: std_root.to_path_buf(),
                        error,
                    })
            })
            .collect::<Result<Vec<_>, _>>()?;
        files.retain(|path| path.extension().is_some_and(|ext| ext == "yu"));
        files.sort();

        for path in files {
            let Some(stem) = path.file_stem().and_then(|stem| stem.to_str()) else {
                continue;
            };
            let module_path = Path {
                segments: vec![Name("std".to_string()), Name(stem.to_string())],
            };
            self.std_modules.push(Name(stem.to_string()));
            self.collect_fixed_module_file(path, module_path)?;
        }

        Ok(())
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
                source = format!(
                    "{}{IMPLICIT_PRELUDE_IMPORT}{source}",
                    self.synthetic_std_module_source()
                );
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

    fn collect_fixed_module_file(
        &mut self,
        path: PathBuf,
        module_path: Path,
    ) -> Result<(), RouteError> {
        let canonical = canonicalize_for_dedupe(&path);
        self.record_module_file(&module_path, &canonical)?;
        if !self.seen_files.insert(canonical) {
            return Ok(());
        }

        let source = fs::read_to_string(&path).map_err(|error| RouteError::Io {
            path: path.clone(),
            error,
        })?;
        self.files.push(CollectedSource {
            path,
            module_path,
            source,
        });
        Ok(())
    }

    fn synthetic_std_module_source(&self) -> String {
        if self.std_modules.is_empty() {
            return String::new();
        }

        let mut source = String::from("mod std:\n");
        for module in &self.std_modules {
            source.push_str("  mod ");
            source.push_str(&module.0);
            source.push_str(";\n");
        }
        source
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

fn dump_poly_from_sources(files: Vec<CollectedSource>) -> Result<DumpPolyOutput, RouteError> {
    let source_files = files
        .iter()
        .map(|file| SourceFile {
            module_path: file.module_path.clone(),
            source: file.source.clone(),
        })
        .collect::<Vec<_>>();
    let loaded = sources::load(source_files);
    let dump = infer::dump::dump_loaded_files(&loaded).map_err(RouteError::Lower)?;
    Ok(DumpPolyOutput {
        text: dump.text,
        file_count: loaded.len(),
    })
}

fn resolve_nearby_std_root(base: &FsPath) -> Option<PathBuf> {
    find_nearby_std_root(base).or_else(|| env_std_root().filter(|root| is_std_root(root)))
}

fn env_std_root() -> Option<PathBuf> {
    let value = env::var_os(YULANG_STD_ENV)?;
    if value.is_empty() {
        return None;
    }
    Some(PathBuf::from(value))
}

fn is_std_root(path: &FsPath) -> bool {
    path.join("prelude.yu").is_file()
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
    fn collect_local_sources_with_std_reads_nearby_lib_std() {
        let root = temp_root("nearby-std");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(root.join("lib").join("std")).unwrap();
        fs::write(root.join("main.yu"), "my x = 1\n").unwrap();
        fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();
        fs::write(root.join("lib").join("std").join("var.yu"), "my y = 2\n").unwrap();

        let files = collect_local_sources_with_std(root.join("main.yu")).unwrap();

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
        assert!(root_source.source.starts_with("mod std:\n"));
        assert!(root_source.source.contains(IMPLICIT_PRELUDE_IMPORT));
    }

    #[test]
    fn dump_poly_with_std_uses_nearby_prelude() {
        let root = temp_root("dump-poly-with-std");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(root.join("lib").join("std")).unwrap();
        fs::write(root.join("main.yu"), "my x = 1\n").unwrap();
        fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

        let output = dump_poly_from_entry_with_std(root.join("main.yu")).unwrap();

        assert_eq!(output.file_count, 2);
        assert!(output.text.contains("my d"));
        assert!(output.text.contains(": int = "));
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
