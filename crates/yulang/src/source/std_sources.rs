use super::*;

pub(super) fn resolve_std_root(
    base: &FsPath,
    options: &StdSourceOptions,
) -> Result<PathBuf, RouteError> {
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

pub(super) fn resolve_nearby_std_root(base: &FsPath) -> Option<PathBuf> {
    env_std_root()
        .filter(|root| is_std_root(root))
        .or_else(|| find_nearby_std_root(base))
}

pub(super) fn parse_dump_module_path(module: &str) -> Result<Path, RouteError> {
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

pub(super) fn resolve_auto_std_root(base: &FsPath) -> Result<PathBuf, RouteError> {
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

pub(super) fn embedded_std_sources_with_root(
    entry: &FsPath,
    source: String,
) -> Vec<CollectedSource> {
    let mut files = embedded_std_sources();
    files.push(CollectedSource {
        path: entry.to_path_buf(),
        module_path: Path::default(),
        source: source_with_implicit_std_prelude(source),
    });
    files
}

pub(super) fn embedded_playground_std_sources_with_root(
    entry: &FsPath,
    source: String,
) -> Vec<CollectedSource> {
    let mut files = crate::playground_std::embedded_playground_std_sources();
    files.push(CollectedSource {
        path: entry.to_path_buf(),
        module_path: Path::default(),
        source: source_with_implicit_std_prelude(source),
    });
    files
}

pub(super) fn source_with_implicit_std_prelude(source: String) -> String {
    format!("{IMPLICIT_PRELUDE_IMPORT}{IMPLICIT_STD_MODULE_DECL}{source}")
}

pub(super) fn embedded_std_sources() -> Vec<CollectedSource> {
    embedded_std_files()
        .iter()
        .map(|file| CollectedSource {
            path: PathBuf::from("<embedded-std>").join(file.relative_path),
            module_path: embedded_std_module_path(file.relative_path),
            source: file.source.to_string(),
        })
        .collect()
}

pub(super) fn embedded_std_module_path(relative_path: &str) -> Path {
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

pub(super) fn is_std_root(path: &FsPath) -> bool {
    crate::stdlib::is_std_root(path)
}

pub(super) fn discover_module_loads(module_path: &Path, source: &str) -> Vec<ModuleLoadRequest> {
    let cst = parser::parse_module_to_green(source);
    let root = rowan::SyntaxNode::<parser::sink::YulangLanguage>::new_root(cst);
    sources::module_load_requests(module_path, &root)
}

pub(super) fn resolve_module_file(
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

pub(super) fn relative_module_segments<'a>(current: &Path, requested: &'a Path) -> &'a [Name] {
    requested
        .segments
        .strip_prefix(current.segments.as_slice())
        .unwrap_or(requested.segments.as_slice())
}

pub(super) fn module_file_candidates(current: &FsPath, relative: &[Name]) -> Vec<PathBuf> {
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

pub(super) fn relative_path(segments: &[Name]) -> PathBuf {
    let mut path = PathBuf::new();
    for segment in segments {
        path.push(&segment.0);
    }
    path
}

pub(super) fn format_module_path(path: &Path) -> String {
    if path.segments.is_empty() {
        return "<root>".to_string();
    }
    path.segments
        .iter()
        .map(|name| name.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

pub(super) fn write_candidates(f: &mut fmt::Formatter<'_>, candidates: &[PathBuf]) -> fmt::Result {
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

pub(super) fn canonicalize_for_dedupe(path: &FsPath) -> PathBuf {
    path.canonicalize().unwrap_or_else(|_| path.to_path_buf())
}
