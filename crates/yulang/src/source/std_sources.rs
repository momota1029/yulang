use std::cell::RefCell;

use super::*;

thread_local! {
    static EMBEDDED_STD_LOADED_PREFIX: RefCell<Option<Vec<sources::LoadedFile>>> =
        const { RefCell::new(None) };
    static EMBEDDED_STD_LOWERING_PREFIX: RefCell<Option<infer::lowering::BodyLoweringPrefix>> =
        const { RefCell::new(None) };
    static EMBEDDED_PLAYGROUND_STD_LOADED_PREFIX: RefCell<Option<Vec<sources::LoadedFile>>> =
        const { RefCell::new(None) };
    static EMBEDDED_PLAYGROUND_STD_LOWERING_PREFIX: RefCell<Option<infer::lowering::BodyLoweringPrefix>> =
        const { RefCell::new(None) };
}

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

    if let Some(root) = installed_versioned_std_root().filter(|root| is_std_root(root)) {
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
    let entry_band = entry_band_path(&sources::local_realm_root(entry), entry);
    let mut files = embedded_std_sources();
    let source = source_with_implicit_std_prelude(source);
    let metadata = discover_source_header_metadata(&Path::default(), &source);
    files.push(CollectedSource::with_band_path_and_resolution_imports(
        entry.to_path_buf(),
        Path::default(),
        entry_band,
        source,
        metadata.resolution_imports,
    ));
    files
}

pub(super) fn embedded_std_loaded_with_root(
    _entry: &FsPath,
    source: String,
) -> Vec<sources::LoadedFile> {
    let prefix = cached_embedded_std_loaded_prefix();
    load_with_embedded_prefix(prefix, source)
}

pub(super) fn embedded_playground_std_sources_with_root(
    entry: &FsPath,
    source: String,
) -> Vec<CollectedSource> {
    let entry_band = entry_band_path(&sources::local_realm_root(entry), entry);
    let mut files = crate::playground_std::embedded_playground_std_sources();
    let source = source_with_implicit_std_prelude(source);
    let metadata = discover_source_header_metadata(&Path::default(), &source);
    files.push(CollectedSource::with_band_path_and_resolution_imports(
        entry.to_path_buf(),
        Path::default(),
        entry_band,
        source,
        metadata.resolution_imports,
    ));
    files
}

pub(super) fn embedded_playground_std_loaded_with_root(
    _entry: &FsPath,
    source: String,
) -> Vec<sources::LoadedFile> {
    let prefix = cached_embedded_playground_std_loaded_prefix();
    load_with_embedded_prefix(prefix, source)
}

pub(super) fn source_with_implicit_std_prelude(source: String) -> String {
    format!("{IMPLICIT_PRELUDE_IMPORT}{IMPLICIT_STD_MODULE_DECL}{source}")
}

pub(super) fn source_with_implicit_prelude_only(source: String) -> String {
    format!("{IMPLICIT_PRELUDE_IMPORT}{source}")
}

pub(super) fn embedded_playground_std_lowering_with_root(
    source: String,
) -> Result<(infer::lowering::BodyLowering, usize), RouteError> {
    let prefix = cached_embedded_playground_std_lowering_prefix()?;
    lower_root_with_embedded_prefix(
        &prefix,
        cached_embedded_playground_std_loaded_prefix(),
        source,
    )
}

pub(super) fn embedded_playground_std_lowering_with_root_artifact(
    artifact: crate::cache::CachedCompiledUnitArtifact,
    source: String,
) -> Result<(infer::lowering::BodyLowering, usize), RouteError> {
    let prefix = lowering_prefix_from_compiled_unit_artifact(artifact)?;
    lower_root_with_embedded_prefix(
        &prefix,
        cached_embedded_playground_std_loaded_prefix(),
        source,
    )
}

pub(super) fn embedded_std_lowering_with_root(
    source: String,
) -> Result<(infer::lowering::BodyLowering, usize), RouteError> {
    let prefix = cached_embedded_std_lowering_prefix()?;
    lower_root_with_embedded_prefix(&prefix, cached_embedded_std_loaded_prefix(), source)
}

pub(super) fn embedded_std_lowering_with_root_artifact(
    artifact: crate::cache::CachedCompiledUnitArtifact,
    source: String,
) -> Result<(infer::lowering::BodyLowering, usize), RouteError> {
    let prefix = lowering_prefix_from_compiled_unit_artifact(artifact)?;
    lower_root_with_embedded_prefix(&prefix, cached_embedded_std_loaded_prefix(), source)
}

fn lower_root_with_embedded_prefix(
    prefix: &infer::lowering::BodyLoweringPrefix,
    loaded_prefix: Vec<sources::LoadedFile>,
    source: String,
) -> Result<(infer::lowering::BodyLowering, usize), RouteError> {
    let loaded = load_with_embedded_prefix_prelude_only(loaded_prefix, source);
    let file_count = loaded.len();
    let root = loaded
        .iter()
        .find(|file| file.module_path.segments.is_empty())
        .ok_or(RouteError::Lower(infer::LoadedFilesError::MissingRoot))?;
    let lowering = infer::lowering::lower_root_loaded_file_with_prefix(prefix, root)
        .map_err(RouteError::Lower)?;
    Ok((lowering, file_count))
}

pub(super) fn embedded_std_sources() -> Vec<CollectedSource> {
    embedded_std_files()
        .iter()
        .map(|file| {
            let module_path = embedded_std_module_path(file.relative_path);
            let source = file.source.to_string();
            let metadata = discover_source_header_metadata(&module_path, &source);
            CollectedSource::with_band_path_and_resolution_imports(
                PathBuf::from("<embedded-std>").join(file.relative_path),
                module_path,
                Path::default(),
                source,
                metadata.resolution_imports,
            )
        })
        .collect()
}

fn cached_embedded_std_loaded_prefix() -> Vec<sources::LoadedFile> {
    EMBEDDED_STD_LOADED_PREFIX.with(|cache| cached_loaded_prefix(cache, || embedded_std_sources()))
}

fn cached_embedded_std_lowering_prefix() -> Result<infer::lowering::BodyLoweringPrefix, RouteError>
{
    EMBEDDED_STD_LOWERING_PREFIX.with(|cache| {
        if let Some(prefix) = cache.borrow().as_ref() {
            return Ok(prefix.clone());
        }

        let files =
            embedded_std_sources_with_root(FsPath::new("<embedded-std-root>"), String::new());
        let loaded = load_collected_source_files(files.clone());
        let artifact = cached_embedded_compiled_unit_artifact(&files, &loaded)?;
        let prefix = lowering_prefix_from_compiled_unit_artifact(artifact)?;
        *cache.borrow_mut() = Some(prefix.clone());
        Ok(prefix)
    })
}

fn cached_embedded_playground_std_loaded_prefix() -> Vec<sources::LoadedFile> {
    EMBEDDED_PLAYGROUND_STD_LOADED_PREFIX.with(|cache| {
        cached_loaded_prefix(
            cache,
            crate::playground_std::embedded_playground_std_sources,
        )
    })
}

fn cached_embedded_playground_std_lowering_prefix()
-> Result<infer::lowering::BodyLoweringPrefix, RouteError> {
    EMBEDDED_PLAYGROUND_STD_LOWERING_PREFIX.with(|cache| {
        if let Some(prefix) = cache.borrow().as_ref() {
            return Ok(prefix.clone());
        }

        let files = embedded_playground_std_sources_with_root(
            FsPath::new("<embedded-playground-std-root>"),
            String::new(),
        );
        let loaded = load_collected_source_files(files.clone());
        let artifact = cached_embedded_compiled_unit_artifact(&files, &loaded)?;
        let prefix = lowering_prefix_from_compiled_unit_artifact(artifact)?;
        *cache.borrow_mut() = Some(prefix.clone());
        Ok(prefix)
    })
}

fn lowering_prefix_from_compiled_unit_artifact(
    artifact: crate::cache::CachedCompiledUnitArtifact,
) -> Result<infer::lowering::BodyLoweringPrefix, RouteError> {
    infer::lowering::BodyLoweringPrefix::from_compiled_unit_surfaces(
        &artifact.namespace,
        &artifact.lowering,
        &artifact.runtime,
    )
    .ok_or(infer::LoadedFilesError::MissingRoot)
    .map_err(RouteError::Lower)
}

pub(super) fn cached_embedded_compiled_unit_artifact(
    files: &[CollectedSource],
    loaded: &[sources::LoadedFile],
) -> Result<crate::cache::CachedCompiledUnitArtifact, RouteError> {
    let key = crate::cache::source_cache_key(files);
    if let Some(artifact) = read_embedded_compiled_unit_artifact(key) {
        return Ok(artifact);
    }

    let artifact =
        crate::cache::compiled_unit_artifact_from_loaded_files_with_key(files, loaded, key)
            .map_err(RouteError::Lower)?;
    write_embedded_compiled_unit_artifact(key, &artifact);
    Ok(artifact)
}

#[cfg(not(target_arch = "wasm32"))]
fn read_embedded_compiled_unit_artifact(
    key: crate::cache::SourceCacheKey,
) -> Option<crate::cache::CachedCompiledUnitArtifact> {
    let cache = crate::cache::ArtifactCache::new(crate::stdlib::default_user_cache_root());
    match cache.read_compiled_unit_artifact(key) {
        Ok(Some(artifact)) if artifact.errors.is_empty() => Some(artifact),
        _ => None,
    }
}

#[cfg(target_arch = "wasm32")]
fn read_embedded_compiled_unit_artifact(
    _key: crate::cache::SourceCacheKey,
) -> Option<crate::cache::CachedCompiledUnitArtifact> {
    None
}

#[cfg(not(target_arch = "wasm32"))]
fn write_embedded_compiled_unit_artifact(
    key: crate::cache::SourceCacheKey,
    artifact: &crate::cache::CachedCompiledUnitArtifact,
) {
    if !artifact.errors.is_empty() {
        return;
    }
    let cache = crate::cache::ArtifactCache::new(crate::stdlib::default_user_cache_root());
    let _ = cache.write_compiled_unit_artifact(key, artifact);
}

#[cfg(target_arch = "wasm32")]
fn write_embedded_compiled_unit_artifact(
    _key: crate::cache::SourceCacheKey,
    _artifact: &crate::cache::CachedCompiledUnitArtifact,
) {
}

fn cached_loaded_prefix(
    cache: &RefCell<Option<Vec<sources::LoadedFile>>>,
    sources: impl FnOnce() -> Vec<CollectedSource>,
) -> Vec<sources::LoadedFile> {
    let mut cached = cache.borrow_mut();
    cached
        .get_or_insert_with(|| load_collected_source_files(sources()))
        .clone()
}

pub(super) fn load_collected_source_files(files: Vec<CollectedSource>) -> Vec<sources::LoadedFile> {
    let (source_files, band_paths) = collected_source_files_and_band_paths(files);
    sources::load_with_band_paths(source_files, band_paths)
}

fn load_with_embedded_prefix(
    prefix: Vec<sources::LoadedFile>,
    source: String,
) -> Vec<sources::LoadedFile> {
    sources::load_with_loaded_prefix(
        &prefix,
        vec![SourceFile {
            module_path: Path::default(),
            source: source_with_implicit_std_prelude(source),
        }],
    )
}

fn load_with_embedded_prefix_prelude_only(
    prefix: Vec<sources::LoadedFile>,
    source: String,
) -> Vec<sources::LoadedFile> {
    sources::load_with_loaded_prefix(
        &prefix,
        vec![SourceFile {
            module_path: Path::default(),
            source: source_with_implicit_prelude_only(source),
        }],
    )
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

pub(super) fn std_module_path_for_file(std_root: &FsPath, file: &FsPath) -> Option<Path> {
    let std_root = canonicalize_for_dedupe(std_root);
    let file = canonicalize_for_dedupe(file);
    let relative = file.strip_prefix(std_root).ok()?;
    let mut relative_without_extension = relative.to_path_buf();
    if relative_without_extension.extension()? != "yu" {
        return None;
    }
    relative_without_extension.set_extension("");
    let segments = relative_without_extension
        .components()
        .map(|component| match component {
            std::path::Component::Normal(segment) => {
                segment.to_str().map(|segment| Name(segment.to_string()))
            }
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    if segments.first().map(|name| name.0.as_str()) != Some("std") {
        return None;
    }
    Some(Path { segments })
}

pub(super) fn is_std_root(path: &FsPath) -> bool {
    crate::stdlib::is_std_root(path)
}

#[derive(Debug, Clone, Default)]
pub(super) struct SourceHeaderMetadata {
    pub module_loads: Vec<ModuleLoadRequest>,
    pub resolution_imports: Vec<sources::UseImport>,
    pub current_realm_bands: Vec<Path>,
}

pub(super) fn discover_source_header_metadata(
    module_path: &Path,
    source: &str,
) -> SourceHeaderMetadata {
    if !source.contains("mod") && !source.contains("use") {
        return SourceHeaderMetadata::default();
    }
    let cst = parser::parse_module_to_green(source);
    let root = rowan::SyntaxNode::<parser::sink::YulangLanguage>::new_root(cst);
    let module_loads = sources::module_load_requests(module_path, &root);
    let mut metadata = SourceHeaderMetadata {
        module_loads,
        resolution_imports: Vec::new(),
        current_realm_bands: Vec::new(),
    };
    collect_source_resolution_imports(&root, &mut metadata);
    metadata
}

pub(super) fn discover_module_loads(module_path: &Path, source: &str) -> Vec<ModuleLoadRequest> {
    discover_source_header_metadata(module_path, source).module_loads
}

fn collect_source_resolution_imports(
    node: &rowan::SyntaxNode<parser::sink::YulangLanguage>,
    metadata: &mut SourceHeaderMetadata,
) {
    if node.kind() == parser::lex::SyntaxKind::UseDecl {
        collect_source_resolution_imports_from_use(node, metadata);
    }
    for child in node.children() {
        collect_source_resolution_imports(&child, metadata);
    }
}

fn collect_source_resolution_imports_from_use(
    node: &rowan::SyntaxNode<parser::sink::YulangLanguage>,
    metadata: &mut SourceHeaderMetadata,
) {
    for import in sources::use_imports(node) {
        let (path, route, has_version, has_anchor) = match &import {
            sources::UseImport::Alias {
                path,
                route,
                version,
                anchor,
                ..
            }
            | sources::UseImport::Glob {
                prefix: path,
                route,
                version,
                anchor,
            } => (path, *route, version.is_some(), anchor.is_some()),
        };
        if let sources::UsePathRoute::CurrentRealm { band_segments } = route {
            let band = Path {
                segments: path.segments.iter().take(band_segments).cloned().collect(),
            };
            if !band.segments.is_empty() && !metadata.current_realm_bands.contains(&band) {
                metadata.current_realm_bands.push(band);
            }
        }
        if route != sources::UsePathRoute::Relative || has_version || has_anchor {
            metadata.resolution_imports.push(import);
        }
    }
}

pub(super) fn resolve_realm_band_file(root: &FsPath, band: &Path) -> Result<PathBuf, RouteError> {
    let candidate = realm_band_file_candidate(root, band);
    if candidate.is_file() {
        return Ok(candidate);
    }
    Err(RouteError::RealmBandNotFound {
        root: root.to_path_buf(),
        band: band.clone(),
        candidates: vec![candidate],
    })
}

pub(super) fn realm_band_file_candidate(root: &FsPath, band: &Path) -> PathBuf {
    let mut relative = relative_path(&band.segments);
    relative.set_extension("yu");
    root.join(relative)
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
