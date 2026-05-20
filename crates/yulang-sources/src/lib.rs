use std::cmp::Ordering;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;
use std::fs;
use std::io;
use std::path::{Path as FsPath, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use rowan::{NodeOrToken, SyntaxNode};
use serde::{Deserialize, Serialize};
use yulang_parser::lex::SyntaxKind;
use yulang_parser::op::{BpVec, OpDef, OpTable, standard_op_table};
use yulang_parser::parse_module_to_green;
use yulang_parser::sink::YulangLanguage;
use yulang_typed_ir::{Name, Path as ModulePath};

mod cache;
mod lock;
mod realm_path;
mod stdlib;

pub use cache::{
    YULANG_LOCK_FILE, YULANG_MANIFEST_FILE, YULANG_PROJECT_DIR, YULANG_TARGET_DIR,
    YulangCachePaths, default_user_cache_root, project_target_root,
};
pub use lock::{
    LockedRealm, LockedRealmDependency, LockedRealmSource, LockedWithConstraint,
    SourceWithConstraint, WithConstraintConflict, YULANG_LOCK_FORMAT_VERSION, YulangLockFile,
    collect_source_with_constraints,
};
pub use realm_path::{
    CanonicalRealmPath, CanonicalRealmPathParseError, parse_canonical_realm_path,
};
pub use stdlib::{
    YULANG_LIB_DIR_ENV, YULANG_STD_ENV, YULANG_STDLIB_VERSION, default_user_lib_root,
    default_versioned_std_root, find_std_root_near, install_embedded_std, is_std_root,
    resolve_or_install_std_root,
};

pub fn parse_source_meta(source: &str) -> SourceMeta {
    let root = SyntaxNode::<YulangLanguage>::new_root(parse_module_to_green(source));
    let mut meta = SourceMeta::default();
    collect_leading_meta_items(&root, &mut meta);
    meta
}

pub fn collect_source_files(entry: impl AsRef<FsPath>) -> Result<SourceSet, SourceLoadError> {
    collect_source_files_with_options(entry, SourceOptions::default())
}

pub fn collect_virtual_source_files_with_options(
    source: &str,
    base_dir: Option<PathBuf>,
    options: SourceOptions,
) -> Result<SourceSet, SourceLoadError> {
    let mut loader = SourceLoader::new(options, None);
    loader.register_realm(
        virtual_single_file_realm_id(),
        SourceRealmRoot::Virtual,
        Vec::new(),
    );
    loader.load_virtual_entry(source, base_dir.as_deref())?;
    sort_files_topologically(&mut loader.files);
    build_syntax_tables(&mut loader.files);
    Ok(SourceSet::from_files_with_realms(
        loader.files,
        loader.realms,
    ))
}

pub fn collect_inline_source_files_with_options(
    source: &str,
    inline_sources: impl IntoIterator<Item = InlineSource>,
    options: SourceOptions,
) -> SourceSet {
    let mut loader = InlineSourceLoader::new(inline_sources, options);
    loader.load_entry(source);
    sort_files_topologically(&mut loader.files);
    build_syntax_tables(&mut loader.files);
    SourceSet::from_files_with_realm(
        loader.files,
        inline_realm_id(),
        SourceRealmRoot::Embedded("inline".to_string()),
    )
}

pub fn collect_source_files_with_options(
    entry: impl AsRef<FsPath>,
    options: SourceOptions,
) -> Result<SourceSet, SourceLoadError> {
    let entry = entry.as_ref();
    let realm_root = local_realm_root(entry);
    let manifest = load_realm_manifest(&realm_root)?;
    let lock = load_realm_lock(&realm_root)?;
    let realm_id = manifest
        .as_ref()
        .map(|manifest| manifest.id.clone())
        .unwrap_or_else(|| local_realm_id(entry));
    let dependencies = manifest
        .as_ref()
        .map(|manifest| manifest.dependencies.clone())
        .unwrap_or_default();
    let mut loader = SourceLoader::new(options, lock);
    loader.register_realm(
        realm_id.clone(),
        SourceRealmRoot::Local(realm_root),
        dependencies,
    );
    loader.load_entry(entry, realm_id)?;
    sort_files_topologically(&mut loader.files);
    build_syntax_tables(&mut loader.files);
    Ok(SourceSet::from_files_with_realms(
        loader.files,
        loader.realms,
    ))
}

pub const COMPILED_UNIT_ARTIFACT_FORMAT_VERSION: u32 = 10;
pub const COMPILED_UNIT_PARSER_FORMAT_VERSION: u32 = 1;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SourceOptions {
    pub std_root: Option<PathBuf>,
    pub implicit_prelude: bool,
    pub search_paths: Vec<PathBuf>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct RealmIdentity(pub String);

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct RealmVersion(pub String);

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ResolvedRealmId {
    pub identity: RealmIdentity,
    pub version: Option<RealmVersion>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum SourceRealmRoot {
    Local(PathBuf),
    Cached(PathBuf),
    Embedded(String),
    Virtual,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceRealmDependency {
    pub identity: RealmIdentity,
    pub requirement: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceRealmManifest {
    pub id: ResolvedRealmId,
    pub dependencies: Vec<SourceRealmDependency>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrozenRealmSnapshot {
    pub format_version: u32,
    pub identity: RealmIdentity,
    pub version: RealmVersion,
    pub source_hash: u64,
    pub files: Vec<FrozenRealmSnapshotFile>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrozenRealmSnapshotFile {
    pub path: String,
    pub source_len: usize,
    pub source_hash: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FreezeRealmOutput {
    pub root: PathBuf,
    pub snapshot_path: PathBuf,
    pub snapshot: FrozenRealmSnapshot,
    pub already_exists: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SourceRealmSeed {
    id: ResolvedRealmId,
    root: SourceRealmRoot,
    dependencies: Vec<SourceRealmDependency>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceRealm {
    pub id: ResolvedRealmId,
    pub root: SourceRealmRoot,
    pub dependencies: Vec<SourceRealmDependency>,
    pub bands: Vec<SourceBand>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct BandPath {
    pub segments: Vec<Name>,
}

impl BandPath {
    pub fn root() -> Self {
        Self::default()
    }

    pub fn from_segments(segments: Vec<Name>) -> Self {
        Self { segments }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ResolvedBandId {
    pub realm: ResolvedRealmId,
    pub band: BandPath,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceBand {
    pub path: BandPath,
    pub files: Vec<usize>,
    pub entry: bool,
}

impl SourceRealm {
    pub fn band(&self, path: &BandPath) -> Option<&SourceBand> {
        self.bands.iter().find(|band| &band.path == path)
    }
}

fn virtual_single_file_realm_id() -> ResolvedRealmId {
    ResolvedRealmId {
        identity: RealmIdentity("virtual:entry".to_string()),
        version: None,
    }
}

fn inline_realm_id() -> ResolvedRealmId {
    ResolvedRealmId {
        identity: RealmIdentity("embedded:inline".to_string()),
        version: None,
    }
}

fn local_realm_id(entry: &FsPath) -> ResolvedRealmId {
    ResolvedRealmId {
        identity: RealmIdentity(format!("file://{}", local_realm_root(entry).display())),
        version: None,
    }
}

fn local_realm_root(entry: &FsPath) -> PathBuf {
    let path = canonicalize_for_dedupe(entry);
    path.parent()
        .map(FsPath::to_path_buf)
        .unwrap_or_else(|| PathBuf::from("."))
}

#[derive(Debug, Serialize, Deserialize)]
struct RealmManifestToml {
    realm: Option<RealmManifestRealmToml>,
    dependencies: Option<BTreeMap<String, String>>,
}

#[derive(Debug, Serialize, Deserialize)]
struct RealmManifestRealmToml {
    identity: Option<String>,
    name: Option<String>,
    version: Option<String>,
}

fn load_realm_manifest(root: &FsPath) -> Result<Option<SourceRealmManifest>, SourceLoadError> {
    let path = root.join(cache::YULANG_MANIFEST_FILE);
    if !path.is_file() {
        return Ok(None);
    }
    let source = fs::read_to_string(&path).map_err(|error| SourceLoadError::Io {
        path: path.clone(),
        error,
    })?;
    let decoded = toml::from_str::<RealmManifestToml>(&source).map_err(|error| {
        SourceLoadError::InvalidRealmManifest {
            path: path.clone(),
            message: error.to_string(),
        }
    })?;
    let realm = decoded
        .realm
        .ok_or_else(|| invalid_realm_manifest(&path, "missing [realm] table"))?;
    let identity = realm
        .identity
        .or(realm.name)
        .filter(|identity| !identity.trim().is_empty())
        .ok_or_else(|| invalid_realm_manifest(&path, "missing realm.identity"))?;
    let version = realm
        .version
        .filter(|version| !version.trim().is_empty())
        .map(RealmVersion);
    let mut dependencies = decoded
        .dependencies
        .unwrap_or_default()
        .into_iter()
        .filter_map(|(identity, requirement)| {
            (!identity.trim().is_empty()).then_some(SourceRealmDependency {
                identity: RealmIdentity(identity),
                requirement,
            })
        })
        .collect::<Vec<_>>();
    dependencies.sort_by(|left, right| left.identity.0.cmp(&right.identity.0));

    Ok(Some(SourceRealmManifest {
        id: ResolvedRealmId {
            identity: RealmIdentity(identity),
            version,
        },
        dependencies,
    }))
}

pub fn freeze_realm_version(
    root: impl AsRef<FsPath>,
    version: impl Into<String>,
) -> Result<FreezeRealmOutput, FreezeRealmError> {
    freeze_realm_version_inner(root.as_ref(), RealmVersion(version.into()))
}

fn freeze_realm_version_inner(
    root: &FsPath,
    version: RealmVersion,
) -> Result<FreezeRealmOutput, FreezeRealmError> {
    if version.0.trim().is_empty() {
        return Err(FreezeRealmError::InvalidVersion(version.0));
    }
    let root = canonicalize_for_dedupe(root);
    let manifest = load_realm_manifest(&root)
        .map_err(FreezeRealmError::SourceLoad)?
        .ok_or_else(|| FreezeRealmError::MissingManifest { root: root.clone() })?;
    let snapshot_root = root
        .join(cache::YULANG_PROJECT_DIR)
        .join("versions")
        .join(&version.0);
    let files = collect_freezable_realm_files(&root)?;
    let snapshot = frozen_realm_snapshot(&root, &manifest, version.clone(), &files)?;
    let snapshot_path = snapshot_root.join("snapshot.json");

    if snapshot_root.exists() {
        let existing = read_frozen_realm_snapshot(&snapshot_path)?;
        if existing.source_hash == snapshot.source_hash {
            return Ok(FreezeRealmOutput {
                root: snapshot_root,
                snapshot_path,
                snapshot: existing,
                already_exists: true,
            });
        }
        return Err(FreezeRealmError::SnapshotExistsHashMismatch {
            path: snapshot_root,
            existing_hash: existing.source_hash,
            new_hash: snapshot.source_hash,
        });
    }

    let temp_root = freeze_temp_root(&snapshot_root);
    if temp_root.exists() {
        fs::remove_dir_all(&temp_root).map_err(|error| FreezeRealmError::Io {
            path: temp_root.clone(),
            error,
        })?;
    }
    fs::create_dir_all(&temp_root).map_err(|error| FreezeRealmError::Io {
        path: temp_root.clone(),
        error,
    })?;
    write_frozen_realm_files(&root, &temp_root, &manifest, &version, &files)?;
    let snapshot_json = serde_json::to_string_pretty(&snapshot).map_err(|error| {
        FreezeRealmError::EncodeSnapshot {
            path: snapshot_path.clone(),
            message: error.to_string(),
        }
    })?;
    fs::write(
        temp_root.join("snapshot.json"),
        format!("{snapshot_json}\n"),
    )
    .map_err(|error| FreezeRealmError::Io {
        path: temp_root.join("snapshot.json"),
        error,
    })?;
    ensure_parent_dir(&snapshot_root)?;
    fs::rename(&temp_root, &snapshot_root).map_err(|error| FreezeRealmError::Io {
        path: snapshot_root.clone(),
        error,
    })?;

    Ok(FreezeRealmOutput {
        root: snapshot_root,
        snapshot_path,
        snapshot,
        already_exists: false,
    })
}

fn collect_freezable_realm_files(root: &FsPath) -> Result<Vec<PathBuf>, FreezeRealmError> {
    let mut files = vec![PathBuf::from(cache::YULANG_MANIFEST_FILE)];
    if root.join(cache::YULANG_LOCK_FILE).is_file() {
        files.push(PathBuf::from(cache::YULANG_LOCK_FILE));
    }
    collect_freezable_realm_files_from(root, root, &mut files)?;
    files.sort();
    files.dedup();
    Ok(files)
}

fn collect_freezable_realm_files_from(
    root: &FsPath,
    dir: &FsPath,
    files: &mut Vec<PathBuf>,
) -> Result<(), FreezeRealmError> {
    for entry in fs::read_dir(dir).map_err(|error| FreezeRealmError::Io {
        path: dir.to_path_buf(),
        error,
    })? {
        let entry = entry.map_err(|error| FreezeRealmError::Io {
            path: dir.to_path_buf(),
            error,
        })?;
        let path = entry.path();
        let file_name = entry.file_name();
        if file_name == cache::YULANG_PROJECT_DIR || file_name == "target" {
            continue;
        }
        let file_type = entry.file_type().map_err(|error| FreezeRealmError::Io {
            path: path.clone(),
            error,
        })?;
        if file_type.is_dir() {
            collect_freezable_realm_files_from(root, &path, files)?;
            continue;
        }
        if file_type.is_file() && path.extension().is_some_and(|ext| ext == "yu") {
            let relative = path.strip_prefix(root).unwrap_or(&path).to_path_buf();
            files.push(relative);
        }
    }
    Ok(())
}

fn frozen_realm_snapshot(
    source_root: &FsPath,
    manifest: &SourceRealmManifest,
    version: RealmVersion,
    files: &[PathBuf],
) -> Result<FrozenRealmSnapshot, FreezeRealmError> {
    let frozen_manifest = frozen_realm_manifest_toml(manifest, &version);
    let frozen_manifest_bytes = toml::to_string_pretty(&frozen_manifest)
        .map_err(|error| FreezeRealmError::EncodeManifest {
            path: source_root.join(cache::YULANG_MANIFEST_FILE),
            message: error.to_string(),
        })?
        .into_bytes();
    let mut snapshot_files = Vec::new();
    let mut hash = StableHash::new();
    hash.write_str("frozen-realm-v1");
    hash.write_str(&manifest.id.identity.0);
    hash.write_str(&version.0);
    for file in files {
        let path = file.to_string_lossy().replace('\\', "/");
        let bytes = if file == FsPath::new(cache::YULANG_MANIFEST_FILE) {
            frozen_manifest_bytes.clone()
        } else {
            fs::read(source_root.join(file)).map_err(|error| FreezeRealmError::Io {
                path: source_root.join(file),
                error,
            })?
        };
        let file_hash = stable_hash_bytes(&bytes);
        hash.write_str(&path);
        hash.write_u64(bytes.len() as u64);
        hash.write_u64(file_hash);
        snapshot_files.push(FrozenRealmSnapshotFile {
            path,
            source_len: bytes.len(),
            source_hash: file_hash,
        });
    }
    Ok(FrozenRealmSnapshot {
        format_version: 1,
        identity: manifest.id.identity.clone(),
        version,
        source_hash: hash.finish(),
        files: snapshot_files,
    })
}

fn write_frozen_realm_files(
    source_root: &FsPath,
    output_root: &FsPath,
    manifest: &SourceRealmManifest,
    version: &RealmVersion,
    files: &[PathBuf],
) -> Result<(), FreezeRealmError> {
    for relative in files {
        let output_path = output_root.join(relative);
        ensure_parent_dir(&output_path)?;
        if relative == FsPath::new(cache::YULANG_MANIFEST_FILE) {
            let manifest = frozen_realm_manifest_toml(manifest, version);
            let encoded = toml::to_string_pretty(&manifest).map_err(|error| {
                FreezeRealmError::EncodeManifest {
                    path: output_path.clone(),
                    message: error.to_string(),
                }
            })?;
            fs::write(&output_path, encoded).map_err(|error| FreezeRealmError::Io {
                path: output_path,
                error,
            })?;
        } else {
            fs::copy(source_root.join(relative), &output_path).map_err(|error| {
                FreezeRealmError::Io {
                    path: output_path,
                    error,
                }
            })?;
        }
    }
    Ok(())
}

fn frozen_realm_manifest_toml(
    manifest: &SourceRealmManifest,
    version: &RealmVersion,
) -> RealmManifestToml {
    let dependencies = (!manifest.dependencies.is_empty()).then(|| {
        manifest
            .dependencies
            .iter()
            .map(|dependency| {
                (
                    dependency.identity.0.clone(),
                    dependency.requirement.clone(),
                )
            })
            .collect::<BTreeMap<_, _>>()
    });
    RealmManifestToml {
        realm: Some(RealmManifestRealmToml {
            identity: Some(manifest.id.identity.0.clone()),
            name: None,
            version: Some(version.0.clone()),
        }),
        dependencies,
    }
}

fn read_frozen_realm_snapshot(path: &FsPath) -> Result<FrozenRealmSnapshot, FreezeRealmError> {
    let source = fs::read_to_string(path).map_err(|error| FreezeRealmError::Io {
        path: path.to_path_buf(),
        error,
    })?;
    serde_json::from_str(&source).map_err(|error| FreezeRealmError::InvalidSnapshot {
        path: path.to_path_buf(),
        message: error.to_string(),
    })
}

pub(crate) fn frozen_realm_source_hash(root: &FsPath) -> Option<u64> {
    let snapshot_path = root.join("snapshot.json");
    let source = fs::read_to_string(snapshot_path).ok()?;
    serde_json::from_str::<FrozenRealmSnapshot>(&source)
        .ok()
        .map(|snapshot| snapshot.source_hash)
}

fn freeze_temp_root(snapshot_root: &FsPath) -> PathBuf {
    let millis = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_millis();
    snapshot_root.with_file_name(format!(
        ".{}.tmp-{}-{millis}",
        snapshot_root
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("freeze"),
        std::process::id()
    ))
}

fn ensure_parent_dir(path: &FsPath) -> Result<(), FreezeRealmError> {
    let Some(parent) = path.parent() else {
        return Ok(());
    };
    fs::create_dir_all(parent).map_err(|error| FreezeRealmError::Io {
        path: parent.to_path_buf(),
        error,
    })
}

#[derive(Debug)]
pub enum FreezeRealmError {
    InvalidVersion(String),
    MissingManifest {
        root: PathBuf,
    },
    SourceLoad(SourceLoadError),
    Io {
        path: PathBuf,
        error: io::Error,
    },
    EncodeManifest {
        path: PathBuf,
        message: String,
    },
    EncodeSnapshot {
        path: PathBuf,
        message: String,
    },
    InvalidSnapshot {
        path: PathBuf,
        message: String,
    },
    SnapshotExistsHashMismatch {
        path: PathBuf,
        existing_hash: u64,
        new_hash: u64,
    },
}

impl fmt::Display for FreezeRealmError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FreezeRealmError::InvalidVersion(version) => {
                write!(f, "invalid realm version `{version}`")
            }
            FreezeRealmError::MissingManifest { root } => {
                write!(f, "realm manifest not found under {}", root.display())
            }
            FreezeRealmError::SourceLoad(error) => write!(f, "{error}"),
            FreezeRealmError::Io { path, error } => {
                write!(f, "failed to access {}: {error}", path.display())
            }
            FreezeRealmError::EncodeManifest { path, message } => {
                write!(
                    f,
                    "failed to encode realm manifest {}: {message}",
                    path.display()
                )
            }
            FreezeRealmError::EncodeSnapshot { path, message } => {
                write!(
                    f,
                    "failed to encode realm snapshot {}: {message}",
                    path.display()
                )
            }
            FreezeRealmError::InvalidSnapshot { path, message } => {
                write!(f, "invalid realm snapshot {}: {message}", path.display())
            }
            FreezeRealmError::SnapshotExistsHashMismatch {
                path,
                existing_hash,
                new_hash,
            } => write!(
                f,
                "frozen realm {} already exists with a different hash: existing={existing_hash:016x} new={new_hash:016x}",
                path.display()
            ),
        }
    }
}

impl std::error::Error for FreezeRealmError {}

fn load_realm_lock(root: &FsPath) -> Result<Option<YulangLockFile>, SourceLoadError> {
    let path = root.join(cache::YULANG_LOCK_FILE);
    if !path.is_file() {
        return Ok(None);
    }
    let source = fs::read_to_string(&path).map_err(|error| SourceLoadError::Io {
        path: path.clone(),
        error,
    })?;
    serde_json::from_str::<YulangLockFile>(&source)
        .map(Some)
        .map_err(|error| SourceLoadError::InvalidLockFile {
            path,
            message: error.to_string(),
        })
}

fn invalid_realm_manifest(path: &FsPath, message: impl Into<String>) -> SourceLoadError {
    SourceLoadError::InvalidRealmManifest {
        path: path.to_path_buf(),
        message: message.into(),
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SourceMeta {
    pub module_files: Vec<ModuleFileDecl>,
    pub uses: Vec<UseDeclMeta>,
    pub syntax_exports: Vec<SyntaxExport>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleFileDecl {
    pub visibility: Visibility,
    pub name: Name,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UseDeclMeta {
    pub visibility: Visibility,
    pub import: UseImport,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UseImport {
    Alias {
        name: Name,
        path: ModulePath,
        realm_version: Option<RealmVersion>,
        with_anchor: Option<ModulePath>,
    },
    Glob {
        prefix: ModulePath,
        excluded: Vec<Name>,
        realm_version: Option<RealmVersion>,
        with_anchor: Option<ModulePath>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SyntaxExport {
    pub visibility: Visibility,
    pub name: Name,
    pub op: OpDef,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Visibility {
    Pub,
    Our,
    My,
}

#[derive(Debug, Clone)]
pub struct SourceSet {
    pub files: Vec<SourceFile>,
    pub realms: Vec<SourceRealm>,
}

impl SourceSet {
    pub fn from_files(files: Vec<SourceFile>) -> Self {
        Self::from_files_with_realm(
            files,
            virtual_single_file_realm_id(),
            SourceRealmRoot::Virtual,
        )
    }

    pub fn from_files_with_realm(
        mut files: Vec<SourceFile>,
        realm: ResolvedRealmId,
        root: SourceRealmRoot,
    ) -> Self {
        for file in &mut files {
            file.realm = realm.clone();
            file.realm_path_prefix_len = 0;
        }
        Self::from_files_with_realms(
            files,
            vec![SourceRealmSeed {
                id: realm,
                root,
                dependencies: Vec::new(),
            }],
        )
    }

    fn from_files_with_realms(mut files: Vec<SourceFile>, realms: Vec<SourceRealmSeed>) -> Self {
        let realms = realms
            .into_iter()
            .map(|realm| {
                let file_indices = files
                    .iter()
                    .enumerate()
                    .filter_map(|(idx, file)| (file.realm == realm.id).then_some(idx))
                    .collect::<Vec<_>>();
                let bands = assign_source_bands(&mut files, &file_indices, &realm.id);
                SourceRealm {
                    id: realm.id,
                    root: realm.root,
                    dependencies: realm.dependencies,
                    bands,
                }
            })
            .collect();
        Self { files, realms }
    }

    pub fn with_realm_dependencies(mut self, dependencies: Vec<SourceRealmDependency>) -> Self {
        if let Some(realm) = self.realms.first_mut() {
            realm.dependencies = dependencies;
        }
        self
    }

    pub fn resolved_band(&self, id: &ResolvedBandId) -> Option<&SourceBand> {
        self.realms
            .iter()
            .find(|realm| realm.id == id.realm)?
            .band(&id.band)
    }

    pub fn entry_bands(&self) -> impl Iterator<Item = (&SourceRealm, &SourceBand)> {
        self.realms.iter().flat_map(|realm| {
            realm
                .bands
                .iter()
                .filter(|band| band.entry)
                .map(move |band| (realm, band))
        })
    }

    pub fn files_with_origin(&self, origin: SourceOrigin) -> impl Iterator<Item = &SourceFile> {
        self.files.iter().filter(move |file| file.origin == origin)
    }

    pub fn std_files(&self) -> impl Iterator<Item = &SourceFile> {
        self.files_with_origin(SourceOrigin::Std)
    }

    pub fn entry_files(&self) -> impl Iterator<Item = &SourceFile> {
        self.files_with_origin(SourceOrigin::Entry)
    }

    pub fn user_files(&self) -> impl Iterator<Item = &SourceFile> {
        self.files_with_origin(SourceOrigin::User)
    }

    pub fn compilation_units(&self) -> SourceCompilationUnits {
        SourceCompilationUnits::from_source_set(self)
    }

    pub fn compiled_unit_syntax_artifacts(&self) -> Vec<CompiledUnitSyntaxArtifact> {
        let units = self.compilation_units();
        units.syntax_artifacts(self)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceCompilationUnits {
    pub units: Vec<SourceCompilationUnit>,
    pub file_to_unit: Vec<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceCompilationUnit {
    pub files: Vec<usize>,
    pub dependencies: Vec<usize>,
    pub origin: SourceCompilationUnitOrigin,
    pub syntax_exports: Vec<SyntaxExport>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SourceCompilationUnitOrigin {
    Entry,
    Std,
    User,
    Mixed,
}

impl SourceCompilationUnits {
    fn from_source_set(source_set: &SourceSet) -> Self {
        let dependencies = source_set
            .files
            .iter()
            .enumerate()
            .map(|(file_idx, _)| source_dependencies(file_idx, &source_set.files))
            .collect::<Vec<_>>();
        let components = source_sccs(&dependencies);
        let mut file_to_unit = vec![0; source_set.files.len()];
        for (unit_idx, files) in components.iter().enumerate() {
            for &file_idx in files {
                file_to_unit[file_idx] = unit_idx;
            }
        }

        let units = components
            .iter()
            .map(|files| {
                let mut unit_deps = Vec::new();
                for &file_idx in files {
                    for &dep in &dependencies[file_idx] {
                        let dep_unit = file_to_unit[dep];
                        if dep_unit != file_to_unit[file_idx] {
                            unit_deps.push(dep_unit);
                        }
                    }
                }
                unit_deps.sort_unstable();
                unit_deps.dedup();

                SourceCompilationUnit {
                    files: files.clone(),
                    dependencies: unit_deps,
                    origin: source_unit_origin(files, &source_set.files),
                    syntax_exports: source_unit_syntax_exports(files, &source_set.files),
                }
            })
            .collect();

        Self {
            units,
            file_to_unit,
        }
    }

    pub fn syntax_artifacts(&self, source_set: &SourceSet) -> Vec<CompiledUnitSyntaxArtifact> {
        let public_exports = source_public_syntax_exports(&source_set.files);
        let unit_hashes = self
            .units
            .iter()
            .enumerate()
            .map(|(unit_idx, unit)| {
                compiled_unit_source_hash(unit_idx, unit, &source_set.files, &public_exports)
            })
            .collect::<Vec<_>>();
        let unit_interface_hashes = self
            .units
            .iter()
            .map(|unit| compiled_unit_interface_hash(unit, &source_set.files, &public_exports))
            .collect::<Vec<_>>();

        self.units
            .iter()
            .enumerate()
            .map(|(unit_idx, unit)| {
                let syntax = compiled_syntax_surface(unit, &source_set.files, &public_exports);
                let manifest = compiled_unit_manifest(
                    unit_idx,
                    unit,
                    source_set,
                    &unit_hashes,
                    &unit_interface_hashes,
                    &syntax,
                );
                CompiledUnitSyntaxArtifact { manifest, syntax }
            })
            .collect()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledUnitSyntaxArtifact {
    pub manifest: CompiledUnitManifest,
    pub syntax: CompiledSyntaxSurface,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledUnitManifest {
    pub artifact_format_version: u32,
    pub parser_format_version: u32,
    pub unit_index: usize,
    pub origin: SourceCompilationUnitOrigin,
    pub realms: Vec<ResolvedRealmId>,
    pub bands: Vec<ResolvedBandId>,
    pub files: Vec<CompiledSourceFileIdentity>,
    pub dependencies: Vec<CompiledUnitDependency>,
    pub source_hash: u64,
    pub syntax_hash: u64,
    pub interface_hash: u64,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledSourceFileIdentity {
    pub path: String,
    pub module_path: ModulePath,
    pub origin: SourceOrigin,
    pub source_len: usize,
    pub source_hash: u64,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledUnitDependency {
    pub unit_index: usize,
    pub source_hash: u64,
    pub interface_hash: u64,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledSyntaxSurface {
    pub modules: Vec<CompiledModuleSyntaxSurface>,
    pub direct_exports: Vec<CompiledSyntaxExport>,
    pub public_exports: Vec<CompiledSyntaxExport>,
}

impl CompiledSyntaxSurface {
    pub fn public_op_table_contribution(&self) -> OpTable {
        compiled_exports_op_table(self.public_exports.iter())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledModuleSyntaxSurface {
    pub module_path: ModulePath,
    pub direct_exports: Vec<CompiledSyntaxExport>,
    pub public_exports: Vec<CompiledSyntaxExport>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledSyntaxExport {
    pub visibility: Visibility,
    pub name: Name,
    pub op: CompiledOperatorSyntax,
}

impl CompiledSyntaxExport {
    pub fn to_syntax_export(&self) -> SyntaxExport {
        SyntaxExport {
            visibility: self.visibility,
            name: self.name.clone(),
            op: self.op.to_op_def(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledOperatorSyntax {
    pub prefix: Option<Vec<i8>>,
    pub infix: Option<(Vec<i8>, Vec<i8>)>,
    pub suffix: Option<Vec<i8>>,
    pub nullfix: bool,
}

impl CompiledOperatorSyntax {
    pub fn from_op_def(op: &OpDef) -> Self {
        Self {
            prefix: op.prefix.as_ref().map(compiled_bp_vec),
            infix: op
                .infix
                .as_ref()
                .map(|(left, right)| (compiled_bp_vec(left), compiled_bp_vec(right))),
            suffix: op.suffix.as_ref().map(compiled_bp_vec),
            nullfix: op.nullfix,
        }
    }

    pub fn to_op_def(&self) -> OpDef {
        OpDef {
            prefix: self.prefix.as_ref().map(|bp| runtime_bp_vec(bp)),
            infix: self
                .infix
                .as_ref()
                .map(|(left, right)| (runtime_bp_vec(left), runtime_bp_vec(right))),
            suffix: self.suffix.as_ref().map(|bp| runtime_bp_vec(bp)),
            nullfix: self.nullfix,
        }
    }
}

pub fn op_table_from_compiled_syntax_imports(
    meta: &SourceMeta,
    artifacts: &[CompiledUnitSyntaxArtifact],
) -> OpTable {
    let mut table = standard_op_table();
    for export in &meta.syntax_exports {
        insert_table_op_def(&mut table.0, export.name.clone(), export.op.clone());
    }

    let public_exports = compiled_public_syntax_exports_by_module(artifacts);
    for use_ in &meta.uses {
        let imported = imported_compiled_syntax_exports(&use_.import, &public_exports);
        for export in imported {
            insert_table_op_def(&mut table.0, export.name.clone(), export.op.to_op_def());
        }
    }

    table
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SourceOrigin {
    Entry,
    Std,
    User,
}

#[derive(Debug, Clone)]
pub struct SourceFile {
    pub path: PathBuf,
    pub module_path: ModulePath,
    pub origin: SourceOrigin,
    pub realm: ResolvedRealmId,
    pub realm_path_prefix_len: usize,
    pub band: Option<ResolvedBandId>,
    pub op_table: OpTable,
    pub source_prefix_len: usize,
    pub source: String,
    pub meta: SourceMeta,
}

#[derive(Debug, Clone)]
pub struct InlineSource {
    pub path: PathBuf,
    pub module_path: ModulePath,
    pub origin: SourceOrigin,
    pub source: String,
    pub meta: Option<SourceMeta>,
}

#[derive(Debug)]
pub enum SourceLoadError {
    Io {
        path: PathBuf,
        error: io::Error,
    },
    InvalidRealmManifest {
        path: PathBuf,
        message: String,
    },
    InvalidLockFile {
        path: PathBuf,
        message: String,
    },
    LockedRealmHashMismatch {
        path: PathBuf,
        realm: ResolvedRealmId,
        expected: u64,
        actual: Option<u64>,
    },
    ModuleNotFound {
        parent: PathBuf,
        name: Name,
    },
    AmbiguousModuleFile {
        current: PathBuf,
        name: Name,
        candidates: Vec<PathBuf>,
    },
}

impl fmt::Display for SourceLoadError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SourceLoadError::Io { path, error } => {
                write!(f, "failed to read {}: {error}", path.display())
            }
            SourceLoadError::InvalidRealmManifest { path, message } => {
                write!(f, "invalid realm manifest {}: {message}", path.display())
            }
            SourceLoadError::InvalidLockFile { path, message } => {
                write!(f, "invalid lock file {}: {message}", path.display())
            }
            SourceLoadError::LockedRealmHashMismatch {
                path,
                realm,
                expected,
                actual,
            } => {
                write!(
                    f,
                    "locked realm {} at {} has a different source hash: expected={expected:016x}",
                    format_resolved_realm(realm),
                    path.display()
                )?;
                match actual {
                    Some(actual) => write!(f, " actual={actual:016x}"),
                    None => write!(f, " actual=<missing snapshot>"),
                }
            }
            SourceLoadError::ModuleNotFound { parent, name } => {
                write!(
                    f,
                    "module file for `{}` not found next to {}",
                    name.0,
                    parent.display()
                )
            }
            SourceLoadError::AmbiguousModuleFile {
                current,
                name,
                candidates,
            } => {
                write!(
                    f,
                    "module file for `{}` from {} is ambiguous",
                    name.0,
                    current.display()
                )?;
                for candidate in candidates {
                    write!(f, ": {}", candidate.display())?;
                }
                Ok(())
            }
        }
    }
}

impl std::error::Error for SourceLoadError {}

struct SourceLoader {
    options: SourceOptions,
    lock: Option<YulangLockFile>,
    realms: Vec<SourceRealmSeed>,
    seen: HashSet<PathBuf>,
    files: Vec<SourceFile>,
}

struct InlineSourceLoader {
    options: SourceOptions,
    sources: HashMap<ModulePath, InlineSource>,
    seen: HashSet<ModulePath>,
    files: Vec<SourceFile>,
}

impl InlineSourceLoader {
    fn new(inline_sources: impl IntoIterator<Item = InlineSource>, options: SourceOptions) -> Self {
        Self {
            options,
            sources: inline_sources
                .into_iter()
                .map(|source| (source.module_path.clone(), source))
                .collect(),
            seen: HashSet::new(),
            files: Vec::new(),
        }
    }

    fn load_entry(&mut self, source: &str) {
        let source_prefix = if self.options.implicit_prelude {
            "use std::prelude::*\n"
        } else {
            ""
        };
        self.load_source(
            PathBuf::from("<virtual-entry>"),
            ModulePath { segments: vec![] },
            SourceOrigin::Entry,
            inline_realm_id(),
            0,
            source,
            source_prefix,
            None,
        );
    }

    fn load_module_path(&mut self, module_path: &ModulePath) {
        if module_path.segments.is_empty() || self.seen.contains(module_path) {
            return;
        }
        let Some(source) = self.sources.get(module_path).cloned() else {
            return;
        };
        let InlineSource {
            path,
            module_path,
            origin,
            source,
            meta,
        } = source;
        self.load_source(
            path,
            module_path,
            origin,
            inline_realm_id(),
            0,
            &source,
            "",
            meta,
        );
    }

    fn load_source(
        &mut self,
        path: PathBuf,
        module_path: ModulePath,
        origin: SourceOrigin,
        realm: ResolvedRealmId,
        realm_path_prefix_len: usize,
        source: &str,
        source_prefix: &str,
        cached_meta: Option<SourceMeta>,
    ) {
        if !self.seen.insert(module_path.clone()) {
            return;
        }

        let source_prefix_len = source_prefix.len();
        let mut source = source.to_string();
        if !source_prefix.is_empty() {
            source.insert_str(0, source_prefix);
        }
        let meta = cached_meta.unwrap_or_else(|| parse_source_meta(&source));
        let dependencies = inline_dependencies(&module_path, &meta);
        self.files.push(SourceFile {
            path,
            module_path,
            origin,
            realm,
            realm_path_prefix_len,
            band: None,
            op_table: standard_op_table(),
            source_prefix_len,
            source,
            meta,
        });
        for dependency in dependencies {
            self.load_module_path(&dependency);
        }
    }
}

impl SourceLoader {
    fn new(options: SourceOptions, lock: Option<YulangLockFile>) -> Self {
        Self {
            options,
            lock,
            realms: Vec::new(),
            seen: HashSet::new(),
            files: Vec::new(),
        }
    }

    fn register_realm(
        &mut self,
        id: ResolvedRealmId,
        root: SourceRealmRoot,
        dependencies: Vec<SourceRealmDependency>,
    ) {
        if self.realms.iter().any(|realm| realm.id == id) {
            return;
        }
        self.realms.push(SourceRealmSeed {
            id,
            root,
            dependencies,
        });
    }

    fn load_entry(&mut self, path: &FsPath, realm: ResolvedRealmId) -> Result<(), SourceLoadError> {
        let source_prefix = if self.options.implicit_prelude && self.options.std_root.is_some() {
            "use std::prelude::*\n"
        } else {
            ""
        };
        self.load_module_with_prefix(
            path,
            ModulePath { segments: vec![] },
            SourceOrigin::Entry,
            realm,
            0,
            source_prefix,
        )
    }

    fn load_virtual_entry(
        &mut self,
        source: &str,
        base_dir: Option<&FsPath>,
    ) -> Result<(), SourceLoadError> {
        let source_prefix = if self.options.implicit_prelude && self.options.std_root.is_some() {
            "use std::prelude::*\n"
        } else {
            ""
        };
        self.load_virtual_module_with_prefix(
            source,
            ModulePath { segments: vec![] },
            SourceOrigin::Entry,
            virtual_single_file_realm_id(),
            0,
            source_prefix,
            base_dir,
        )
    }

    fn load_module(
        &mut self,
        path: &FsPath,
        module_path: ModulePath,
        origin: SourceOrigin,
        realm: ResolvedRealmId,
        realm_path_prefix_len: usize,
    ) -> Result<(), SourceLoadError> {
        self.load_module_with_prefix(path, module_path, origin, realm, realm_path_prefix_len, "")
    }

    fn load_module_with_prefix(
        &mut self,
        path: &FsPath,
        module_path: ModulePath,
        origin: SourceOrigin,
        realm: ResolvedRealmId,
        realm_path_prefix_len: usize,
        source_prefix: &str,
    ) -> Result<(), SourceLoadError> {
        let canonical = canonicalize_for_dedupe(path);
        if !self.seen.insert(canonical) {
            return Ok(());
        }

        let source_prefix_len = source_prefix.len();
        let mut source = fs::read_to_string(path).map_err(|error| SourceLoadError::Io {
            path: path.to_path_buf(),
            error,
        })?;
        if !source_prefix.is_empty() {
            source.insert_str(0, source_prefix);
        }
        let meta = parse_source_meta(&source);
        let module_paths = meta
            .module_files
            .iter()
            .map(|decl| {
                let mut child_module = module_path.segments.clone();
                child_module.push(decl.name.clone());
                resolve_module_file(path, &decl.name).map(|path| {
                    (
                        path,
                        ModulePath {
                            segments: child_module,
                        },
                        child_origin(origin),
                    )
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let mut imported_paths = Vec::new();
        for use_ in &meta.uses {
            let Some(module_path) = import_module_path(&use_.import) else {
                continue;
            };
            if let Some(imported) =
                self.resolve_import_module_file(&realm, &module_path, &use_.import)?
            {
                imported_paths.push(imported);
            }
        }

        self.files.push(SourceFile {
            path: path.to_path_buf(),
            module_path,
            origin,
            realm: realm.clone(),
            realm_path_prefix_len,
            band: None,
            op_table: standard_op_table(),
            source_prefix_len,
            source,
            meta,
        });

        for (path, module_path, origin) in module_paths {
            self.load_module(
                &path,
                module_path,
                origin,
                realm.clone(),
                realm_path_prefix_len,
            )?;
        }
        for imported in imported_paths {
            self.load_module(
                &imported.path,
                imported.module_path,
                imported.origin,
                imported.realm,
                imported.realm_path_prefix_len,
            )?;
        }
        Ok(())
    }

    fn load_virtual_module_with_prefix(
        &mut self,
        source: &str,
        module_path: ModulePath,
        origin: SourceOrigin,
        realm: ResolvedRealmId,
        realm_path_prefix_len: usize,
        source_prefix: &str,
        base_dir: Option<&FsPath>,
    ) -> Result<(), SourceLoadError> {
        let synthetic_path = base_dir
            .map(|dir| dir.join("<virtual-entry>"))
            .unwrap_or_else(|| PathBuf::from("<virtual-entry>"));
        let canonical = canonicalize_for_dedupe(&synthetic_path);
        if !self.seen.insert(canonical) {
            return Ok(());
        }

        let source_prefix_len = source_prefix.len();
        let mut source = source.to_string();
        if !source_prefix.is_empty() {
            source.insert_str(0, source_prefix);
        }
        let meta = parse_source_meta(&source);
        let module_paths = meta
            .module_files
            .iter()
            .map(|decl| {
                let mut child_module = module_path.segments.clone();
                child_module.push(decl.name.clone());
                resolve_module_file(&synthetic_path, &decl.name).map(|path| {
                    (
                        path,
                        ModulePath {
                            segments: child_module,
                        },
                        child_origin(origin),
                    )
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let mut imported_paths = Vec::new();
        for use_ in &meta.uses {
            let Some(module_path) = import_module_path(&use_.import) else {
                continue;
            };
            if let Some(imported) =
                self.resolve_import_module_file(&realm, &module_path, &use_.import)?
            {
                imported_paths.push(imported);
            }
        }

        self.files.push(SourceFile {
            path: synthetic_path,
            module_path,
            origin,
            realm: realm.clone(),
            realm_path_prefix_len,
            band: None,
            op_table: standard_op_table(),
            source_prefix_len,
            source,
            meta,
        });

        for (path, module_path, origin) in module_paths {
            self.load_module(
                &path,
                module_path,
                origin,
                realm.clone(),
                realm_path_prefix_len,
            )?;
        }
        for imported in imported_paths {
            self.load_module(
                &imported.path,
                imported.module_path,
                imported.origin,
                imported.realm,
                imported.realm_path_prefix_len,
            )?;
        }
        Ok(())
    }

    fn resolve_import_module_file(
        &mut self,
        requester_realm: &ResolvedRealmId,
        module_path: &ModulePath,
        import: &UseImport,
    ) -> Result<Option<ResolvedImport>, SourceLoadError> {
        if module_path.segments.is_empty() {
            return Ok(None);
        }

        if module_path
            .segments
            .first()
            .is_some_and(|name| name.0 == "std")
        {
            let Some(std_root) = self.options.std_root.as_ref() else {
                return Ok(None);
            };
            let Some(path) = resolve_module_path_under_root(std_root, &module_path.segments[1..])
            else {
                return Ok(None);
            };
            return Ok(Some(ResolvedImport {
                path,
                module_path: module_path.clone(),
                origin: SourceOrigin::Std,
                realm: requester_realm.clone(),
                realm_path_prefix_len: 0,
            }));
        }

        if let Some(external) = self.resolve_cross_realm_import(module_path, import)? {
            return Ok(Some(external));
        }

        let Some(path) = self
            .options
            .search_paths
            .iter()
            .find_map(|root| resolve_module_path_under_root(root, &module_path.segments))
        else {
            return Ok(None);
        };
        Ok(Some(ResolvedImport {
            path,
            module_path: module_path.clone(),
            origin: import_origin(module_path),
            realm: requester_realm.clone(),
            realm_path_prefix_len: 0,
        }))
    }

    fn resolve_cross_realm_import(
        &mut self,
        module_path: &ModulePath,
        import: &UseImport,
    ) -> Result<Option<ResolvedImport>, SourceLoadError> {
        let import_version = import_realm_version(import);
        let with_version = self.resolve_locked_with_constraint_version(module_path, import);
        let Some(locked_version) =
            selected_import_version(import_version.as_ref(), with_version.as_ref())
        else {
            return Ok(None);
        };
        if let Some(locked) = self.resolve_locked_realm_import(module_path, locked_version)? {
            return Ok(Some(locked));
        }

        let Some((dependency, identity_len)) =
            self.resolve_manifest_dependency_prefix(module_path, import_version.as_ref())
        else {
            return Ok(None);
        };
        let selected_version = locked_version
            .cloned()
            .or_else(|| exact_dependency_version(&dependency.requirement));
        let (root_path, root) = if let Some(version) = selected_version.as_ref() {
            let Some(root) = self.find_existing_realm_root(&dependency.identity, Some(version))
            else {
                return Ok(None);
            };
            root
        } else {
            let Some(root) = self.find_existing_realm_root_for_requirement(
                &dependency.identity,
                &dependency.requirement,
            ) else {
                return Ok(None);
            };
            root
        };
        let manifest = load_realm_manifest(&root_path).ok().flatten();
        let realm = manifest
            .as_ref()
            .map(|manifest| manifest.id.clone())
            .unwrap_or_else(|| ResolvedRealmId {
                identity: dependency.identity.clone(),
                version: selected_version.clone(),
            });
        let dependencies = manifest
            .map(|manifest| manifest.dependencies)
            .unwrap_or_default();
        let module_tail = &module_path.segments[identity_len..];
        if module_tail.is_empty() {
            return Ok(None);
        }
        let Some(path) = resolve_module_path_under_root(&root_path, module_tail) else {
            return Ok(None);
        };
        self.register_realm(realm.clone(), root, dependencies);
        Ok(Some(ResolvedImport {
            path,
            module_path: module_path.clone(),
            origin: SourceOrigin::User,
            realm,
            realm_path_prefix_len: identity_len,
        }))
    }

    fn resolve_locked_realm_import(
        &mut self,
        module_path: &ModulePath,
        import_version: Option<&RealmVersion>,
    ) -> Result<Option<ResolvedImport>, SourceLoadError> {
        let Some(lock) = self.lock.clone() else {
            return Ok(None);
        };
        let locked = lock
            .realms
            .iter()
            .filter_map(|realm| {
                if import_version.is_some() && realm.id.version.as_ref() != import_version {
                    return None;
                }
                let identity_len = realm_identity_prefix_len(&realm.id.identity, module_path)?;
                Some((identity_len, realm.clone()))
            })
            .max_by_key(|(identity_len, _)| *identity_len);
        let Some(locked) = locked else {
            return Ok(None);
        };
        let identity_len = locked.0;
        let realm = locked.1;
        let Some(root_path) = locked_realm_source_path(&realm.source) else {
            return Ok(None);
        };
        validate_locked_realm_source_hash(&root_path, &realm)?;
        let module_tail = &module_path.segments[identity_len..];
        if module_tail.is_empty() {
            return Ok(None);
        }
        let Some(path) = resolve_module_path_under_root(&root_path, module_tail) else {
            return Ok(None);
        };
        let manifest = load_realm_manifest(&root_path).ok().flatten();
        let dependencies = manifest
            .map(|manifest| manifest.dependencies)
            .unwrap_or_default();
        self.register_realm(realm.id.clone(), realm.source.into(), dependencies);
        Ok(Some(ResolvedImport {
            path,
            module_path: module_path.clone(),
            origin: SourceOrigin::User,
            realm: realm.id,
            realm_path_prefix_len: identity_len,
        }))
    }

    fn resolve_locked_with_constraint_version(
        &self,
        module_path: &ModulePath,
        import: &UseImport,
    ) -> Option<RealmVersion> {
        let lock = self.lock.as_ref()?;
        let anchor = import_with_anchor(import)?;
        lock.with_constraints
            .iter()
            .filter(|constraint| constraint.anchor == anchor)
            .filter_map(|constraint| {
                let identity_len = realm_identity_prefix_len(&constraint.target, module_path)?;
                Some((identity_len, constraint.resolved.version.clone()))
            })
            .max_by_key(|(identity_len, _)| *identity_len)
            .and_then(|(_, version)| version)
    }

    fn resolve_manifest_dependency_prefix(
        &self,
        module_path: &ModulePath,
        import_version: Option<&RealmVersion>,
    ) -> Option<(SourceRealmDependency, usize)> {
        self.realms
            .iter()
            .flat_map(|realm| realm.dependencies.iter())
            .filter_map(|dependency| {
                let identity_len = realm_identity_prefix_len(&dependency.identity, module_path)?;
                if import_version.is_none() && dependency.requirement.trim().is_empty() {
                    return None;
                }
                Some((dependency.clone(), identity_len))
            })
            .max_by_key(|(_, identity_len)| *identity_len)
    }

    fn find_existing_realm_root(
        &self,
        identity: &RealmIdentity,
        version: Option<&RealmVersion>,
    ) -> Option<(PathBuf, SourceRealmRoot)> {
        for search_root in &self.options.search_paths {
            let root = search_root.join(realm_identity_path(identity));
            if let Some(version) = version {
                let frozen = root
                    .join(cache::YULANG_PROJECT_DIR)
                    .join("versions")
                    .join(&version.0);
                if realm_root_matches(&frozen, identity, Some(version)) {
                    return Some((frozen.clone(), SourceRealmRoot::Local(frozen)));
                }
            }
            if realm_root_matches(&root, identity, version) {
                return Some((root.clone(), SourceRealmRoot::Local(root)));
            }
        }

        let mut cached = default_user_cache_root()
            .join("realms")
            .join(realm_identity_path(identity));
        if let Some(version) = version {
            cached.push(&version.0);
        }
        if realm_root_matches(&cached, identity, version) {
            return Some((cached.clone(), SourceRealmRoot::Cached(cached)));
        }
        None
    }

    fn find_existing_realm_root_for_requirement(
        &self,
        identity: &RealmIdentity,
        requirement: &str,
    ) -> Option<(PathBuf, SourceRealmRoot)> {
        let mut candidates = Vec::new();

        for search_root in &self.options.search_paths {
            let root = search_root.join(realm_identity_path(identity));
            push_realm_root_candidate(
                &mut candidates,
                root.clone(),
                SourceRealmRoot::Local(root.clone()),
                identity,
                requirement,
            );

            let frozen_root = root.join(cache::YULANG_PROJECT_DIR).join("versions");
            push_realm_root_child_candidates(
                &mut candidates,
                &frozen_root,
                SourceRealmRootKind::Local,
                identity,
                requirement,
            );
        }

        let cached = default_user_cache_root()
            .join("realms")
            .join(realm_identity_path(identity));
        push_realm_root_candidate(
            &mut candidates,
            cached.clone(),
            SourceRealmRoot::Cached(cached.clone()),
            identity,
            requirement,
        );
        push_realm_root_child_candidates(
            &mut candidates,
            &cached,
            SourceRealmRootKind::Cached,
            identity,
            requirement,
        );

        candidates
            .into_iter()
            .max_by(compare_realm_root_candidates)
            .map(|candidate| (candidate.path, candidate.root))
    }
}

#[derive(Debug, Clone)]
struct ResolvedImport {
    path: PathBuf,
    module_path: ModulePath,
    origin: SourceOrigin,
    realm: ResolvedRealmId,
    realm_path_prefix_len: usize,
}

impl From<LockedRealmSource> for SourceRealmRoot {
    fn from(source: LockedRealmSource) -> Self {
        match source {
            LockedRealmSource::Local(path) => SourceRealmRoot::Local(path),
            LockedRealmSource::Cached(path) => SourceRealmRoot::Cached(path),
            LockedRealmSource::Embedded(name) => SourceRealmRoot::Embedded(name),
            LockedRealmSource::Virtual => SourceRealmRoot::Virtual,
        }
    }
}

fn locked_realm_source_path(source: &LockedRealmSource) -> Option<PathBuf> {
    match source {
        LockedRealmSource::Local(path) | LockedRealmSource::Cached(path) => Some(path.clone()),
        LockedRealmSource::Embedded(_) | LockedRealmSource::Virtual => None,
    }
}

fn validate_locked_realm_source_hash(
    root_path: &FsPath,
    realm: &LockedRealm,
) -> Result<(), SourceLoadError> {
    let Some(expected) = realm.source_hash else {
        return Ok(());
    };
    let actual = frozen_realm_source_hash(root_path);
    if actual == Some(expected) {
        return Ok(());
    }
    Err(SourceLoadError::LockedRealmHashMismatch {
        path: root_path.to_path_buf(),
        realm: realm.id.clone(),
        expected,
        actual,
    })
}

fn realm_identity_prefix_len(identity: &RealmIdentity, module_path: &ModulePath) -> Option<usize> {
    let identity_segments = realm_identity_segments(identity);
    if identity_segments.is_empty() || identity_segments.len() >= module_path.segments.len() {
        return None;
    }
    identity_segments
        .iter()
        .zip(&module_path.segments)
        .all(|(left, right)| left == &right.0)
        .then_some(identity_segments.len())
}

fn realm_identity_segments(identity: &RealmIdentity) -> Vec<String> {
    identity
        .0
        .split('/')
        .filter(|segment| !segment.is_empty())
        .map(str::to_string)
        .collect()
}

fn realm_identity_path(identity: &RealmIdentity) -> PathBuf {
    identity
        .0
        .split('/')
        .filter(|segment| !segment.is_empty())
        .collect()
}

fn realm_root_matches(
    root: &FsPath,
    identity: &RealmIdentity,
    version: Option<&RealmVersion>,
) -> bool {
    let Ok(Some(manifest)) = load_realm_manifest(root) else {
        return false;
    };
    manifest.id.identity == *identity
        && version.is_none_or(|version| manifest.id.version.as_ref() == Some(version))
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RealmRootCandidate {
    path: PathBuf,
    root: SourceRealmRoot,
    version: RealmVersion,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SourceRealmRootKind {
    Local,
    Cached,
}

impl SourceRealmRootKind {
    fn root(self, path: PathBuf) -> SourceRealmRoot {
        match self {
            SourceRealmRootKind::Local => SourceRealmRoot::Local(path),
            SourceRealmRootKind::Cached => SourceRealmRoot::Cached(path),
        }
    }
}

fn push_realm_root_candidate(
    candidates: &mut Vec<RealmRootCandidate>,
    path: PathBuf,
    root: SourceRealmRoot,
    identity: &RealmIdentity,
    requirement: &str,
) {
    let Ok(Some(manifest)) = load_realm_manifest(&path) else {
        return;
    };
    if manifest.id.identity != *identity {
        return;
    }
    let Some(version) = manifest.id.version else {
        return;
    };
    if !version_satisfies_requirement(&version, requirement) {
        return;
    }
    candidates.push(RealmRootCandidate {
        path,
        root,
        version,
    });
}

fn push_realm_root_child_candidates(
    candidates: &mut Vec<RealmRootCandidate>,
    root: &FsPath,
    root_kind: SourceRealmRootKind,
    identity: &RealmIdentity,
    requirement: &str,
) {
    let Ok(entries) = fs::read_dir(root) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if !entry.file_type().is_ok_and(|ty| ty.is_dir()) {
            continue;
        }
        push_realm_root_candidate(
            candidates,
            path.clone(),
            root_kind.root(path),
            identity,
            requirement,
        );
    }
}

fn compare_realm_root_candidates(
    left: &RealmRootCandidate,
    right: &RealmRootCandidate,
) -> Ordering {
    compare_realm_versions(&left.version, &right.version)
}

fn compare_realm_versions(left: &RealmVersion, right: &RealmVersion) -> Ordering {
    match (parse_realm_version(left), parse_realm_version(right)) {
        (Some(left), Some(right)) => left.cmp(&right),
        (Some(_), None) => Ordering::Greater,
        (None, Some(_)) => Ordering::Less,
        (None, None) => left.0.cmp(&right.0),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct ParsedRealmVersion {
    major: u64,
    minor: u64,
    patch: u64,
}

fn parse_realm_version(version: &RealmVersion) -> Option<ParsedRealmVersion> {
    parse_realm_version_str(&version.0)
}

fn parse_realm_version_str(version: &str) -> Option<ParsedRealmVersion> {
    let core = version
        .trim()
        .strip_prefix('v')
        .unwrap_or_else(|| version.trim())
        .split(['-', '+'])
        .next()
        .unwrap_or_default();
    if core.is_empty() {
        return None;
    }
    let mut parts = core.split('.');
    let major = parts.next()?.parse().ok()?;
    let minor = parts.next().unwrap_or("0").parse().ok()?;
    let patch = parts.next().unwrap_or("0").parse().ok()?;
    if parts.next().is_some() {
        return None;
    }
    Some(ParsedRealmVersion {
        major,
        minor,
        patch,
    })
}

fn version_satisfies_requirement(version: &RealmVersion, requirement: &str) -> bool {
    let requirement = requirement.trim();
    if requirement.is_empty() {
        return false;
    }
    if let Some(base) = requirement.strip_prefix('^') {
        return version_satisfies_caret(version, base);
    }
    if let Some(base) = requirement.strip_prefix('~') {
        return version_satisfies_tilde(version, base);
    }
    if exact_dependency_version(requirement).is_some() {
        return version_matches_exact_requirement(version, requirement);
    }
    false
}

fn version_satisfies_caret(version: &RealmVersion, base: &str) -> bool {
    let Some(version) = parse_realm_version(version) else {
        return false;
    };
    let Some(base) = parse_realm_version_str(base) else {
        return false;
    };
    let upper = if base.major > 0 {
        ParsedRealmVersion {
            major: base.major + 1,
            minor: 0,
            patch: 0,
        }
    } else if base.minor > 0 {
        ParsedRealmVersion {
            major: 0,
            minor: base.minor + 1,
            patch: 0,
        }
    } else {
        ParsedRealmVersion {
            major: 0,
            minor: 0,
            patch: base.patch + 1,
        }
    };
    version >= base && version < upper
}

fn version_satisfies_tilde(version: &RealmVersion, base: &str) -> bool {
    let Some(version) = parse_realm_version(version) else {
        return false;
    };
    let Some(base) = parse_realm_version_str(base) else {
        return false;
    };
    let upper = ParsedRealmVersion {
        major: base.major,
        minor: base.minor + 1,
        patch: 0,
    };
    version >= base && version < upper
}

fn version_matches_exact_requirement(version: &RealmVersion, requirement: &str) -> bool {
    if version.0 == requirement {
        return true;
    }
    parse_realm_version(version) == parse_realm_version_str(requirement)
}

fn format_resolved_realm(realm: &ResolvedRealmId) -> String {
    match &realm.version {
        Some(version) => format!("{}@{}", realm.identity.0, version.0),
        None => realm.identity.0.clone(),
    }
}

fn exact_dependency_version(requirement: &str) -> Option<RealmVersion> {
    let requirement = requirement.trim();
    if requirement.is_empty()
        || requirement
            .chars()
            .any(|ch| matches!(ch, '^' | '~' | '*' | '<' | '>' | '=' | ',' | ' '))
    {
        return None;
    }
    Some(RealmVersion(requirement.to_string()))
}

fn selected_import_version<'a>(
    import_version: Option<&'a RealmVersion>,
    with_version: Option<&'a RealmVersion>,
) -> Option<Option<&'a RealmVersion>> {
    if let (Some(import_version), Some(with_version)) = (import_version, with_version)
        && import_version != with_version
    {
        return None;
    }
    Some(import_version.or(with_version))
}

fn import_realm_version(import: &UseImport) -> Option<RealmVersion> {
    match import {
        UseImport::Alias { realm_version, .. } | UseImport::Glob { realm_version, .. } => {
            realm_version.clone()
        }
    }
}

fn import_with_anchor(import: &UseImport) -> Option<BandPath> {
    match import {
        UseImport::Alias { with_anchor, .. } | UseImport::Glob { with_anchor, .. } => with_anchor
            .as_ref()
            .map(|path| BandPath::from_segments(path.segments.clone())),
    }
}

fn child_origin(parent: SourceOrigin) -> SourceOrigin {
    match parent {
        SourceOrigin::Std => SourceOrigin::Std,
        SourceOrigin::Entry | SourceOrigin::User => SourceOrigin::User,
    }
}

fn import_origin(module_path: &ModulePath) -> SourceOrigin {
    if module_path
        .segments
        .first()
        .is_some_and(|name| name.0 == "std")
    {
        SourceOrigin::Std
    } else {
        SourceOrigin::User
    }
}

fn collect_leading_meta_items(root: &SyntaxNode<YulangLanguage>, meta: &mut SourceMeta) {
    for node in root.children() {
        if node.kind() == SyntaxKind::IndentBlock {
            collect_leading_meta_items(&node, meta);
            return;
        }

        if node.kind() == SyntaxKind::DocCommentDecl {
            continue;
        }

        if let Some(decl) = module_file_decl(&node) {
            meta.module_files.push(decl);
            continue;
        }

        if node.kind() == SyntaxKind::UseDecl {
            if let Some(decl) = use_mod_module_file_decl(&node) {
                meta.module_files.push(decl);
            }
            let visibility = lower_visibility(&node);
            meta.uses.extend(
                use_decl_imports(&node)
                    .into_iter()
                    .map(|import| UseDeclMeta { visibility, import }),
            );
            continue;
        }

        if let Some(export) = syntax_export(&node) {
            meta.syntax_exports.push(export);
            continue;
        }

        break;
    }
}

fn sort_files_topologically(files: &mut Vec<SourceFile>) {
    let dependencies = files
        .iter()
        .enumerate()
        .map(|(file_idx, _)| source_dependencies(file_idx, files))
        .collect::<Vec<_>>();
    let mut marks = vec![VisitMark::Unvisited; files.len()];
    let mut order = Vec::new();

    for idx in 0..files.len() {
        visit_source_file(idx, &dependencies, &mut marks, &mut order);
    }

    let mut old = std::mem::take(files)
        .into_iter()
        .map(Some)
        .collect::<Vec<_>>();
    *files = order
        .into_iter()
        .filter_map(|idx| old[idx].take())
        .collect();
}

fn assign_source_bands(
    files: &mut [SourceFile],
    file_indices: &[usize],
    realm: &ResolvedRealmId,
) -> Vec<SourceBand> {
    let mod_dependencies = files
        .iter()
        .enumerate()
        .map(|(file_idx, _)| source_mod_dependencies(file_idx, files))
        .collect::<Vec<_>>();
    let mut incoming = vec![0usize; files.len()];
    for &file_idx in file_indices {
        let deps = &mod_dependencies[file_idx];
        for &dep in deps {
            incoming[dep] += 1;
        }
    }

    let mut roots = incoming
        .iter()
        .enumerate()
        .filter_map(|(idx, count)| (files[idx].realm == *realm && *count == 0).then_some(idx))
        .collect::<Vec<_>>();
    if roots.is_empty() {
        roots.extend(file_indices.first().copied());
    }

    let mut assigned = vec![false; files.len()];
    let mut bands = Vec::new();
    for root_idx in roots {
        if assigned[root_idx] {
            continue;
        }
        let band_path = source_file_band_path(&files[root_idx]);
        let band_id = ResolvedBandId {
            realm: realm.clone(),
            band: band_path.clone(),
        };
        let mut stack = vec![root_idx];
        let mut band_files = Vec::new();
        while let Some(file_idx) = stack.pop() {
            if assigned[file_idx] {
                continue;
            }
            assigned[file_idx] = true;
            files[file_idx].band = Some(band_id.clone());
            band_files.push(file_idx);
            for &dep in &mod_dependencies[file_idx] {
                stack.push(dep);
            }
        }
        band_files.sort_unstable();
        let entry = band_files
            .iter()
            .any(|&file_idx| files[file_idx].origin == SourceOrigin::Entry);
        bands.push(SourceBand {
            path: band_path,
            files: band_files,
            entry,
        });
    }

    for &file_idx in file_indices {
        if assigned[file_idx] {
            continue;
        }
        let band_path = source_file_band_path(&files[file_idx]);
        let band_id = ResolvedBandId {
            realm: realm.clone(),
            band: band_path.clone(),
        };
        files[file_idx].band = Some(band_id);
        bands.push(SourceBand {
            path: band_path,
            files: vec![file_idx],
            entry: files[file_idx].origin == SourceOrigin::Entry,
        });
    }

    bands.sort_by(|a, b| a.path.segments.cmp(&b.path.segments));
    bands
}

fn source_file_band_path(file: &SourceFile) -> BandPath {
    let prefix_len = file
        .realm_path_prefix_len
        .min(file.module_path.segments.len());
    BandPath::from_segments(
        file.module_path.segments[prefix_len..]
            .first()
            .cloned()
            .into_iter()
            .collect(),
    )
}

fn source_dependencies(file_idx: usize, files: &[SourceFile]) -> Vec<usize> {
    let mut deps = source_mod_dependencies(file_idx, files);
    let file = &files[file_idx];

    for use_ in &file.meta.uses {
        match &use_.import {
            UseImport::Alias { path, .. } => {
                push_best_module_dependency(path, file_idx, files, &mut deps);
            }
            UseImport::Glob { prefix, .. } => {
                push_best_module_dependency(prefix, file_idx, files, &mut deps);
            }
        }
    }

    deps.sort_unstable();
    deps.dedup();
    deps
}

fn source_mod_dependencies(file_idx: usize, files: &[SourceFile]) -> Vec<usize> {
    let mut deps = Vec::new();
    let file = &files[file_idx];
    for decl in &file.meta.module_files {
        let mut child = file.module_path.segments.clone();
        child.push(decl.name.clone());
        push_module_dependency(&child, file_idx, files, &mut deps);
    }
    deps.sort_unstable();
    deps.dedup();
    deps
}

fn source_sccs(dependencies: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let mut ctx = SourceSccContext {
        dependencies,
        index: 0,
        stack: Vec::new(),
        on_stack: vec![false; dependencies.len()],
        indices: vec![None; dependencies.len()],
        lowlink: vec![0; dependencies.len()],
        components: Vec::new(),
    };
    for file in 0..dependencies.len() {
        if ctx.indices[file].is_none() {
            source_scc_connect(file, &mut ctx);
        }
    }
    ctx.components.reverse();
    ctx.components
}

struct SourceSccContext<'a> {
    dependencies: &'a [Vec<usize>],
    index: usize,
    stack: Vec<usize>,
    on_stack: Vec<bool>,
    indices: Vec<Option<usize>>,
    lowlink: Vec<usize>,
    components: Vec<Vec<usize>>,
}

fn source_scc_connect(file: usize, ctx: &mut SourceSccContext<'_>) {
    ctx.indices[file] = Some(ctx.index);
    ctx.lowlink[file] = ctx.index;
    ctx.index += 1;
    ctx.stack.push(file);
    ctx.on_stack[file] = true;

    for &dep in &ctx.dependencies[file] {
        if ctx.indices[dep].is_none() {
            source_scc_connect(dep, ctx);
            ctx.lowlink[file] = ctx.lowlink[file].min(ctx.lowlink[dep]);
        } else if ctx.on_stack[dep] {
            ctx.lowlink[file] = ctx.lowlink[file].min(ctx.indices[dep].unwrap());
        }
    }

    if ctx.lowlink[file] == ctx.indices[file].unwrap() {
        let mut component = Vec::new();
        while let Some(member) = ctx.stack.pop() {
            ctx.on_stack[member] = false;
            component.push(member);
            if member == file {
                break;
            }
        }
        component.sort_unstable();
        ctx.components.push(component);
    }
}

fn source_unit_origin(files: &[usize], source_files: &[SourceFile]) -> SourceCompilationUnitOrigin {
    let mut origin = None;
    for &file in files {
        match origin {
            None => origin = Some(source_files[file].origin),
            Some(existing) if existing == source_files[file].origin => {}
            Some(_) => return SourceCompilationUnitOrigin::Mixed,
        }
    }
    match origin.unwrap_or(SourceOrigin::User) {
        SourceOrigin::Entry => SourceCompilationUnitOrigin::Entry,
        SourceOrigin::Std => SourceCompilationUnitOrigin::Std,
        SourceOrigin::User => SourceCompilationUnitOrigin::User,
    }
}

fn source_unit_syntax_exports(files: &[usize], source_files: &[SourceFile]) -> Vec<SyntaxExport> {
    let mut exports = Vec::new();
    for &file in files {
        exports.extend(source_files[file].meta.syntax_exports.iter().cloned());
    }
    exports.sort_by(|left, right| left.name.0.cmp(&right.name.0));
    exports
}

fn source_public_syntax_exports(source_files: &[SourceFile]) -> Vec<HashMap<Name, OpDef>> {
    let module_paths = source_files
        .iter()
        .map(|file| file.module_path.clone())
        .collect::<Vec<_>>();
    let mut public_exports = source_files
        .iter()
        .map(|file| local_public_syntax_exports(&file.meta))
        .collect::<Vec<_>>();

    let mut changed = true;
    while changed {
        changed = false;
        for idx in 0..source_files.len() {
            for use_ in &source_files[idx].meta.uses {
                if use_.visibility == Visibility::My {
                    continue;
                }
                let imported =
                    imported_syntax_exports(&use_.import, &module_paths, &public_exports);
                for (name, op) in imported {
                    changed |= insert_export_op_def(&mut public_exports[idx], name, op);
                }
            }
        }
    }

    public_exports
}

fn compiled_unit_manifest(
    unit_idx: usize,
    unit: &SourceCompilationUnit,
    source_set: &SourceSet,
    unit_hashes: &[u64],
    unit_interface_hashes: &[u64],
    syntax: &CompiledSyntaxSurface,
) -> CompiledUnitManifest {
    let (realms, bands) = compiled_unit_realm_band_identities(unit, source_set);
    let files = unit
        .files
        .iter()
        .map(|&file_idx| {
            let file = &source_set.files[file_idx];
            CompiledSourceFileIdentity {
                path: file.path.to_string_lossy().to_string(),
                module_path: file.module_path.clone(),
                origin: file.origin,
                source_len: file.source.len(),
                source_hash: stable_hash_bytes(file.source.as_bytes()),
            }
        })
        .collect::<Vec<_>>();
    let dependencies = unit
        .dependencies
        .iter()
        .map(|&dep| CompiledUnitDependency {
            unit_index: dep,
            source_hash: unit_hashes[dep],
            interface_hash: unit_interface_hashes[dep],
        })
        .collect::<Vec<_>>();
    let source_hash = unit_hashes[unit_idx];
    let syntax_hash = stable_hash_compiled_exports(&syntax.public_exports);
    let interface_hash = unit_interface_hashes[unit_idx];

    CompiledUnitManifest {
        artifact_format_version: COMPILED_UNIT_ARTIFACT_FORMAT_VERSION,
        parser_format_version: COMPILED_UNIT_PARSER_FORMAT_VERSION,
        unit_index: unit_idx,
        origin: unit.origin,
        realms,
        bands,
        files,
        dependencies,
        source_hash,
        syntax_hash,
        interface_hash,
    }
}

fn compiled_unit_realm_band_identities(
    unit: &SourceCompilationUnit,
    source_set: &SourceSet,
) -> (Vec<ResolvedRealmId>, Vec<ResolvedBandId>) {
    let mut realms = Vec::new();
    let mut bands = Vec::new();
    for &file_idx in &unit.files {
        let Some(band) = &source_set.files[file_idx].band else {
            continue;
        };
        realms.push(band.realm.clone());
        bands.push(band.clone());
    }
    realms.sort_by_key(resolved_realm_sort_key);
    realms.dedup();
    bands.sort_by_key(resolved_band_sort_key);
    bands.dedup();
    (realms, bands)
}

fn resolved_realm_sort_key(realm: &ResolvedRealmId) -> String {
    match &realm.version {
        Some(version) => format!("{}@{}", realm.identity.0, version.0),
        None => realm.identity.0.clone(),
    }
}

fn resolved_band_sort_key(band: &ResolvedBandId) -> String {
    let band_path = band
        .band
        .segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::");
    format!("{}/{}", resolved_realm_sort_key(&band.realm), band_path)
}

fn compiled_syntax_surface(
    unit: &SourceCompilationUnit,
    source_files: &[SourceFile],
    public_exports: &[HashMap<Name, OpDef>],
) -> CompiledSyntaxSurface {
    let mut modules = unit
        .files
        .iter()
        .map(|&file_idx| {
            let direct_exports = source_files[file_idx]
                .meta
                .syntax_exports
                .iter()
                .map(compiled_syntax_export)
                .collect::<Vec<_>>();
            let mut public_exports = public_exports[file_idx]
                .iter()
                .map(|(name, op)| CompiledSyntaxExport {
                    visibility: Visibility::Pub,
                    name: name.clone(),
                    op: CompiledOperatorSyntax::from_op_def(op),
                })
                .collect::<Vec<_>>();
            let mut direct_exports = direct_exports;
            sort_compiled_exports(&mut direct_exports);
            sort_compiled_exports(&mut public_exports);
            CompiledModuleSyntaxSurface {
                module_path: source_files[file_idx].module_path.clone(),
                direct_exports,
                public_exports,
            }
        })
        .collect::<Vec<_>>();
    modules.sort_by(|left, right| left.module_path.segments.cmp(&right.module_path.segments));

    let mut direct_exports = Vec::new();
    for &file_idx in &unit.files {
        direct_exports.extend(
            source_files[file_idx]
                .meta
                .syntax_exports
                .iter()
                .map(compiled_syntax_export),
        );
    }
    sort_compiled_exports(&mut direct_exports);

    let mut public_unit_table = HashMap::new();
    for &file_idx in &unit.files {
        for (name, op) in &public_exports[file_idx] {
            insert_export_op_def(&mut public_unit_table, name.clone(), op.clone());
        }
    }
    let mut public_unit_exports = public_unit_table
        .into_iter()
        .map(|(name, op)| CompiledSyntaxExport {
            visibility: Visibility::Pub,
            name,
            op: CompiledOperatorSyntax::from_op_def(&op),
        })
        .collect::<Vec<_>>();
    sort_compiled_exports(&mut public_unit_exports);

    CompiledSyntaxSurface {
        modules,
        direct_exports,
        public_exports: public_unit_exports,
    }
}

fn compiled_syntax_export(export: &SyntaxExport) -> CompiledSyntaxExport {
    CompiledSyntaxExport {
        visibility: export.visibility,
        name: export.name.clone(),
        op: CompiledOperatorSyntax::from_op_def(&export.op),
    }
}

fn sort_compiled_exports(exports: &mut [CompiledSyntaxExport]) {
    exports.sort_by(|left, right| {
        left.name.cmp(&right.name).then_with(|| {
            compiled_operator_sort_key(&left.op).cmp(&compiled_operator_sort_key(&right.op))
        })
    });
}

fn compiled_exports_op_table<'a>(
    exports: impl IntoIterator<Item = &'a CompiledSyntaxExport>,
) -> OpTable {
    let mut table = OpTable::new();
    for export in exports {
        insert_table_op_def(&mut table.0, export.name.clone(), export.op.to_op_def());
    }
    table
}

fn compiled_public_syntax_exports_by_module(
    artifacts: &[CompiledUnitSyntaxArtifact],
) -> Vec<(ModulePath, Vec<CompiledSyntaxExport>)> {
    let mut modules = Vec::new();
    for artifact in artifacts {
        for module in &artifact.syntax.modules {
            modules.push((module.module_path.clone(), module.public_exports.clone()));
        }
    }
    modules.sort_by(|left, right| left.0.segments.cmp(&right.0.segments));
    modules
}

fn imported_compiled_syntax_exports(
    import: &UseImport,
    public_exports: &[(ModulePath, Vec<CompiledSyntaxExport>)],
) -> Vec<CompiledSyntaxExport> {
    match import {
        UseImport::Alias { name, path, .. } => {
            let Some((module_path, imported_name)) =
                path.segments.split_last().map(|(last, prefix)| {
                    (
                        ModulePath {
                            segments: prefix.to_vec(),
                        },
                        last.clone(),
                    )
                })
            else {
                return Vec::new();
            };
            public_exports
                .iter()
                .find(|(candidate, _)| candidate == &module_path)
                .and_then(|(_, exports)| exports.iter().find(|export| export.name == imported_name))
                .cloned()
                .map(|mut export| {
                    export.name = name.clone();
                    export
                })
                .into_iter()
                .collect()
        }
        UseImport::Glob {
            prefix, excluded, ..
        } => public_exports
            .iter()
            .find(|(candidate, _)| candidate == prefix)
            .map(|(_, exports)| {
                exports
                    .iter()
                    .filter(|export| !excluded.contains(&export.name))
                    .cloned()
                    .collect()
            })
            .unwrap_or_default(),
    }
}

fn compiled_bp_vec(bp: &BpVec) -> Vec<i8> {
    bp.0.iter().copied().collect()
}

fn runtime_bp_vec(bp: &[i8]) -> BpVec {
    BpVec::new(bp.to_vec())
}

fn compiled_unit_source_hash(
    unit_idx: usize,
    unit: &SourceCompilationUnit,
    source_files: &[SourceFile],
    public_exports: &[HashMap<Name, OpDef>],
) -> u64 {
    let mut hash = StableHash::new();
    hash.write_u64(unit_idx as u64);
    hash.write_str(source_unit_origin_tag(unit.origin));
    for &file_idx in &unit.files {
        let file = &source_files[file_idx];
        hash.write_str(&file.path.to_string_lossy());
        hash.write_path(&file.module_path);
        hash.write_str(source_origin_tag(file.origin));
        hash.write_u64(file.source.len() as u64);
        hash.write_u64(stable_hash_bytes(file.source.as_bytes()));
    }
    for export in &compiled_syntax_surface(unit, source_files, public_exports).public_exports {
        hash.write_compiled_export(export);
    }
    hash.finish()
}

fn compiled_unit_interface_hash(
    unit: &SourceCompilationUnit,
    source_files: &[SourceFile],
    public_exports: &[HashMap<Name, OpDef>],
) -> u64 {
    stable_hash_compiled_exports(
        &compiled_syntax_surface(unit, source_files, public_exports).public_exports,
    )
}

fn stable_hash_bytes(bytes: &[u8]) -> u64 {
    let mut hash = StableHash::new();
    hash.write_bytes(bytes);
    hash.finish()
}

fn stable_hash_compiled_exports(exports: &[CompiledSyntaxExport]) -> u64 {
    let mut hash = StableHash::new();
    for export in exports {
        hash.write_compiled_export(export);
    }
    hash.finish()
}

fn compiled_operator_sort_key(op: &CompiledOperatorSyntax) -> String {
    format!(
        "p={:?};i={:?};s={:?};n={}",
        op.prefix, op.infix, op.suffix, op.nullfix
    )
}

fn source_origin_tag(origin: SourceOrigin) -> &'static str {
    match origin {
        SourceOrigin::Entry => "entry",
        SourceOrigin::Std => "std",
        SourceOrigin::User => "user",
    }
}

fn source_unit_origin_tag(origin: SourceCompilationUnitOrigin) -> &'static str {
    match origin {
        SourceCompilationUnitOrigin::Entry => "entry",
        SourceCompilationUnitOrigin::Std => "std",
        SourceCompilationUnitOrigin::User => "user",
        SourceCompilationUnitOrigin::Mixed => "mixed",
    }
}

struct StableHash {
    value: u64,
}

impl StableHash {
    fn new() -> Self {
        Self {
            value: 0xcbf29ce484222325,
        }
    }

    fn write_bytes(&mut self, bytes: &[u8]) {
        self.write_u64(bytes.len() as u64);
        self.write_raw_bytes(bytes);
    }

    fn write_raw_bytes(&mut self, bytes: &[u8]) {
        for byte in bytes {
            self.value ^= u64::from(*byte);
            self.value = self.value.wrapping_mul(0x100000001b3);
        }
    }

    fn write_u64(&mut self, value: u64) {
        self.write_raw_bytes(&value.to_le_bytes());
    }

    fn write_str(&mut self, value: &str) {
        self.write_bytes(value.as_bytes());
    }

    fn write_path(&mut self, path: &ModulePath) {
        self.write_u64(path.segments.len() as u64);
        for segment in &path.segments {
            self.write_str(&segment.0);
        }
    }

    fn write_compiled_export(&mut self, export: &CompiledSyntaxExport) {
        self.write_str(visibility_tag(export.visibility));
        self.write_str(&export.name.0);
        self.write_operator(&export.op);
    }

    fn write_operator(&mut self, op: &CompiledOperatorSyntax) {
        self.write_optional_bp(op.prefix.as_deref());
        if let Some((left, right)) = &op.infix {
            self.write_str("some-infix");
            self.write_bp(left);
            self.write_bp(right);
        } else {
            self.write_str("none-infix");
        }
        self.write_optional_bp(op.suffix.as_deref());
        self.write_str(if op.nullfix { "nullfix" } else { "no-nullfix" });
    }

    fn write_optional_bp(&mut self, bp: Option<&[i8]>) {
        if let Some(bp) = bp {
            self.write_str("some-bp");
            self.write_bp(bp);
        } else {
            self.write_str("none-bp");
        }
    }

    fn write_bp(&mut self, bp: &[i8]) {
        self.write_u64(bp.len() as u64);
        for value in bp {
            self.write_bytes(&value.to_le_bytes());
        }
    }

    fn finish(self) -> u64 {
        self.value
    }
}

fn visibility_tag(visibility: Visibility) -> &'static str {
    match visibility {
        Visibility::Pub => "pub",
        Visibility::Our => "our",
        Visibility::My => "my",
    }
}

fn import_module_path(import: &UseImport) -> Option<ModulePath> {
    match import {
        UseImport::Alias { path, .. } => {
            let (_, prefix) = path.segments.split_last()?;
            if prefix.is_empty() {
                None
            } else {
                Some(ModulePath {
                    segments: prefix.to_vec(),
                })
            }
        }
        UseImport::Glob { prefix, .. } if prefix.segments.is_empty() => None,
        UseImport::Glob { prefix, .. } => Some(prefix.clone()),
    }
}

fn inline_dependencies(module_path: &ModulePath, meta: &SourceMeta) -> Vec<ModulePath> {
    let mut deps = meta
        .module_files
        .iter()
        .map(|decl| {
            let mut child = module_path.segments.clone();
            child.push(decl.name.clone());
            ModulePath { segments: child }
        })
        .chain(
            meta.uses
                .iter()
                .filter_map(|use_| import_module_path(&use_.import)),
        )
        .collect::<Vec<_>>();
    deps.sort_by(|left, right| left.segments.cmp(&right.segments));
    deps.dedup();
    deps
}

fn push_best_module_dependency(
    path: &ModulePath,
    current_idx: usize,
    files: &[SourceFile],
    deps: &mut Vec<usize>,
) {
    let current = &files[current_idx];
    let Some((idx, _)) = files
        .iter()
        .enumerate()
        .filter(|(idx, candidate)| {
            *idx != current_idx
                && !candidate.module_path.segments.is_empty()
                && import_can_target_realm(path, current, candidate)
                && is_prefix(&candidate.module_path.segments, &path.segments)
        })
        .max_by_key(|(_, candidate)| candidate.module_path.segments.len())
    else {
        return;
    };
    deps.push(idx);
}

fn push_module_dependency(
    path: &[Name],
    current_idx: usize,
    files: &[SourceFile],
    deps: &mut Vec<usize>,
) {
    let current = &files[current_idx];
    if let Some((idx, _)) = files.iter().enumerate().find(|(idx, candidate)| {
        *idx != current_idx
            && candidate.realm == current.realm
            && candidate.module_path.segments == path
    }) {
        deps.push(idx);
    }
}

fn import_can_target_realm(
    path: &ModulePath,
    current: &SourceFile,
    candidate: &SourceFile,
) -> bool {
    if candidate.realm == current.realm {
        return true;
    }
    let prefix_len = realm_identity_prefix_len(&candidate.realm.identity, path);
    prefix_len == Some(candidate.realm_path_prefix_len)
}

fn is_prefix(prefix: &[Name], path: &[Name]) -> bool {
    prefix.len() <= path.len() && prefix.iter().zip(path).all(|(a, b)| a == b)
}

fn visit_source_file(
    idx: usize,
    dependencies: &[Vec<usize>],
    marks: &mut [VisitMark],
    order: &mut Vec<usize>,
) {
    match marks[idx] {
        VisitMark::Done => return,
        VisitMark::Visiting => return,
        VisitMark::Unvisited => {}
    }
    marks[idx] = VisitMark::Visiting;
    for &dep in &dependencies[idx] {
        visit_source_file(dep, dependencies, marks, order);
    }
    marks[idx] = VisitMark::Done;
    order.push(idx);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum VisitMark {
    Unvisited,
    Visiting,
    Done,
}

fn build_syntax_tables(files: &mut [SourceFile]) {
    let module_paths = files
        .iter()
        .map(|file| file.module_path.clone())
        .collect::<Vec<_>>();
    let public_exports = source_public_syntax_exports(files);

    for idx in 0..files.len() {
        let mut table = standard_op_table();
        for export in &files[idx].meta.syntax_exports {
            insert_table_op_def(&mut table.0, export.name.clone(), export.op.clone());
        }
        for use_ in &files[idx].meta.uses {
            let imported = imported_syntax_exports(&use_.import, &module_paths, &public_exports);
            for (name, op) in imported {
                insert_table_op_def(&mut table.0, name, op);
            }
        }
        files[idx].op_table = table;
    }
}

fn local_public_syntax_exports(meta: &SourceMeta) -> HashMap<Name, OpDef> {
    let mut exports = HashMap::new();
    for export in &meta.syntax_exports {
        if export.visibility != Visibility::My {
            insert_export_op_def(&mut exports, export.name.clone(), export.op.clone());
        }
    }
    exports
}

fn imported_syntax_exports(
    import: &UseImport,
    module_paths: &[ModulePath],
    public_exports: &[HashMap<Name, OpDef>],
) -> Vec<(Name, OpDef)> {
    match import {
        UseImport::Alias { name, path, .. } => {
            let Some((module_path, imported_name)) =
                path.segments.split_last().map(|(last, prefix)| {
                    (
                        ModulePath {
                            segments: prefix.to_vec(),
                        },
                        last.clone(),
                    )
                })
            else {
                return Vec::new();
            };
            let Some(idx) = module_index(&module_path, module_paths) else {
                return Vec::new();
            };
            public_exports[idx]
                .get(&imported_name)
                .cloned()
                .map(|op| vec![(name.clone(), op)])
                .unwrap_or_default()
        }
        UseImport::Glob {
            prefix, excluded, ..
        } => {
            let Some(idx) = module_index(prefix, module_paths) else {
                return Vec::new();
            };
            public_exports[idx]
                .iter()
                .filter(|(name, _)| !excluded.contains(name))
                .map(|(name, op)| (name.clone(), op.clone()))
                .collect()
        }
    }
}

fn module_index(path: &ModulePath, module_paths: &[ModulePath]) -> Option<usize> {
    module_paths.iter().position(|candidate| candidate == path)
}

fn insert_export_op_def(table: &mut HashMap<Name, OpDef>, name: Name, op: OpDef) -> bool {
    match table.get(&name) {
        Some(existing) => {
            let merged = merge_op_defs(existing.clone(), op);
            if existing == &merged {
                false
            } else {
                table.insert(name, merged);
                true
            }
        }
        None => {
            table.insert(name, op);
            true
        }
    }
}

fn insert_table_op_def(table: &mut yulang_parser::op::trie::Trie<OpDef>, name: Name, op: OpDef) {
    let key = name.0;
    let merged = table
        .get(key.as_bytes())
        .cloned()
        .map(|existing| merge_op_defs(existing, op.clone()))
        .unwrap_or(op);
    table.insert(key.into(), merged);
}

fn merge_op_defs(mut lhs: OpDef, rhs: OpDef) -> OpDef {
    lhs.prefix = rhs.prefix.or(lhs.prefix);
    lhs.infix = rhs.infix.or(lhs.infix);
    lhs.suffix = rhs.suffix.or(lhs.suffix);
    lhs.nullfix = lhs.nullfix || rhs.nullfix;
    lhs
}

fn module_file_decl(node: &SyntaxNode<YulangLanguage>) -> Option<ModuleFileDecl> {
    if node.kind() != SyntaxKind::ModDecl || !has_direct_token(node, SyntaxKind::Semicolon) {
        return None;
    }
    let name = direct_token_text(node, SyntaxKind::Ident).map(Name)?;
    Some(ModuleFileDecl {
        visibility: lower_visibility(node),
        name,
    })
}

fn use_mod_module_file_decl(node: &SyntaxNode<YulangLanguage>) -> Option<ModuleFileDecl> {
    if node.kind() != SyntaxKind::UseDecl || !has_direct_token(node, SyntaxKind::Mod) {
        return None;
    }
    let name = direct_token_text(node, SyntaxKind::Ident).map(Name)?;
    Some(ModuleFileDecl {
        visibility: lower_visibility(node),
        name,
    })
}

fn syntax_export(node: &SyntaxNode<YulangLanguage>) -> Option<SyntaxExport> {
    if node.kind() != SyntaxKind::OpDef {
        return None;
    }
    let header = node
        .children()
        .find(|child| child.kind() == SyntaxKind::OpDefHeader)?;
    let name = direct_token_text(&header, SyntaxKind::OpName).map(Name)?;
    let fixity = header.children_with_tokens().find_map(|item| match item {
        NodeOrToken::Token(tok)
            if matches!(
                tok.kind(),
                SyntaxKind::Prefix | SyntaxKind::Infix | SyntaxKind::Suffix | SyntaxKind::Nullfix
            ) =>
        {
            Some(tok.kind())
        }
        _ => None,
    })?;
    let bps = header
        .children_with_tokens()
        .filter_map(|item| match item {
            NodeOrToken::Token(tok) if tok.kind() == SyntaxKind::Number => BpVec::parse(tok.text()),
            _ => None,
        })
        .collect::<Vec<_>>();
    Some(SyntaxExport {
        visibility: lower_visibility(node),
        name,
        op: op_def_from_header(fixity, &bps),
    })
}

fn op_def_from_header(fixity: SyntaxKind, bps: &[BpVec]) -> OpDef {
    match fixity {
        SyntaxKind::Prefix => OpDef {
            prefix: bps.first().cloned(),
            ..OpDef::default()
        },
        SyntaxKind::Infix => OpDef {
            infix: bps.first().cloned().zip(bps.get(1).cloned()),
            ..OpDef::default()
        },
        SyntaxKind::Suffix => OpDef {
            suffix: bps.first().cloned(),
            ..OpDef::default()
        },
        SyntaxKind::Nullfix => OpDef {
            nullfix: true,
            ..OpDef::default()
        },
        _ => OpDef::default(),
    }
}

fn use_decl_imports(node: &SyntaxNode<YulangLanguage>) -> Vec<UseImport> {
    let mut path = Vec::new();
    let mut after_as = false;
    let mut alias = None;
    let mut imports = Vec::new();
    let mut excluding_glob = None;
    let mut default_realm_version = None;
    let with_anchor = use_with_anchor(node);

    for item in node.children_with_tokens() {
        match item {
            NodeOrToken::Token(tok) => match tok.kind() {
                SyntaxKind::Pub
                | SyntaxKind::Our
                | SyntaxKind::My
                | SyntaxKind::Use
                | SyntaxKind::Mod => {}
                SyntaxKind::ColonColon | SyntaxKind::Slash => {}
                SyntaxKind::Ident if tok.text() == "with" => break,
                SyntaxKind::Ident if use_realm_version(tok.text()).is_some() => {
                    default_realm_version = use_realm_version(tok.text());
                }
                SyntaxKind::Ident if tok.text() == "without" => {
                    excluding_glob = imports.len().checked_sub(1);
                    path.clear();
                    alias = None;
                    after_as = false;
                }
                SyntaxKind::Ident if excluding_glob.is_some() => {
                    push_use_glob_exclusion(
                        &mut imports,
                        excluding_glob,
                        Name(tok.text().to_string()),
                    );
                }
                SyntaxKind::Ident if after_as => {
                    alias = Some(Name(tok.text().to_string()));
                    after_as = false;
                }
                SyntaxKind::Ident => path.push(Name(tok.text().to_string())),
                SyntaxKind::As => after_as = true,
                SyntaxKind::OpName if tok.text() == "*" => {
                    imports.push(UseImport::Glob {
                        prefix: ModulePath {
                            segments: path.clone(),
                        },
                        excluded: Vec::new(),
                        realm_version: None,
                        with_anchor: None,
                    });
                    path.clear();
                    alias = None;
                    after_as = false;
                }
                SyntaxKind::OpName if excluding_glob.is_some() => {
                    push_use_glob_exclusion(
                        &mut imports,
                        excluding_glob,
                        Name(tok.text().to_string()),
                    );
                }
                SyntaxKind::OpName => path.push(Name(tok.text().to_string())),
                SyntaxKind::ParenL | SyntaxKind::ParenR => {}
                _ => {}
            },
            NodeOrToken::Node(child) if child.kind() == SyntaxKind::BraceGroup => {
                if excluding_glob.is_some() {
                    collect_use_glob_exclusions(&child, &mut imports, excluding_glob);
                } else {
                    collect_use_group_imports(&child, &path, &mut imports);
                    path.clear();
                    alias = None;
                    after_as = false;
                }
            }
            _ => {}
        }
    }

    push_use_alias_import(path, alias, None, &mut imports);
    apply_use_realm_version_default(&mut imports, default_realm_version);
    apply_use_with_anchor(&mut imports, with_anchor);
    imports
}

fn collect_use_group_imports(
    node: &SyntaxNode<YulangLanguage>,
    base: &[Name],
    imports: &mut Vec<UseImport>,
) {
    let mut path = base.to_vec();
    let mut alias = None;
    let mut after_as = false;
    let mut consumed_nested = false;
    let mut excluding_glob = None;
    let mut item_realm_version = None;
    let mut last_item_import_idx = None;

    for item in node.children_with_tokens() {
        match item {
            NodeOrToken::Token(tok) => match tok.kind() {
                SyntaxKind::BraceL => {}
                SyntaxKind::BraceR => {
                    if !consumed_nested {
                        push_use_alias_import(
                            path,
                            alias.take(),
                            item_realm_version.take(),
                            imports,
                        );
                    }
                    return;
                }
                SyntaxKind::Comma => {
                    if !consumed_nested {
                        push_use_alias_import(
                            path,
                            alias.take(),
                            item_realm_version.take(),
                            imports,
                        );
                    }
                    path = base.to_vec();
                    after_as = false;
                    consumed_nested = false;
                    item_realm_version = None;
                    last_item_import_idx = None;
                }
                SyntaxKind::ColonColon | SyntaxKind::Slash => {}
                SyntaxKind::Ident if tok.text() == "without" => {
                    excluding_glob = imports.len().checked_sub(1);
                    path = base.to_vec();
                    alias = None;
                    after_as = false;
                    consumed_nested = true;
                    item_realm_version = None;
                    last_item_import_idx = excluding_glob;
                }
                SyntaxKind::Ident if use_realm_version(tok.text()).is_some() => {
                    let version = use_realm_version(tok.text());
                    if let (Some(idx), Some(version)) = (last_item_import_idx, version.clone()) {
                        set_use_import_realm_version(imports, idx, version);
                    } else {
                        item_realm_version = version;
                    }
                }
                SyntaxKind::Ident if excluding_glob.is_some() => {
                    push_use_glob_exclusion(
                        &mut *imports,
                        excluding_glob,
                        Name(tok.text().to_string()),
                    );
                    consumed_nested = true;
                }
                SyntaxKind::Ident if after_as => {
                    alias = Some(Name(tok.text().to_string()));
                    after_as = false;
                }
                SyntaxKind::Ident => path.push(Name(tok.text().to_string())),
                SyntaxKind::As => after_as = true,
                SyntaxKind::OpName if tok.text() == "*" => {
                    imports.push(UseImport::Glob {
                        prefix: ModulePath {
                            segments: path.clone(),
                        },
                        excluded: Vec::new(),
                        realm_version: None,
                        with_anchor: None,
                    });
                    last_item_import_idx = imports.len().checked_sub(1);
                    path = base.to_vec();
                    alias = None;
                    after_as = false;
                    consumed_nested = true;
                    item_realm_version = None;
                }
                SyntaxKind::OpName if excluding_glob.is_some() => {
                    push_use_glob_exclusion(
                        &mut *imports,
                        excluding_glob,
                        Name(tok.text().to_string()),
                    );
                    consumed_nested = true;
                }
                SyntaxKind::OpName => path.push(Name(tok.text().to_string())),
                SyntaxKind::ParenL | SyntaxKind::ParenR => {}
                _ => {}
            },
            NodeOrToken::Node(child) if child.kind() == SyntaxKind::BraceGroup => {
                if excluding_glob.is_some() {
                    collect_use_glob_exclusions(&child, imports, excluding_glob);
                } else {
                    collect_use_group_imports(&child, &path, imports);
                }
                path = base.to_vec();
                alias = None;
                after_as = false;
                consumed_nested = true;
                item_realm_version = None;
                last_item_import_idx = imports.len().checked_sub(1);
            }
            NodeOrToken::Node(child) if child.kind() == SyntaxKind::Separator => {
                if !consumed_nested {
                    push_use_alias_import(path, alias.take(), item_realm_version.take(), imports);
                }
                path = base.to_vec();
                after_as = false;
                consumed_nested = false;
                item_realm_version = None;
                last_item_import_idx = None;
            }
            _ => {}
        }
    }

    if !consumed_nested {
        push_use_alias_import(path, alias, item_realm_version, imports);
    }
}

fn collect_use_glob_exclusions(
    node: &SyntaxNode<YulangLanguage>,
    imports: &mut Vec<UseImport>,
    glob_idx: Option<usize>,
) {
    for item in node.children_with_tokens() {
        match item {
            NodeOrToken::Token(tok) => match tok.kind() {
                SyntaxKind::Ident => {
                    push_use_glob_exclusion(imports, glob_idx, Name(tok.text().to_string()));
                }
                SyntaxKind::OpName if tok.text() != "*" => {
                    push_use_glob_exclusion(imports, glob_idx, Name(tok.text().to_string()));
                }
                _ => {}
            },
            NodeOrToken::Node(child) if child.kind() == SyntaxKind::BraceGroup => {
                collect_use_glob_exclusions(&child, imports, glob_idx);
            }
            _ => {}
        }
    }
}

fn push_use_glob_exclusion(imports: &mut [UseImport], glob_idx: Option<usize>, name: Name) {
    let Some(idx) = glob_idx else {
        return;
    };
    let Some(UseImport::Glob { excluded, .. }) = imports.get_mut(idx) else {
        return;
    };
    if !excluded.contains(&name) {
        excluded.push(name);
    }
}

fn set_use_import_realm_version(imports: &mut [UseImport], idx: usize, version: RealmVersion) {
    let Some(import) = imports.get_mut(idx) else {
        return;
    };
    match import {
        UseImport::Alias { realm_version, .. } | UseImport::Glob { realm_version, .. } => {
            *realm_version = Some(version);
        }
    }
}

fn apply_use_realm_version_default(
    imports: &mut [UseImport],
    default_realm_version: Option<RealmVersion>,
) {
    let Some(default_realm_version) = default_realm_version else {
        return;
    };
    for import in imports {
        match import {
            UseImport::Alias { realm_version, .. } | UseImport::Glob { realm_version, .. } => {
                if realm_version.is_none() {
                    *realm_version = Some(default_realm_version.clone());
                }
            }
        }
    }
}

fn push_use_alias_import(
    path: Vec<Name>,
    alias: Option<Name>,
    realm_version: Option<RealmVersion>,
    imports: &mut Vec<UseImport>,
) {
    if path.is_empty() {
        return;
    }
    let Some(name) = alias.or_else(|| path.last().cloned()) else {
        return;
    };
    imports.push(UseImport::Alias {
        name,
        path: ModulePath { segments: path },
        realm_version,
        with_anchor: None,
    });
}

fn use_realm_version(text: &str) -> Option<RealmVersion> {
    let version = text.strip_prefix('v')?;
    if version.is_empty() || !version.chars().next().is_some_and(|c| c.is_ascii_digit()) {
        return None;
    }
    Some(RealmVersion(version.to_string()))
}

fn apply_use_with_anchor(imports: &mut [UseImport], with_anchor: Option<ModulePath>) {
    let Some(anchor) = with_anchor else {
        return;
    };
    for import in imports {
        match import {
            UseImport::Alias { with_anchor, .. } | UseImport::Glob { with_anchor, .. } => {
                *with_anchor = Some(anchor.clone());
            }
        }
    }
}

fn use_with_anchor(node: &SyntaxNode<YulangLanguage>) -> Option<ModulePath> {
    let mut after_with = false;
    let mut segments = Vec::new();

    for item in node.children_with_tokens() {
        let NodeOrToken::Token(tok) = item else {
            continue;
        };
        match tok.kind() {
            SyntaxKind::Ident if tok.text() == "with" => {
                after_with = true;
            }
            SyntaxKind::Ident if after_with => {
                segments.push(Name(tok.text().to_string()));
            }
            SyntaxKind::ColonColon | SyntaxKind::Slash if after_with => {}
            _ if after_with && !segments.is_empty() => break,
            _ => {}
        }
    }

    (!segments.is_empty()).then_some(ModulePath { segments })
}

fn lower_visibility(node: &SyntaxNode<YulangLanguage>) -> Visibility {
    if let Some(visibility) = direct_visibility(node) {
        return visibility;
    }
    if matches!(node.kind(), SyntaxKind::OpDef) {
        for child in node.children() {
            if child.kind() == SyntaxKind::OpDefHeader {
                if let Some(visibility) = direct_visibility(&child) {
                    return visibility;
                }
            }
        }
    }
    Visibility::My
}

fn direct_visibility(node: &SyntaxNode<YulangLanguage>) -> Option<Visibility> {
    for item in node.children_with_tokens() {
        if let NodeOrToken::Token(tok) = item {
            match tok.kind() {
                SyntaxKind::Pub => return Some(Visibility::Pub),
                SyntaxKind::Our => return Some(Visibility::Our),
                SyntaxKind::My => return Some(Visibility::My),
                _ => {}
            }
        }
    }
    None
}

fn resolve_module_file(current: &FsPath, name: &Name) -> Result<PathBuf, SourceLoadError> {
    let parent = current.parent().unwrap_or_else(|| FsPath::new("."));
    let direct = parent.join(format!("{}.yu", name.0));
    let stem_child = current.with_extension("").join(format!("{}.yu", name.0));
    let mut candidates = Vec::new();
    if direct.is_file() {
        candidates.push(direct);
    }
    if stem_child.is_file() {
        candidates.push(stem_child);
    }
    match candidates.len() {
        1 => return Ok(candidates.remove(0)),
        len if len > 1 => {
            return Err(SourceLoadError::AmbiguousModuleFile {
                current: current.to_path_buf(),
                name: name.clone(),
                candidates,
            });
        }
        _ => {}
    }
    Err(SourceLoadError::ModuleNotFound {
        parent: parent.to_path_buf(),
        name: name.clone(),
    })
}

fn resolve_module_path_under_root(root: &FsPath, module_path: &[Name]) -> Option<PathBuf> {
    if module_path.is_empty() {
        let nested = root.join("mod.yu");
        return nested.is_file().then_some(nested);
    }

    let mut base = root.to_path_buf();
    for segment in &module_path[..module_path.len() - 1] {
        base.push(&segment.0);
    }
    let last = &module_path[module_path.len() - 1];
    let direct = base.join(format!("{}.yu", last.0));
    if direct.is_file() {
        return Some(direct);
    }
    let nested = base.join(&last.0).join("mod.yu");
    nested.is_file().then_some(nested)
}

fn canonicalize_for_dedupe(path: &FsPath) -> PathBuf {
    path.canonicalize().unwrap_or_else(|_| path.to_path_buf())
}

fn has_direct_token(node: &SyntaxNode<YulangLanguage>, kind: SyntaxKind) -> bool {
    node.children_with_tokens()
        .any(|item| matches!(item, NodeOrToken::Token(tok) if tok.kind() == kind))
}

fn direct_token_text(node: &SyntaxNode<YulangLanguage>, kind: SyntaxKind) -> Option<String> {
    node.children_with_tokens().find_map(|item| match item {
        NodeOrToken::Token(tok) if tok.kind() == kind => Some(tok.text().to_string()),
        _ => None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn names(path: &ModulePath) -> Vec<&str> {
        path.segments.iter().map(|name| name.0.as_str()).collect()
    }

    fn temp_root(name: &str) -> PathBuf {
        std::env::temp_dir().join(format!(
            "yulang-sources-{name}-{}",
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ))
    }

    fn module_path(segments: &[&str]) -> ModulePath {
        ModulePath {
            segments: segments
                .iter()
                .map(|segment| Name((*segment).to_string()))
                .collect(),
        }
    }

    #[test]
    fn inline_sources_keep_entry_and_std_origins() {
        let set = collect_inline_source_files_with_options(
            "1",
            [InlineSource {
                path: PathBuf::from("<std>/prelude.yu"),
                module_path: module_path(&["std", "prelude"]),
                origin: SourceOrigin::Std,
                source: String::new(),
                meta: None,
            }],
            SourceOptions {
                std_root: None,
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        );

        assert_eq!(set.entry_files().count(), 1);
        assert_eq!(set.std_files().count(), 1);
        assert_eq!(set.user_files().count(), 0);
    }

    #[test]
    fn parses_leading_mod_file_and_use_metadata() {
        let meta =
            parse_source_meta("pub mod list;\nuse list::{List, map as list_map}\nmy x = list_map");

        assert_eq!(
            meta.module_files,
            vec![ModuleFileDecl {
                visibility: Visibility::Pub,
                name: Name("list".to_string()),
            }]
        );
        assert_eq!(meta.uses.len(), 2);
        let UseImport::Alias { name, path, .. } = &meta.uses[0].import else {
            panic!("expected alias import");
        };
        assert_eq!(name.0, "List");
        assert_eq!(names(path), vec!["list", "List"]);
        let UseImport::Alias { name, path, .. } = &meta.uses[1].import else {
            panic!("expected alias import");
        };
        assert_eq!(name.0, "list_map");
        assert_eq!(names(path), vec!["list", "map"]);
    }

    #[test]
    fn parses_use_mod_as_module_file_and_use_metadata() {
        let meta = parse_source_meta("use mod math::*\nmy x = answer");

        assert_eq!(
            meta.module_files,
            vec![ModuleFileDecl {
                visibility: Visibility::My,
                name: Name("math".to_string()),
            }]
        );
        assert_eq!(meta.uses.len(), 1);
        let UseImport::Glob {
            prefix, excluded, ..
        } = &meta.uses[0].import
        else {
            panic!("expected glob import");
        };
        assert_eq!(names(prefix), vec!["math"]);
        assert!(excluded.is_empty());
    }

    #[test]
    fn parses_use_with_anchor_metadata() {
        let meta = parse_source_meta("use ui/widget::a with program::ui\nmy x = a");

        assert_eq!(meta.uses.len(), 1);
        let UseImport::Alias {
            name,
            path,
            with_anchor,
            ..
        } = &meta.uses[0].import
        else {
            panic!("expected alias import");
        };
        assert_eq!(name.0, "a");
        assert_eq!(names(path), vec!["ui", "widget", "a"]);
        assert_eq!(with_anchor.as_ref().map(names), Some(vec!["program", "ui"]));
    }

    #[test]
    fn parses_use_realm_version_metadata() {
        let meta = parse_source_meta("use yulang/std::prelude v0.1.3\nmy x = prelude");

        assert_eq!(meta.uses.len(), 1);
        let UseImport::Alias {
            name,
            path,
            realm_version,
            ..
        } = &meta.uses[0].import
        else {
            panic!("expected alias import");
        };
        assert_eq!(name.0, "prelude");
        assert_eq!(names(path), vec!["yulang", "std", "prelude"]);
        assert_eq!(realm_version, &Some(RealmVersion("0.1.3".to_string())));
    }

    #[test]
    fn parses_group_item_use_realm_version_metadata() {
        let meta = parse_source_meta("use user/{realm1 v1.3, realm2::a::b::c v1.4}\nmy x = c");

        assert_eq!(meta.uses.len(), 2);
        let UseImport::Alias {
            name,
            path,
            realm_version,
            ..
        } = &meta.uses[0].import
        else {
            panic!("expected alias import");
        };
        assert_eq!(name.0, "realm1");
        assert_eq!(names(path), vec!["user", "realm1"]);
        assert_eq!(realm_version, &Some(RealmVersion("1.3".to_string())));

        let UseImport::Alias {
            name,
            path,
            realm_version,
            ..
        } = &meta.uses[1].import
        else {
            panic!("expected alias import");
        };
        assert_eq!(name.0, "c");
        assert_eq!(names(path), vec!["user", "realm2", "a", "b", "c"]);
        assert_eq!(realm_version, &Some(RealmVersion("1.4".to_string())));
    }

    #[test]
    fn parses_group_use_realm_version_default_metadata() {
        let meta = parse_source_meta(
            "use user/{realm1 v1.3, realm2::a, realm3::module::*} v1.0\nmy x = a",
        );

        assert_eq!(meta.uses.len(), 3);
        let UseImport::Alias {
            path,
            realm_version,
            ..
        } = &meta.uses[0].import
        else {
            panic!("expected alias import");
        };
        assert_eq!(names(path), vec!["user", "realm1"]);
        assert_eq!(realm_version, &Some(RealmVersion("1.3".to_string())));

        let UseImport::Alias {
            path,
            realm_version,
            ..
        } = &meta.uses[1].import
        else {
            panic!("expected alias import");
        };
        assert_eq!(names(path), vec!["user", "realm2", "a"]);
        assert_eq!(realm_version, &Some(RealmVersion("1.0".to_string())));

        let UseImport::Glob {
            prefix,
            realm_version,
            ..
        } = &meta.uses[2].import
        else {
            panic!("expected glob import");
        };
        assert_eq!(names(prefix), vec!["user", "realm3", "module"]);
        assert_eq!(realm_version, &Some(RealmVersion("1.0".to_string())));
    }

    #[test]
    fn local_realm_manifest_sets_realm_identity_and_dependencies() {
        let root = temp_root("realm-manifest");
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("realm.toml"),
            r#"[realm]
identity = "user/program"
version = "0.1.3"

[dependencies]
"ui/widget" = "^2.4"
"std" = "0.1.3"
"#,
        )
        .unwrap();
        fs::write(root.join("main.yu"), "my x = 1\n").unwrap();

        let set = collect_source_files_with_options(
            root.join("main.yu"),
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        )
        .unwrap();

        assert_eq!(
            set.realms[0].id,
            ResolvedRealmId {
                identity: RealmIdentity("user/program".to_string()),
                version: Some(RealmVersion("0.1.3".to_string())),
            }
        );
        assert_eq!(
            set.realms[0].dependencies,
            vec![
                SourceRealmDependency {
                    identity: RealmIdentity("std".to_string()),
                    requirement: "0.1.3".to_string(),
                },
                SourceRealmDependency {
                    identity: RealmIdentity("ui/widget".to_string()),
                    requirement: "^2.4".to_string(),
                },
            ]
        );
    }

    #[test]
    fn parses_operator_use_metadata() {
        let meta = parse_source_meta("use ops::{(+), id}\nmy x = 1");

        assert_eq!(meta.uses.len(), 2);
        let UseImport::Alias { name, path, .. } = &meta.uses[0].import else {
            panic!("expected operator alias import");
        };
        assert_eq!(name.0, "+");
        assert_eq!(names(path), vec!["ops", "+"]);
    }

    #[test]
    fn parses_glob_without_metadata() {
        let meta = parse_source_meta("use ops::* without (%%), id\nmy x = 1");

        assert_eq!(meta.uses.len(), 1);
        let UseImport::Glob {
            prefix, excluded, ..
        } = &meta.uses[0].import
        else {
            panic!("expected glob import");
        };
        assert_eq!(names(prefix), vec!["ops"]);
        assert_eq!(
            excluded
                .iter()
                .map(|name| name.0.as_str())
                .collect::<Vec<_>>(),
            vec!["%%", "id"]
        );
    }

    #[test]
    fn parses_leading_operator_export_metadata() {
        let meta = parse_source_meta("pub infix (%%) 50 51 = \\x -> \\y -> y\nmy x = 1");

        assert_eq!(meta.syntax_exports.len(), 1);
        let export = &meta.syntax_exports[0];
        assert_eq!(export.visibility, Visibility::Pub);
        assert_eq!(export.name.0, "%%");
        assert!(export.op.infix.is_some());
    }

    #[test]
    fn stops_metadata_after_first_ordinary_item() {
        let meta = parse_source_meta("my x = 1\nmod late;\nuse late::x");

        assert!(meta.module_files.is_empty());
        assert!(meta.uses.is_empty());
    }

    #[test]
    fn collects_module_files_recursively() {
        let root = temp_root("collects-module-files");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(root.join("list")).unwrap();
        fs::write(root.join("main.yu"), "mod list;\nmy x = 1").unwrap();
        fs::write(root.join("list.yu"), "mod inner;\nmy y = 2").unwrap();
        fs::write(root.join("list").join("inner.yu"), "my z = 3").unwrap();

        let set = collect_source_files(root.join("main.yu")).unwrap();
        let file_names = set
            .files
            .iter()
            .map(|file| file.path.file_name().unwrap().to_string_lossy().to_string())
            .collect::<Vec<_>>();
        assert_eq!(file_names, vec!["inner.yu", "list.yu", "main.yu"]);
        let module_paths = set
            .files
            .iter()
            .map(|file| names(&file.module_path))
            .collect::<Vec<_>>();
        assert_eq!(
            module_paths,
            vec![vec!["list", "inner"], vec!["list"], Vec::<&str>::new()]
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn mod_file_can_use_stem_child_layout() {
        let root = temp_root("stem-child-module-file");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(root.join("main")).unwrap();
        fs::write(root.join("main.yu"), "mod child;\nchild::x\n").unwrap();
        fs::write(root.join("main").join("child.yu"), "pub x = 1\n").unwrap();

        let set = collect_source_files(root.join("main.yu")).unwrap();
        let module_paths = set
            .files
            .iter()
            .map(|file| names(&file.module_path))
            .collect::<Vec<_>>();
        assert_eq!(module_paths, vec![vec!["child"], Vec::<&str>::new()]);

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn mod_file_reports_ambiguous_sibling_and_stem_child() {
        let root = temp_root("ambiguous-module-file");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(root.join("main")).unwrap();
        fs::write(root.join("main.yu"), "mod child;\nchild::x\n").unwrap();
        fs::write(root.join("child.yu"), "pub x = 1\n").unwrap();
        fs::write(root.join("main").join("child.yu"), "pub x = 2\n").unwrap();

        let err = collect_source_files(root.join("main.yu")).unwrap_err();
        assert!(matches!(
            err,
            SourceLoadError::AmbiguousModuleFile { name, .. } if name == Name("child".to_string())
        ));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn imported_operator_syntax_is_available_for_full_parse() {
        let root = temp_root("operator-syntax");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("main.yu"),
            "mod ops;\nuse ops::*\nmy y = 1 %% true\n",
        )
        .unwrap();
        fs::write(
            root.join("ops.yu"),
            "pub infix (%%) 50 51 = \\x -> \\y -> y\n",
        )
        .unwrap();

        let set = collect_source_files(root.join("main.yu")).unwrap();
        let main = set
            .files
            .iter()
            .find(|file| file.module_path.segments.is_empty())
            .unwrap();
        let parsed = SyntaxNode::<YulangLanguage>::new_root(
            yulang_parser::parse_module_to_green_with_ops(&main.source, main.op_table.clone()),
        );

        assert!(
            parsed
                .descendants()
                .any(|node| node.kind() == SyntaxKind::InfixNode)
        );
        assert!(parsed.descendants_with_tokens().any(|item| {
            matches!(
                item,
                NodeOrToken::Token(tok) if tok.kind() == SyntaxKind::Infix && tok.text() == "%%"
            )
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn reexported_operator_syntax_is_available_for_full_parse() {
        let root = temp_root("operator-syntax-reexport");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("main.yu"),
            "mod ops;\nmod prelude;\nuse prelude::*\nmy y = 1 %% true\n",
        )
        .unwrap();
        fs::write(
            root.join("ops.yu"),
            "pub infix (%%) 50 51 = \\x -> \\y -> y\n",
        )
        .unwrap();
        fs::write(root.join("prelude.yu"), "pub use ops::*\n").unwrap();

        let set = collect_source_files(root.join("main.yu")).unwrap();
        let main = set
            .files
            .iter()
            .find(|file| file.module_path.segments.is_empty())
            .unwrap();
        let parsed = SyntaxNode::<YulangLanguage>::new_root(
            yulang_parser::parse_module_to_green_with_ops(&main.source, main.op_table.clone()),
        );

        assert!(
            parsed
                .descendants()
                .any(|node| node.kind() == SyntaxKind::InfixNode)
        );
        assert!(parsed.descendants_with_tokens().any(|item| {
            matches!(
                item,
                NodeOrToken::Token(tok) if tok.kind() == SyntaxKind::Infix && tok.text() == "%%"
            )
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn implicit_prelude_loads_std_source_and_imports_it_into_entry() {
        let root = temp_root("implicit-prelude");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(root.join("std")).unwrap();
        fs::write(root.join("main.yu"), "my y = id 1\n").unwrap();
        fs::write(root.join("std").join("prelude.yu"), "pub id x = x\n").unwrap();

        let set = collect_source_files_with_options(
            root.join("main.yu"),
            SourceOptions {
                std_root: Some(root.join("std")),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let module_paths = set
            .files
            .iter()
            .map(|file| names(&file.module_path))
            .collect::<Vec<_>>();

        assert_eq!(
            module_paths,
            vec![vec!["std", "prelude"], Vec::<&str>::new()]
        );
        let main = set
            .files
            .iter()
            .find(|file| file.module_path.segments.is_empty())
            .unwrap();
        assert!(main.source.starts_with("use std::prelude::*\n"));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn implicit_prelude_operator_syntax_is_available_for_full_parse() {
        let root = temp_root("implicit-prelude-operator-syntax");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(root.join("std")).unwrap();
        fs::write(root.join("main.yu"), "my y = 1 %% fail true\n").unwrap();
        fs::write(
            root.join("std").join("prelude.yu"),
            "pub prefix(fail) 70 = \\x -> x\npub infix (%%) 50 51 = \\x -> \\y -> x\n",
        )
        .unwrap();

        let set = collect_source_files_with_options(
            root.join("main.yu"),
            SourceOptions {
                std_root: Some(root.join("std")),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let main = set
            .files
            .iter()
            .find(|file| file.module_path.segments.is_empty())
            .unwrap();
        let parsed = SyntaxNode::<YulangLanguage>::new_root(
            yulang_parser::parse_module_to_green_with_ops(&main.source, main.op_table.clone()),
        );

        assert!(parsed.descendants_with_tokens().any(|item| {
            matches!(
                item,
                NodeOrToken::Token(tok) if tok.kind() == SyntaxKind::Infix && tok.text() == "%%"
            )
        }));
        assert!(parsed.descendants_with_tokens().any(|item| {
            matches!(
                item,
                NodeOrToken::Token(tok) if tok.kind() == SyntaxKind::Prefix && tok.text() == "fail"
            )
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn explicit_std_import_loads_std_module_source() {
        let root = temp_root("explicit-std-import");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(root.join("std")).unwrap();
        fs::write(
            root.join("main.yu"),
            "use std::index::Index\nmy f = Index::index\n",
        )
        .unwrap();
        fs::write(
            root.join("std").join("index.yu"),
            "pub role Index 'container 'key 'value:\n  our index: 'container -> 'key -> 'value\n",
        )
        .unwrap();

        let set = collect_source_files_with_options(
            root.join("main.yu"),
            SourceOptions {
                std_root: Some(root.join("std")),
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let module_paths = set
            .files
            .iter()
            .map(|file| names(&file.module_path))
            .collect::<Vec<_>>();

        assert_eq!(module_paths, vec![vec!["std", "index"], Vec::<&str>::new()]);
        assert_eq!(set.std_files().count(), 1);
        assert_eq!(set.entry_files().count(), 1);
        assert_eq!(set.user_files().count(), 0);

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn glob_without_excludes_operator_syntax_from_full_parse() {
        let root = temp_root("operator-syntax-without");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("main.yu"),
            "mod ops;\nuse ops::* without (%%)\nmy y = 1 %% true\n",
        )
        .unwrap();
        fs::write(
            root.join("ops.yu"),
            "pub infix (%%) 50 51 = \\x -> \\y -> y\n",
        )
        .unwrap();

        let set = collect_source_files(root.join("main.yu")).unwrap();
        let main = set
            .files
            .iter()
            .find(|file| file.module_path.segments.is_empty())
            .unwrap();
        let parsed = SyntaxNode::<YulangLanguage>::new_root(
            yulang_parser::parse_module_to_green_with_ops(&main.source, main.op_table.clone()),
        );

        assert!(!parsed.descendants_with_tokens().any(|item| {
            matches!(
                item,
                NodeOrToken::Token(tok) if tok.kind() == SyntaxKind::Infix && tok.text() == "%%"
            )
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn compilation_units_keep_file_sccs_and_operator_exports() {
        let set = collect_inline_source_files_with_options(
            "use a::*\n1 %% 2\n",
            [
                InlineSource {
                    path: PathBuf::from("<a>.yu"),
                    module_path: module_path(&["a"]),
                    origin: SourceOrigin::User,
                    source: "use b::*\npub infix (%%) 50 51 = \\x -> \\y -> x\n".to_string(),
                    meta: None,
                },
                InlineSource {
                    path: PathBuf::from("<b>.yu"),
                    module_path: module_path(&["b"]),
                    origin: SourceOrigin::User,
                    source: "use a::*\npub prefix(not) 8.0.0 = \\x -> x\n".to_string(),
                    meta: None,
                },
            ],
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        );
        let units = set.compilation_units();
        let cyclic_unit = units
            .units
            .iter()
            .find(|unit| unit.files.len() == 2)
            .expect("a/b should form one SCC");
        let unit_modules = cyclic_unit
            .files
            .iter()
            .map(|&idx| names(&set.files[idx].module_path))
            .collect::<Vec<_>>();
        assert!(unit_modules.contains(&vec!["a"]));
        assert!(unit_modules.contains(&vec!["b"]));
        assert!(
            cyclic_unit
                .syntax_exports
                .iter()
                .any(|export| export.name == Name("%%".to_string()))
        );
        assert!(
            cyclic_unit
                .syntax_exports
                .iter()
                .any(|export| export.name == Name("not".to_string()))
        );
    }

    #[test]
    fn compiled_syntax_artifact_preserves_operator_exports_and_reexports() {
        let set = collect_inline_source_files_with_options(
            "use prelude::*\n1 %% 2\n",
            [
                InlineSource {
                    path: PathBuf::from("<ops>.yu"),
                    module_path: module_path(&["ops"]),
                    origin: SourceOrigin::User,
                    source: "pub infix (%%) 50 51 = \\x -> \\y -> x\n".to_string(),
                    meta: None,
                },
                InlineSource {
                    path: PathBuf::from("<prelude>.yu"),
                    module_path: module_path(&["prelude"]),
                    origin: SourceOrigin::User,
                    source: "pub use ops::*\n".to_string(),
                    meta: None,
                },
            ],
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        );

        let artifacts = set.compiled_unit_syntax_artifacts();
        let ops_artifact = artifacts
            .iter()
            .find(|artifact| {
                artifact
                    .manifest
                    .files
                    .iter()
                    .any(|file| names(&file.module_path) == vec!["ops"])
            })
            .expect("ops unit should exist");
        assert!(
            ops_artifact
                .syntax
                .direct_exports
                .iter()
                .any(|export| export.name == Name("%%".to_string()))
        );

        let prelude_artifact = artifacts
            .iter()
            .find(|artifact| {
                artifact
                    .manifest
                    .files
                    .iter()
                    .any(|file| names(&file.module_path) == vec!["prelude"])
            })
            .expect("prelude unit should exist");
        assert!(
            prelude_artifact
                .syntax
                .public_exports
                .iter()
                .any(|export| export.name == Name("%%".to_string()))
        );
    }

    #[test]
    fn compiled_syntax_artifact_rebuilds_operator_table_for_parse() {
        let set = collect_inline_source_files_with_options(
            "use ops::*\n1 %% 2\n",
            [InlineSource {
                path: PathBuf::from("<ops>.yu"),
                module_path: module_path(&["ops"]),
                origin: SourceOrigin::User,
                source: "pub infix (%%) 50 51 = \\x -> \\y -> x\n".to_string(),
                meta: None,
            }],
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        );
        let artifact = set
            .compiled_unit_syntax_artifacts()
            .into_iter()
            .find(|artifact| {
                artifact
                    .manifest
                    .files
                    .iter()
                    .any(|file| names(&file.module_path) == vec!["ops"])
            })
            .expect("ops artifact should exist");
        let mut table = standard_op_table();
        for export in &artifact.syntax.public_exports {
            insert_table_op_def(&mut table.0, export.name.clone(), export.op.to_op_def());
        }
        let parsed = SyntaxNode::<YulangLanguage>::new_root(
            yulang_parser::parse_module_to_green_with_ops("my y = 1 %% 2\n", table),
        );

        assert!(parsed.descendants_with_tokens().any(|item| {
            matches!(
                item,
                NodeOrToken::Token(tok) if tok.kind() == SyntaxKind::Infix && tok.text() == "%%"
            )
        }));
    }

    #[test]
    fn compiled_syntax_imports_build_downstream_operator_table_without_dependency_source() {
        let dependency_set = collect_inline_source_files_with_options(
            "mod ops;\n",
            [InlineSource {
                path: PathBuf::from("<ops>.yu"),
                module_path: module_path(&["ops"]),
                origin: SourceOrigin::User,
                source: "pub infix (%%) 50 51 = \\x -> \\y -> x\n".to_string(),
                meta: None,
            }],
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        );
        let artifacts = dependency_set.compiled_unit_syntax_artifacts();
        let meta = parse_source_meta("use ops::*\nmy y = 1 %% 2\n");
        let table = op_table_from_compiled_syntax_imports(&meta, &artifacts);
        let parsed = SyntaxNode::<YulangLanguage>::new_root(
            yulang_parser::parse_module_to_green_with_ops("use ops::*\nmy y = 1 %% 2\n", table),
        );

        assert!(parsed.descendants_with_tokens().any(|item| {
            matches!(
                item,
                NodeOrToken::Token(tok) if tok.kind() == SyntaxKind::Infix && tok.text() == "%%"
            )
        }));
    }

    #[test]
    fn compiled_syntax_artifact_round_trips_through_json() {
        let set = collect_inline_source_files_with_options(
            "use ops::*\n1 %% 2\n",
            [InlineSource {
                path: PathBuf::from("<ops>.yu"),
                module_path: module_path(&["ops"]),
                origin: SourceOrigin::User,
                source: "pub infix (%%) 50 51 = \\x -> \\y -> x\n".to_string(),
                meta: None,
            }],
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        );
        let artifact = set
            .compiled_unit_syntax_artifacts()
            .into_iter()
            .find(|artifact| {
                artifact
                    .manifest
                    .files
                    .iter()
                    .any(|file| names(&file.module_path) == vec!["ops"])
            })
            .expect("ops artifact should exist");

        let encoded = serde_json::to_string(&artifact).unwrap();
        let decoded: CompiledUnitSyntaxArtifact = serde_json::from_str(&encoded).unwrap();

        assert_eq!(decoded, artifact);
    }

    #[test]
    fn compiled_syntax_artifact_hash_changes_when_operator_changes() {
        let first = collect_inline_source_files_with_options(
            "use ops::*\n1 %% 2\n",
            [InlineSource {
                path: PathBuf::from("<ops>.yu"),
                module_path: module_path(&["ops"]),
                origin: SourceOrigin::User,
                source: "pub infix (%%) 50 51 = \\x -> \\y -> x\n".to_string(),
                meta: None,
            }],
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        );
        let second = collect_inline_source_files_with_options(
            "use ops::*\n1 %% 2\n",
            [InlineSource {
                path: PathBuf::from("<ops>.yu"),
                module_path: module_path(&["ops"]),
                origin: SourceOrigin::User,
                source: "pub infix (%%) 60 61 = \\x -> \\y -> x\n".to_string(),
                meta: None,
            }],
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        );
        let first_artifact = first
            .compiled_unit_syntax_artifacts()
            .into_iter()
            .find(|artifact| {
                artifact
                    .manifest
                    .files
                    .iter()
                    .any(|file| names(&file.module_path) == vec!["ops"])
            })
            .unwrap();
        let second_artifact = second
            .compiled_unit_syntax_artifacts()
            .into_iter()
            .find(|artifact| {
                artifact
                    .manifest
                    .files
                    .iter()
                    .any(|file| names(&file.module_path) == vec!["ops"])
            })
            .unwrap();

        assert_ne!(
            first_artifact.manifest.source_hash,
            second_artifact.manifest.source_hash
        );
        assert_ne!(
            first_artifact.manifest.syntax_hash,
            second_artifact.manifest.syntax_hash
        );
    }

    #[test]
    fn compiled_unit_interface_hash_can_stay_stable_when_source_changes() {
        let first = collect_inline_source_files_with_options(
            "use dep::*\nx\n",
            [InlineSource {
                path: PathBuf::from("<dep>.yu"),
                module_path: module_path(&["dep"]),
                origin: SourceOrigin::User,
                source: "pub x = 1\n".to_string(),
                meta: None,
            }],
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        );
        let second = collect_inline_source_files_with_options(
            "use dep::*\nx\n",
            [InlineSource {
                path: PathBuf::from("<dep>.yu"),
                module_path: module_path(&["dep"]),
                origin: SourceOrigin::User,
                source: "pub x = 2\n".to_string(),
                meta: None,
            }],
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        );
        let dep_artifact = |set: SourceSet| {
            set.compiled_unit_syntax_artifacts()
                .into_iter()
                .find(|artifact| {
                    artifact
                        .manifest
                        .files
                        .iter()
                        .any(|file| names(&file.module_path) == vec!["dep"])
                })
                .unwrap()
        };
        let first_artifact = dep_artifact(first);
        let second_artifact = dep_artifact(second);

        assert_ne!(
            first_artifact.manifest.source_hash,
            second_artifact.manifest.source_hash
        );
        assert_eq!(
            first_artifact.manifest.interface_hash,
            second_artifact.manifest.interface_hash
        );
    }

    #[test]
    fn virtual_source_set_has_resolved_entry_band() {
        let set = collect_virtual_source_files_with_options(
            "1\n",
            None,
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        )
        .unwrap();

        assert_eq!(set.realms.len(), 1);
        assert_eq!(set.realms[0].id.identity.0, "virtual:entry");
        assert_eq!(set.entry_bands().count(), 1);
        assert_eq!(set.realms[0].bands[0].files, vec![0]);
        assert_eq!(
            set.files[0].band.as_ref(),
            Some(&ResolvedBandId {
                realm: set.realms[0].id.clone(),
                band: BandPath::root(),
            })
        );
    }

    #[test]
    fn compiled_unit_manifest_records_resolved_realm_and_band() {
        let set = collect_inline_source_files_with_options(
            "use ops::*\n1 %% 2\n",
            [InlineSource {
                path: PathBuf::from("<ops>.yu"),
                module_path: module_path(&["ops"]),
                origin: SourceOrigin::User,
                source: "pub infix (%%) 50 51 = \\x -> \\y -> x\n".to_string(),
                meta: None,
            }],
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        );

        let artifact = set
            .compiled_unit_syntax_artifacts()
            .into_iter()
            .find(|artifact| {
                artifact
                    .manifest
                    .files
                    .iter()
                    .any(|file| names(&file.module_path) == vec!["ops"])
            })
            .expect("ops artifact should exist");

        assert_eq!(artifact.manifest.realms, vec![set.realms[0].id.clone()]);
        assert_eq!(
            artifact.manifest.bands,
            vec![ResolvedBandId {
                realm: set.realms[0].id.clone(),
                band: BandPath::from_segments(vec![Name("ops".to_string())]),
            }]
        );
    }

    #[test]
    fn local_source_set_has_file_realm_and_entry_band() {
        let root = temp_root("local-realm-band");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(root.join("main.yu"), "mod child;\nchild::x\n").unwrap();
        fs::write(root.join("child.yu"), "pub x = 1\n").unwrap();

        let set = collect_source_files(root.join("main.yu")).unwrap();

        assert_eq!(set.realms.len(), 1);
        assert!(set.realms[0].id.identity.0.starts_with("file://"));
        assert_eq!(set.entry_bands().count(), 1);
        assert_eq!(set.realms[0].bands[0].files.len(), 2);
        assert!(set.files.iter().all(|file| file.band.as_ref()
            == Some(&ResolvedBandId {
                realm: set.realms[0].id.clone(),
                band: BandPath::root(),
            })));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn use_imported_source_starts_a_separate_band() {
        let root = temp_root("use-import-band");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(root.join("main.yu"), "use util::*\nx\n").unwrap();
        fs::write(root.join("util.yu"), "pub x = 1\n").unwrap();

        let set = collect_source_files_with_options(
            root.join("main.yu"),
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: vec![root.clone()],
            },
        )
        .unwrap();
        let realm = &set.realms[0];
        let root_band = realm.band(&BandPath::root()).unwrap();
        let util_band = realm
            .band(&BandPath::from_segments(vec![Name("util".to_string())]))
            .unwrap();

        assert_eq!(realm.bands.len(), 2);
        assert!(root_band.entry);
        assert!(!util_band.entry);
        assert_eq!(root_band.files.len(), 1);
        assert_eq!(util_band.files.len(), 1);
        assert_eq!(
            set.files[root_band.files[0]].band.as_ref().unwrap().band,
            BandPath::root()
        );
        assert_eq!(
            set.files[util_band.files[0]].band.as_ref().unwrap().band,
            BandPath::from_segments(vec![Name("util".to_string())])
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn imported_band_keeps_mod_children_inside_same_band() {
        let root = temp_root("imported-band-mod-tree");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(root.join("util")).unwrap();
        fs::write(root.join("main.yu"), "use util::*\nx\n").unwrap();
        fs::write(root.join("util.yu"), "mod extra;\npub x = extra::x\n").unwrap();
        fs::write(root.join("util/extra.yu"), "pub x = 1\n").unwrap();

        let set = collect_source_files_with_options(
            root.join("main.yu"),
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: vec![root.clone()],
            },
        )
        .unwrap();
        let realm = &set.realms[0];
        let util_path = BandPath::from_segments(vec![Name("util".to_string())]);
        let util_band = realm.band(&util_path).unwrap();
        let mut util_file_paths = util_band
            .files
            .iter()
            .map(|&file_idx| names(&set.files[file_idx].module_path))
            .collect::<Vec<_>>();
        util_file_paths.sort();

        assert_eq!(realm.bands.len(), 2);
        assert_eq!(util_file_paths, vec![vec!["util"], vec!["util", "extra"]]);
        assert!(util_band.files.iter().all(|&file_idx| {
            set.files[file_idx].band.as_ref()
                == Some(&ResolvedBandId {
                    realm: realm.id.clone(),
                    band: util_path.clone(),
                })
        }));

        let util_artifacts = set
            .compiled_unit_syntax_artifacts()
            .into_iter()
            .filter(|artifact| {
                artifact
                    .manifest
                    .bands
                    .iter()
                    .any(|band| band.band == util_path)
            })
            .collect::<Vec<_>>();
        assert_eq!(util_artifacts.len(), 2);
        assert!(util_artifacts.iter().all(|artifact| artifact.manifest.bands
            == vec![ResolvedBandId {
                realm: realm.id.clone(),
                band: util_path.clone(),
            }]));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn manifest_dependency_use_loads_cross_realm_source() {
        let root = temp_root("cross-realm-use");
        let _ = fs::remove_dir_all(&root);
        let app = root.join("app");
        let ui = root.join("deps").join("ui");
        fs::create_dir_all(ui.join("widget")).unwrap();
        fs::create_dir_all(&app).unwrap();
        fs::write(
            app.join("realm.toml"),
            r#"[realm]
identity = "user/app"
version = "0.1.0"

[dependencies]
ui = "2.4.0"
"#,
        )
        .unwrap();
        fs::write(app.join("main.yu"), "use ui/widget::*\nx\n").unwrap();
        fs::write(
            ui.join("realm.toml"),
            r#"[realm]
identity = "ui"
version = "2.4.0"
"#,
        )
        .unwrap();
        fs::write(ui.join("widget.yu"), "mod part;\npub x = part::x\n").unwrap();
        fs::write(ui.join("widget").join("part.yu"), "pub x = 1\n").unwrap();

        let set = collect_source_files_with_options(
            app.join("main.yu"),
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: vec![root.join("deps")],
            },
        )
        .unwrap();

        assert_eq!(set.realms.len(), 2);
        let ui_realm = set
            .realms
            .iter()
            .find(|realm| realm.id.identity.0 == "ui")
            .expect("ui realm should be loaded");
        assert_eq!(ui_realm.id.version, Some(RealmVersion("2.4.0".to_string())));
        let widget_band = ui_realm
            .band(&BandPath::from_segments(vec![Name("widget".to_string())]))
            .expect("widget band should be assigned inside ui realm");
        let mut widget_modules = widget_band
            .files
            .iter()
            .map(|&idx| names(&set.files[idx].module_path))
            .collect::<Vec<_>>();
        widget_modules.sort();
        assert_eq!(
            widget_modules,
            vec![vec!["ui", "widget"], vec!["ui", "widget", "part"]]
        );
        assert!(widget_band.files.iter().all(|&idx| {
            set.files[idx].band.as_ref()
                == Some(&ResolvedBandId {
                    realm: ui_realm.id.clone(),
                    band: BandPath::from_segments(vec![Name("widget".to_string())]),
                })
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn lock_file_use_loads_cross_realm_source() {
        let root = temp_root("cross-realm-lock-use");
        let _ = fs::remove_dir_all(&root);
        let app = root.join("app");
        let ui = root.join("deps").join("ui-2.4.0");
        fs::create_dir_all(&app).unwrap();
        fs::create_dir_all(&ui).unwrap();
        fs::write(
            app.join("realm.toml"),
            r#"[realm]
identity = "user/app"
version = "0.1.0"

[dependencies]
ui = "2.4.0"
"#,
        )
        .unwrap();
        fs::write(app.join("main.yu"), "use ui/widget::*\nx\n").unwrap();
        let lock = YulangLockFile {
            format_version: YULANG_LOCK_FORMAT_VERSION,
            realms: vec![LockedRealm {
                id: ResolvedRealmId {
                    identity: RealmIdentity("ui".to_string()),
                    version: Some(RealmVersion("2.4.0".to_string())),
                },
                source: LockedRealmSource::Local(ui.clone()),
                source_hash: None,
            }],
            dependencies: Vec::new(),
            with_constraints: Vec::new(),
        };
        fs::write(
            app.join("yulang.lock"),
            format!("{}\n", serde_json::to_string_pretty(&lock).unwrap()),
        )
        .unwrap();
        fs::write(
            ui.join("realm.toml"),
            r#"[realm]
identity = "ui"
version = "2.4.0"
"#,
        )
        .unwrap();
        fs::write(ui.join("widget.yu"), "pub x = 1\n").unwrap();

        let set = collect_source_files_with_options(
            app.join("main.yu"),
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        )
        .unwrap();

        assert!(set.realms.iter().any(|realm| realm.id
            == ResolvedRealmId {
                identity: RealmIdentity("ui".to_string()),
                version: Some(RealmVersion("2.4.0".to_string())),
            }));
        assert!(
            set.files
                .iter()
                .any(|file| names(&file.module_path) == vec!["ui", "widget"]
                    && file.realm.identity.0 == "ui")
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn lock_with_constraint_selects_cross_realm_version() {
        let root = temp_root("cross-realm-with-lock-use");
        let _ = fs::remove_dir_all(&root);
        let app = root.join("app");
        let ui_v1 = root.join("deps").join("ui-1.0.0");
        let ui_v2 = root.join("deps").join("ui-2.4.0");
        fs::create_dir_all(&app).unwrap();
        fs::create_dir_all(&ui_v1).unwrap();
        fs::create_dir_all(&ui_v2).unwrap();
        fs::write(
            app.join("realm.toml"),
            r#"[realm]
identity = "user/app"
version = "0.1.0"

[dependencies]
ui = "2.4.0"
"#,
        )
        .unwrap();
        fs::write(
            app.join("main.yu"),
            "use ui/widget::* with program::ui\nx\n",
        )
        .unwrap();
        let lock = YulangLockFile {
            format_version: YULANG_LOCK_FORMAT_VERSION,
            realms: vec![
                LockedRealm {
                    id: ResolvedRealmId {
                        identity: RealmIdentity("ui".to_string()),
                        version: Some(RealmVersion("1.0.0".to_string())),
                    },
                    source: LockedRealmSource::Local(ui_v1.clone()),
                    source_hash: None,
                },
                LockedRealm {
                    id: ResolvedRealmId {
                        identity: RealmIdentity("ui".to_string()),
                        version: Some(RealmVersion("2.4.0".to_string())),
                    },
                    source: LockedRealmSource::Local(ui_v2.clone()),
                    source_hash: None,
                },
            ],
            dependencies: Vec::new(),
            with_constraints: vec![LockedWithConstraint {
                requester: ResolvedRealmId {
                    identity: RealmIdentity("user/app".to_string()),
                    version: Some(RealmVersion("0.1.0".to_string())),
                },
                target: RealmIdentity("ui".to_string()),
                anchor: BandPath::from_segments(vec![
                    Name("program".to_string()),
                    Name("ui".to_string()),
                ]),
                resolved: ResolvedRealmId {
                    identity: RealmIdentity("ui".to_string()),
                    version: Some(RealmVersion("2.4.0".to_string())),
                },
            }],
        };
        fs::write(
            app.join("yulang.lock"),
            format!("{}\n", serde_json::to_string_pretty(&lock).unwrap()),
        )
        .unwrap();
        fs::write(
            ui_v1.join("realm.toml"),
            r#"[realm]
identity = "ui"
version = "1.0.0"
"#,
        )
        .unwrap();
        fs::write(ui_v1.join("widget.yu"), "pub x = 1\n").unwrap();
        fs::write(
            ui_v2.join("realm.toml"),
            r#"[realm]
identity = "ui"
version = "2.4.0"
"#,
        )
        .unwrap();
        fs::write(ui_v2.join("widget.yu"), "pub x = 2\n").unwrap();

        let set = collect_source_files_with_options(
            app.join("main.yu"),
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        )
        .unwrap();

        let ui_file = set
            .files
            .iter()
            .find(|file| names(&file.module_path) == vec!["ui", "widget"])
            .expect("ui widget should load");
        assert_eq!(
            ui_file.realm,
            ResolvedRealmId {
                identity: RealmIdentity("ui".to_string()),
                version: Some(RealmVersion("2.4.0".to_string())),
            }
        );
        assert!(ui_file.path.starts_with(&ui_v2));
        assert!(ui_file.source.contains("pub x = 2"));
        let generated = YulangLockFile::from_source_set(&set).expect("lock should build");
        assert_eq!(generated.with_constraints.len(), 1);
        assert_eq!(
            generated.with_constraints[0].resolved,
            ResolvedRealmId {
                identity: RealmIdentity("ui".to_string()),
                version: Some(RealmVersion("2.4.0".to_string())),
            }
        );
        assert_eq!(
            generated
                .dependencies
                .iter()
                .find(|dependency| dependency.to.identity.0 == "ui")
                .map(|dependency| dependency.to.version.clone()),
            Some(Some(RealmVersion("2.4.0".to_string())))
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn freeze_realm_writes_versioned_snapshot_under_yulang_dir() {
        let root = temp_root("freeze-realm");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(root.join("widget")).unwrap();
        fs::create_dir_all(root.join(".yulang").join("versions").join("old")).unwrap();
        fs::write(
            root.join("realm.toml"),
            r#"[realm]
identity = "ui"

[dependencies]
std = "0.1.3"
"#,
        )
        .unwrap();
        fs::write(root.join("widget.yu"), "mod part;\npub x = part::x\n").unwrap();
        fs::write(root.join("widget").join("part.yu"), "pub x = 1\n").unwrap();
        fs::write(
            root.join("yulang.lock"),
            r#"{
  "format_version": 1,
  "realms": [],
  "dependencies": [],
  "with_constraints": []
}
"#,
        )
        .unwrap();
        fs::write(
            root.join(".yulang")
                .join("versions")
                .join("old")
                .join("ignored.yu"),
            "pub old = 1\n",
        )
        .unwrap();

        let frozen = freeze_realm_version(&root, "2.4.0").unwrap();

        assert!(!frozen.already_exists);
        assert_eq!(frozen.snapshot.identity, RealmIdentity("ui".to_string()));
        assert_eq!(frozen.snapshot.version, RealmVersion("2.4.0".to_string()));
        assert!(frozen.root.ends_with(".yulang/versions/2.4.0"));
        assert!(frozen.root.join("widget.yu").is_file());
        assert!(frozen.root.join("widget").join("part.yu").is_file());
        assert!(frozen.root.join("yulang.lock").is_file());
        assert!(!frozen.root.join(".yulang").exists());
        let frozen_manifest = fs::read_to_string(frozen.root.join("realm.toml")).unwrap();
        assert!(frozen_manifest.contains("version = \"2.4.0\""));
        assert!(frozen_manifest.contains("std = \"0.1.3\""));
        let snapshot_source = fs::read_to_string(&frozen.snapshot_path).unwrap();
        let decoded: FrozenRealmSnapshot = serde_json::from_str(&snapshot_source).unwrap();
        assert_eq!(decoded, frozen.snapshot);

        let repeated = freeze_realm_version(&root, "2.4.0").unwrap();
        assert!(repeated.already_exists);
        assert_eq!(repeated.snapshot.source_hash, frozen.snapshot.source_hash);

        fs::write(root.join("widget.yu"), "pub x = 2\n").unwrap();
        let err = freeze_realm_version(&root, "2.4.0").unwrap_err();
        assert!(matches!(
            err,
            FreezeRealmError::SnapshotExistsHashMismatch { .. }
        ));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn frozen_realm_snapshot_resolves_as_versioned_cross_realm_use() {
        let root = temp_root("freeze-realm-use");
        let _ = fs::remove_dir_all(&root);
        let app = root.join("app");
        let ui = root.join("ui");
        fs::create_dir_all(&app).unwrap();
        fs::create_dir_all(&ui).unwrap();
        fs::write(
            app.join("realm.toml"),
            r#"[realm]
identity = "user/app"
version = "0.1.0"

[dependencies]
ui = "2.4.0"
"#,
        )
        .unwrap();
        fs::write(app.join("main.yu"), "use ui/widget::*\nx\n").unwrap();
        fs::write(
            ui.join("realm.toml"),
            r#"[realm]
identity = "ui"
"#,
        )
        .unwrap();
        fs::write(ui.join("widget.yu"), "pub x = 1\n").unwrap();
        let frozen = freeze_realm_version(&ui, "2.4.0").unwrap();
        fs::write(ui.join("widget.yu"), "pub x = \"editable\"\n").unwrap();

        let set = collect_source_files_with_options(
            app.join("main.yu"),
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: vec![root.clone()],
            },
        )
        .unwrap();

        let frozen_file = set
            .files
            .iter()
            .find(|file| names(&file.module_path) == vec!["ui", "widget"])
            .expect("frozen ui widget should load");
        assert!(
            frozen_file
                .path
                .ends_with(".yulang/versions/2.4.0/widget.yu")
        );
        assert!(frozen_file.source.contains("pub x = 1"));
        let generated = YulangLockFile::from_source_set(&set).expect("lock should build");
        assert_eq!(
            generated
                .realms
                .iter()
                .find(|realm| realm.id.identity.0 == "ui")
                .and_then(|realm| realm.source_hash),
            Some(frozen.snapshot.source_hash)
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn lock_file_rejects_frozen_snapshot_hash_mismatch() {
        let root = temp_root("freeze-realm-lock-hash");
        let _ = fs::remove_dir_all(&root);
        let app = root.join("app");
        let ui = root.join("ui");
        fs::create_dir_all(&app).unwrap();
        fs::create_dir_all(&ui).unwrap();
        fs::write(app.join("main.yu"), "use ui/widget::*\nx\n").unwrap();
        fs::write(
            ui.join("realm.toml"),
            r#"[realm]
identity = "ui"
"#,
        )
        .unwrap();
        fs::write(ui.join("widget.yu"), "pub x = 1\n").unwrap();
        let frozen = freeze_realm_version(&ui, "2.4.0").unwrap();
        let stale_hash = frozen.snapshot.source_hash ^ 1;
        let lock = YulangLockFile {
            format_version: YULANG_LOCK_FORMAT_VERSION,
            realms: vec![LockedRealm {
                id: ResolvedRealmId {
                    identity: RealmIdentity("ui".to_string()),
                    version: Some(RealmVersion("2.4.0".to_string())),
                },
                source: LockedRealmSource::Local(frozen.root.clone()),
                source_hash: Some(stale_hash),
            }],
            dependencies: Vec::new(),
            with_constraints: Vec::new(),
        };
        fs::write(
            app.join("yulang.lock"),
            format!("{}\n", serde_json::to_string_pretty(&lock).unwrap()),
        )
        .unwrap();

        let err = collect_source_files_with_options(
            app.join("main.yu"),
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        )
        .unwrap_err();

        assert!(matches!(
            err,
            SourceLoadError::LockedRealmHashMismatch {
                expected,
                actual: Some(actual),
                ..
            } if expected == stale_hash && actual == frozen.snapshot.source_hash
        ));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn manifest_range_dependency_selects_highest_matching_frozen_snapshot() {
        let root = temp_root("freeze-realm-range-use");
        let _ = fs::remove_dir_all(&root);
        let app = root.join("app");
        let ui = root.join("ui");
        fs::create_dir_all(&app).unwrap();
        fs::create_dir_all(&ui).unwrap();
        fs::write(
            app.join("realm.toml"),
            r#"[realm]
identity = "user/app"
version = "0.1.0"

[dependencies]
ui = "^2.4"
"#,
        )
        .unwrap();
        fs::write(app.join("main.yu"), "use ui/widget::*\nx\n").unwrap();
        fs::write(
            ui.join("realm.toml"),
            r#"[realm]
identity = "ui"
"#,
        )
        .unwrap();

        fs::write(ui.join("widget.yu"), "pub x = 24\n").unwrap();
        freeze_realm_version(&ui, "2.4.0").unwrap();
        fs::write(ui.join("widget.yu"), "pub x = 25\n").unwrap();
        freeze_realm_version(&ui, "2.5.0").unwrap();
        fs::write(ui.join("widget.yu"), "pub x = 30\n").unwrap();
        freeze_realm_version(&ui, "3.0.0").unwrap();

        let set = collect_source_files_with_options(
            app.join("main.yu"),
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: vec![root.clone()],
            },
        )
        .unwrap();

        let frozen_file = set
            .files
            .iter()
            .find(|file| names(&file.module_path) == vec!["ui", "widget"])
            .expect("frozen ui widget should load");
        assert!(
            frozen_file
                .path
                .ends_with(".yulang/versions/2.5.0/widget.yu")
        );
        assert!(frozen_file.source.contains("pub x = 25"));
        assert_eq!(
            frozen_file.realm,
            ResolvedRealmId {
                identity: RealmIdentity("ui".to_string()),
                version: Some(RealmVersion("2.5.0".to_string())),
            }
        );

        let _ = fs::remove_dir_all(root);
    }
}
