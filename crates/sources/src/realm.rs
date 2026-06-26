use serde::{Deserialize, Serialize};
use std::error::Error;
use std::fmt;
use std::fs;
use std::io;
use std::path::{Path as FsPath, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

pub const YULANG_PROJECT_DIR: &str = ".yulang";
pub const YULANG_MANIFEST_FILE: &str = "realm.toml";
pub const YULANG_LOCK_FILE: &str = "yulang.lock";
const FROZEN_REALM_SNAPSHOT_FORMAT_VERSION: u32 = 2;

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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceRealmManifest {
    pub id: ResolvedRealmId,
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

#[derive(Debug)]
pub enum RealmManifestError {
    Io { path: PathBuf, error: io::Error },
    Invalid { path: PathBuf, message: String },
}

impl fmt::Display for RealmManifestError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io { path, error } => {
                write!(
                    f,
                    "failed to read realm manifest {}: {error}",
                    path.display()
                )
            }
            Self::Invalid { path, message } => {
                write!(f, "invalid realm manifest {}: {message}", path.display())
            }
        }
    }
}

impl Error for RealmManifestError {}

#[derive(Debug)]
pub enum FreezeRealmError {
    InvalidVersion(String),
    MissingManifest {
        root: PathBuf,
    },
    Manifest(RealmManifestError),
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
            Self::InvalidVersion(version) => write!(f, "invalid realm version `{version}`"),
            Self::MissingManifest { root } => {
                write!(f, "realm manifest not found under {}", root.display())
            }
            Self::Manifest(error) => write!(f, "{error}"),
            Self::Io { path, error } => write!(f, "failed to access {}: {error}", path.display()),
            Self::EncodeManifest { path, message } => {
                write!(
                    f,
                    "failed to encode realm manifest {}: {message}",
                    path.display()
                )
            }
            Self::EncodeSnapshot { path, message } => {
                write!(
                    f,
                    "failed to encode realm snapshot {}: {message}",
                    path.display()
                )
            }
            Self::InvalidSnapshot { path, message } => {
                write!(f, "invalid realm snapshot {}: {message}", path.display())
            }
            Self::SnapshotExistsHashMismatch {
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

impl Error for FreezeRealmError {}

pub fn load_realm_manifest(
    root: impl AsRef<FsPath>,
) -> Result<Option<SourceRealmManifest>, RealmManifestError> {
    let root = root.as_ref();
    let path = root.join(YULANG_MANIFEST_FILE);
    if !path.is_file() {
        return Ok(None);
    }
    let source = fs::read_to_string(&path).map_err(|error| RealmManifestError::Io {
        path: path.clone(),
        error,
    })?;
    let decoded = toml::from_str::<RealmManifestToml>(&source).map_err(|error| {
        RealmManifestError::Invalid {
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
    if realm.version.is_some() {
        return Err(invalid_realm_manifest(
            &path,
            "realm.version is not allowed; freeze versions belong to snapshot.json",
        ));
    }
    if decoded.dependencies.is_some() {
        return Err(invalid_realm_manifest(
            &path,
            "[dependencies] is not allowed; dependency requests belong to source imports and the resolution cache",
        ));
    }

    Ok(Some(SourceRealmManifest {
        id: ResolvedRealmId {
            identity: RealmIdentity(identity),
            version: None,
        },
    }))
}

pub fn local_realm_root(entry: impl AsRef<FsPath>) -> PathBuf {
    let entry = entry.as_ref();
    let base = if entry.is_dir() {
        entry
    } else {
        entry.parent().unwrap_or_else(|| FsPath::new("."))
    };
    base.ancestors()
        .find(|ancestor| ancestor.join(YULANG_MANIFEST_FILE).is_file())
        .map(FsPath::to_path_buf)
        .unwrap_or_else(|| base.to_path_buf())
}

pub fn local_realm_id(entry: impl AsRef<FsPath>) -> ResolvedRealmId {
    ResolvedRealmId {
        identity: RealmIdentity(format!(
            "file://{}",
            canonicalize_for_dedupe(&local_realm_root(entry)).display()
        )),
        version: None,
    }
}

pub fn freeze_realm_version(
    root: impl AsRef<FsPath>,
    version: impl Into<String>,
) -> Result<FreezeRealmOutput, FreezeRealmError> {
    freeze_realm_version_inner(root.as_ref(), RealmVersion(version.into()))
}

#[derive(Debug, Serialize, Deserialize)]
struct RealmManifestToml {
    realm: Option<RealmManifestRealmToml>,
    dependencies: Option<toml::Value>,
}

#[derive(Debug, Serialize, Deserialize)]
struct RealmManifestRealmToml {
    identity: Option<String>,
    name: Option<String>,
    version: Option<String>,
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
        .map_err(FreezeRealmError::Manifest)?
        .ok_or_else(|| FreezeRealmError::MissingManifest { root: root.clone() })?;
    let snapshot_root = root
        .join(YULANG_PROJECT_DIR)
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
    write_frozen_realm_files(&root, &temp_root, &manifest, &files)?;
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

fn invalid_realm_manifest(path: &FsPath, message: impl Into<String>) -> RealmManifestError {
    RealmManifestError::Invalid {
        path: path.to_path_buf(),
        message: message.into(),
    }
}

fn collect_freezable_realm_files(root: &FsPath) -> Result<Vec<PathBuf>, FreezeRealmError> {
    let mut files = vec![PathBuf::from(YULANG_MANIFEST_FILE)];
    if root.join(YULANG_LOCK_FILE).is_file() {
        files.push(PathBuf::from(YULANG_LOCK_FILE));
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
        if file_name == YULANG_PROJECT_DIR || file_name == "target" {
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
    let frozen_manifest = frozen_realm_manifest_toml(manifest);
    let frozen_manifest_bytes = toml::to_string_pretty(&frozen_manifest)
        .map_err(|error| FreezeRealmError::EncodeManifest {
            path: source_root.join(YULANG_MANIFEST_FILE),
            message: error.to_string(),
        })?
        .into_bytes();
    let mut snapshot_files = Vec::new();
    let mut hash = StableHash::new();
    hash.write_str("frozen-realm-source-v2");
    hash.write_str(&manifest.id.identity.0);
    for file in files {
        let path = file.to_string_lossy().replace('\\', "/");
        let bytes = if file == FsPath::new(YULANG_MANIFEST_FILE) {
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
        format_version: FROZEN_REALM_SNAPSHOT_FORMAT_VERSION,
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
    files: &[PathBuf],
) -> Result<(), FreezeRealmError> {
    for relative in files {
        let output_path = output_root.join(relative);
        ensure_parent_dir(&output_path)?;
        if relative == FsPath::new(YULANG_MANIFEST_FILE) {
            let manifest = frozen_realm_manifest_toml(manifest);
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
            fs::copy(source_root.join(relative), &output_path)
                .map(|_| ())
                .map_err(|error| FreezeRealmError::Io {
                    path: output_path,
                    error,
                })?;
        }
    }
    Ok(())
}

fn frozen_realm_manifest_toml(manifest: &SourceRealmManifest) -> RealmManifestToml {
    RealmManifestToml {
        realm: Some(RealmManifestRealmToml {
            identity: Some(manifest.id.identity.0.clone()),
            name: None,
            version: None,
        }),
        dependencies: None,
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

fn canonicalize_for_dedupe(path: &FsPath) -> PathBuf {
    path.canonicalize().unwrap_or_else(|_| path.to_path_buf())
}

fn stable_hash_bytes(bytes: &[u8]) -> u64 {
    let mut hash = StableHash::new();
    hash.write_bytes(bytes);
    hash.finish()
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

    fn finish(self) -> u64 {
        self.value
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn temp_root(name: &str) -> PathBuf {
        std::env::temp_dir().join(format!(
            "yulang-sources-{name}-{}",
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ))
    }

    #[test]
    fn realm_manifest_sets_identity_only() {
        let root = temp_root("realm-manifest");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join(YULANG_MANIFEST_FILE),
            r#"[realm]
identity = "app"
"#,
        )
        .unwrap();

        let manifest = load_realm_manifest(&root).unwrap().unwrap();

        assert_eq!(manifest.id.identity, RealmIdentity("app".to_string()));
        assert_eq!(manifest.id.version, None);

        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn realm_manifest_rejects_human_written_version() {
        let root = temp_root("realm-manifest-version");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join(YULANG_MANIFEST_FILE),
            r#"[realm]
identity = "app"
version = "1.2.3"
"#,
        )
        .unwrap();

        let err = load_realm_manifest(&root).unwrap_err();

        assert!(
            err.to_string().contains("realm.version is not allowed"),
            "{err}"
        );

        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn realm_manifest_rejects_realm_wide_dependencies() {
        let root = temp_root("realm-manifest-dependencies");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join(YULANG_MANIFEST_FILE),
            r#"[realm]
identity = "app"

[dependencies]
ui = "^2"
"#,
        )
        .unwrap();

        let err = load_realm_manifest(&root).unwrap_err();

        assert!(
            err.to_string().contains("[dependencies] is not allowed"),
            "{err}"
        );

        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn freeze_realm_writes_versioned_snapshot() {
        let root = temp_root("realm-freeze");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(root.join("src")).unwrap();
        fs::create_dir_all(root.join(YULANG_PROJECT_DIR)).unwrap();
        fs::create_dir_all(root.join("target")).unwrap();
        fs::write(
            root.join(YULANG_MANIFEST_FILE),
            r#"[realm]
identity = "app"
"#,
        )
        .unwrap();
        fs::write(root.join(YULANG_LOCK_FILE), "{}\n").unwrap();
        fs::write(root.join("main.yu"), "my main = 1\n").unwrap();
        fs::write(root.join("src").join("util.yu"), "my util = 2\n").unwrap();
        fs::write(
            root.join(YULANG_PROJECT_DIR).join("ignored.yu"),
            "my x = 0\n",
        )
        .unwrap();
        fs::write(root.join("target").join("ignored.yu"), "my x = 0\n").unwrap();

        let output = freeze_realm_version(&root, "2.0.0").unwrap();
        let files = output
            .snapshot
            .files
            .iter()
            .map(|file| file.path.as_str())
            .collect::<Vec<_>>();

        assert!(!output.already_exists);
        assert!(files.contains(&YULANG_MANIFEST_FILE));
        assert!(files.contains(&YULANG_LOCK_FILE));
        assert!(files.contains(&"main.yu"));
        assert!(files.contains(&"src/util.yu"));
        assert!(!files.contains(&".yulang/ignored.yu"));
        assert!(!files.contains(&"target/ignored.yu"));
        assert!(output.root.join("main.yu").is_file());
        let frozen_manifest = fs::read_to_string(output.root.join(YULANG_MANIFEST_FILE)).unwrap();
        assert!(frozen_manifest.contains("identity = \"app\""));
        assert!(!frozen_manifest.contains("version = "));
        assert!(!frozen_manifest.contains("[dependencies]"));
        assert_eq!(
            output.snapshot.format_version,
            FROZEN_REALM_SNAPSHOT_FORMAT_VERSION
        );
        assert_eq!(output.snapshot.version, RealmVersion("2.0.0".to_string()));

        let repeated = freeze_realm_version(&root, "2.0.0").unwrap();
        assert!(repeated.already_exists);

        let _ = fs::remove_dir_all(&root);
    }
}
