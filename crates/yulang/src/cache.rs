//! Persistent artifact cache used by the `yulang` CLI.
//!
//! The cache starts after source collection. It deliberately avoids owning the
//! collector or std lookup rules so a cache hit cannot change which files form
//! the program.

use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};

use crate::source::CollectedSource;

const POLY_CACHE_FORMAT: u32 = 7;
const CONTROL_CACHE_FORMAT: u32 = 7;
// Bump when compiler/cache semantics change without a serialized envelope bump.
const CACHE_SCHEMA_VERSION: u32 = 1;
const SOURCE_CACHE_SALT: &[u8] = b"yulang/source-set-cache/v2";
const FNV_OFFSET: u64 = 0xcbf29ce484222325;
const FNV_PRIME: u64 = 0x100000001b3;
static CACHE_TMP_COUNTER: AtomicU64 = AtomicU64::new(0);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CacheSchema {
    version: u32,
    poly_format: u32,
    control_format: u32,
}

const CURRENT_CACHE_SCHEMA: CacheSchema = CacheSchema {
    version: CACHE_SCHEMA_VERSION,
    poly_format: POLY_CACHE_FORMAT,
    control_format: CONTROL_CACHE_FORMAT,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArtifactCache {
    root: PathBuf,
}

impl ArtifactCache {
    pub fn new(root: impl Into<PathBuf>) -> Self {
        Self { root: root.into() }
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    pub fn poly_artifact_path(&self, key: SourceCacheKey) -> PathBuf {
        self.artifact_dir("poly")
            .join(format!("{}.yuir", key.to_hex()))
    }

    pub fn control_artifact_path(&self, key: SourceCacheKey) -> PathBuf {
        self.artifact_dir("control-vm")
            .join(format!("{}.yuvm", key.to_hex()))
    }

    pub fn read_poly_artifact(
        &self,
        key: SourceCacheKey,
    ) -> Result<Option<CachedPolyArtifact>, CacheError> {
        let path = self.poly_artifact_path(key);
        let Some(envelope): Option<PolyCacheEnvelope> =
            read_cache_envelope(&path, POLY_CACHE_FORMAT)?
        else {
            return Ok(None);
        };
        Ok(Some(CachedPolyArtifact {
            arena: envelope.arena,
            labels: envelope.labels,
            file_count: envelope.file_count,
            errors: envelope.errors,
        }))
    }

    pub fn write_poly_artifact(
        &self,
        key: SourceCacheKey,
        artifact: &CachedPolyArtifact,
    ) -> Result<(), CacheError> {
        let path = self.poly_artifact_path(key);
        let envelope = PolyCacheEnvelope {
            format: POLY_CACHE_FORMAT,
            arena: &artifact.arena,
            labels: &artifact.labels,
            file_count: artifact.file_count,
            errors: &artifact.errors,
        };
        write_cache_envelope(&path, "yuir", &envelope)
    }

    pub fn read_control_artifact(
        &self,
        key: SourceCacheKey,
    ) -> Result<Option<CachedControlArtifact>, CacheError> {
        let path = self.control_artifact_path(key);
        let Some(envelope): Option<ControlCacheEnvelope> =
            read_cache_envelope(&path, CONTROL_CACHE_FORMAT)?
        else {
            return Ok(None);
        };
        Ok(Some(CachedControlArtifact {
            program: envelope.program,
            labels: envelope.labels,
            file_count: envelope.file_count,
            errors: envelope.errors,
        }))
    }

    pub fn write_control_artifact(
        &self,
        key: SourceCacheKey,
        artifact: &CachedControlArtifact,
    ) -> Result<(), CacheError> {
        let path = self.control_artifact_path(key);
        let envelope = ControlCacheEnvelope {
            format: CONTROL_CACHE_FORMAT,
            program: &artifact.program,
            labels: &artifact.labels,
            file_count: artifact.file_count,
            errors: &artifact.errors,
        };
        write_cache_envelope(&path, "yuvm", &envelope)
    }

    fn artifact_dir(&self, stage: &str) -> PathBuf {
        self.root.join("artifacts").join(stage)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct CachedControlArtifact {
    pub program: control_vm::Program,
    pub labels: poly::dump::DumpLabels,
    pub file_count: usize,
    pub errors: Vec<String>,
}

pub struct CachedPolyArtifact {
    pub arena: poly::expr::Arena,
    pub labels: poly::dump::DumpLabels,
    pub file_count: usize,
    pub errors: Vec<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SourceCacheKey {
    hash: u64,
}

impl SourceCacheKey {
    pub fn to_hex(self) -> String {
        format!("{:016x}", self.hash)
    }
}

pub fn source_cache_key(files: &[CollectedSource]) -> SourceCacheKey {
    source_cache_key_with_schema(files, CURRENT_CACHE_SCHEMA)
}

fn source_cache_key_with_schema(files: &[CollectedSource], schema: CacheSchema) -> SourceCacheKey {
    let mut hasher = StableHasher::new();
    hasher.bytes(SOURCE_CACHE_SALT);
    hasher.u32(schema.version);
    hasher.u32(schema.poly_format);
    hasher.u32(schema.control_format);
    hasher.usize(files.len());
    for file in files {
        hasher.string(&file.path.as_os_str().to_string_lossy());
        hasher.usize(file.module_path.segments.len());
        for segment in &file.module_path.segments {
            hasher.string(&segment.0);
        }
        hasher.string(&file.source);
    }
    SourceCacheKey {
        hash: hasher.finish(),
    }
}

#[derive(Debug)]
pub enum CacheError {
    Read {
        path: PathBuf,
        error: io::Error,
    },
    Decode {
        path: PathBuf,
        error: bincode::Error,
    },
    Encode {
        path: PathBuf,
        error: bincode::Error,
    },
    NoParent {
        path: PathBuf,
    },
    CreateDir {
        path: PathBuf,
        error: io::Error,
    },
    Write {
        path: PathBuf,
        error: io::Error,
    },
    Rename {
        from: PathBuf,
        to: PathBuf,
        error: io::Error,
    },
}

impl fmt::Display for CacheError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Read { path, error } => {
                write!(
                    f,
                    "failed to read cache artifact {}: {error}",
                    path.display()
                )
            }
            Self::Decode { path, error } => write!(
                f,
                "failed to decode cache artifact {}: {error}",
                path.display()
            ),
            Self::Encode { path, error } => write!(
                f,
                "failed to encode cache artifact {}: {error}",
                path.display()
            ),
            Self::NoParent { path } => {
                write!(
                    f,
                    "cache artifact {} has no parent directory",
                    path.display()
                )
            }
            Self::CreateDir { path, error } => write!(
                f,
                "failed to create cache directory {}: {error}",
                path.display()
            ),
            Self::Write { path, error } => {
                write!(
                    f,
                    "failed to write cache artifact {}: {error}",
                    path.display()
                )
            }
            Self::Rename { from, to, error } => write!(
                f,
                "failed to publish cache artifact {} -> {}: {error}",
                from.display(),
                to.display()
            ),
        }
    }
}

impl std::error::Error for CacheError {}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct PolyCacheEnvelope<T = poly::expr::Arena, L = poly::dump::DumpLabels, E = Vec<String>> {
    format: u32,
    arena: T,
    labels: L,
    file_count: usize,
    errors: E,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct ControlCacheEnvelope<T = control_vm::Program, L = poly::dump::DumpLabels, E = Vec<String>> {
    format: u32,
    program: T,
    labels: L,
    file_count: usize,
    errors: E,
}

fn read_cache_envelope<T>(path: &Path, format: u32) -> Result<Option<T>, CacheError>
where
    T: CacheEnvelope + DeserializeOwned,
{
    let bytes = match fs::read(path) {
        Ok(bytes) => bytes,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(error) => {
            return Err(CacheError::Read {
                path: path.to_path_buf(),
                error,
            });
        }
    };
    let envelope: T = bincode::deserialize(&bytes).map_err(|error| CacheError::Decode {
        path: path.to_path_buf(),
        error,
    })?;
    if envelope.format() != format {
        return Ok(None);
    }
    Ok(Some(envelope))
}

fn write_cache_envelope<T>(path: &Path, extension: &str, envelope: &T) -> Result<(), CacheError>
where
    T: Serialize,
{
    let bytes = bincode::serialize(envelope).map_err(|error| CacheError::Encode {
        path: path.to_path_buf(),
        error,
    })?;
    let Some(parent) = path.parent() else {
        return Err(CacheError::NoParent {
            path: path.to_path_buf(),
        });
    };
    fs::create_dir_all(parent).map_err(|error| CacheError::CreateDir {
        path: parent.to_path_buf(),
        error,
    })?;

    let tmp = cache_tmp_path(path, extension);
    fs::write(&tmp, bytes).map_err(|error| CacheError::Write {
        path: tmp.clone(),
        error,
    })?;
    if let Err(error) = fs::rename(&tmp, path) {
        let _ = fs::remove_file(&tmp);
        return Err(CacheError::Rename {
            from: tmp,
            to: path.to_path_buf(),
            error,
        });
    }
    Ok(())
}

fn cache_tmp_path(path: &Path, extension: &str) -> PathBuf {
    let counter = CACHE_TMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    path.with_extension(format!("{extension}.tmp-{}-{counter}", std::process::id()))
}

trait CacheEnvelope {
    fn format(&self) -> u32;
}

impl<T, E> CacheEnvelope for PolyCacheEnvelope<T, E> {
    fn format(&self) -> u32 {
        self.format
    }
}

impl<T, L, E> CacheEnvelope for ControlCacheEnvelope<T, L, E> {
    fn format(&self) -> u32 {
        self.format
    }
}

struct StableHasher {
    state: u64,
}

impl StableHasher {
    fn new() -> Self {
        Self { state: FNV_OFFSET }
    }

    fn finish(self) -> u64 {
        self.state
    }

    fn usize(&mut self, value: usize) {
        self.bytes(&(value as u64).to_le_bytes());
    }

    fn u32(&mut self, value: u32) {
        self.bytes(&value.to_le_bytes());
    }

    fn string(&mut self, value: &str) {
        self.bytes(value.as_bytes());
    }

    fn bytes(&mut self, bytes: &[u8]) {
        self.raw_bytes(&(bytes.len() as u64).to_le_bytes());
        self.raw_bytes(bytes);
    }

    fn raw_bytes(&mut self, bytes: &[u8]) {
        for byte in bytes {
            self.state ^= u64::from(*byte);
            self.state = self.state.wrapping_mul(FNV_PRIME);
        }
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;
    use std::time::{SystemTime, UNIX_EPOCH};

    use sources::{Name, Path};

    use super::*;

    #[test]
    fn source_cache_key_tracks_source_path_and_module() {
        let base = source("main.yu", &[], "1\n");
        let same = source("main.yu", &[], "1\n");
        let changed_source = source("main.yu", &[], "2\n");
        let changed_path = source("other.yu", &[], "1\n");
        let changed_module = source("main.yu", &["app"], "1\n");

        assert_eq!(source_cache_key(&[base.clone()]), source_cache_key(&[same]));
        assert_ne!(
            source_cache_key(&[base.clone()]),
            source_cache_key(&[changed_source])
        );
        assert_ne!(
            source_cache_key(&[base.clone()]),
            source_cache_key(&[changed_path])
        );
        assert_ne!(
            source_cache_key(&[base]),
            source_cache_key(&[changed_module])
        );
    }

    #[test]
    fn source_cache_key_tracks_cache_schema() {
        let files = vec![source("main.yu", &[], "1\n")];
        let current = source_cache_key_with_schema(&files, CURRENT_CACHE_SCHEMA);
        let changed_version = source_cache_key_with_schema(
            &files,
            CacheSchema {
                version: CURRENT_CACHE_SCHEMA.version + 1,
                ..CURRENT_CACHE_SCHEMA
            },
        );
        let changed_poly = source_cache_key_with_schema(
            &files,
            CacheSchema {
                poly_format: CURRENT_CACHE_SCHEMA.poly_format + 1,
                ..CURRENT_CACHE_SCHEMA
            },
        );
        let changed_control = source_cache_key_with_schema(
            &files,
            CacheSchema {
                control_format: CURRENT_CACHE_SCHEMA.control_format + 1,
                ..CURRENT_CACHE_SCHEMA
            },
        );

        assert_ne!(current, changed_version);
        assert_ne!(current, changed_poly);
        assert_ne!(current, changed_control);
    }

    #[test]
    fn cache_tmp_path_is_unique_within_process() {
        let artifact = PathBuf::from("artifact.yuvm");

        assert_ne!(
            cache_tmp_path(&artifact, "yuvm"),
            cache_tmp_path(&artifact, "yuvm")
        );
    }

    #[test]
    fn control_cache_round_trips_binary_artifact_envelope() {
        let root = temp_root("control-round-trip");
        let cache = ArtifactCache::new(&root);
        let key = source_cache_key(&[source("main.yu", &[], "1\n")]);
        let artifact = CachedControlArtifact {
            program: control_vm::Program::default(),
            labels: poly::dump::DumpLabels::new(),
            file_count: 1,
            errors: vec!["lowering warning".to_string()],
        };

        cache.write_control_artifact(key, &artifact).unwrap();
        let restored = cache.read_control_artifact(key).unwrap().unwrap();

        assert_eq!(restored, artifact);
        assert!(cache.control_artifact_path(key).is_file());
        assert_eq!(
            cache.control_artifact_path(key).extension().unwrap(),
            "yuvm"
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn poly_cache_round_trips_binary_artifact_envelope() {
        let root = temp_root("poly-round-trip");
        let cache = ArtifactCache::new(&root);
        let key = source_cache_key(&[source("main.yu", &[], "1\n")]);
        let artifact = CachedPolyArtifact {
            arena: poly::expr::Arena::new(),
            labels: poly::dump::DumpLabels::new(),
            file_count: 1,
            errors: vec!["lowering warning".to_string()],
        };

        cache.write_poly_artifact(key, &artifact).unwrap();
        let restored = cache.read_poly_artifact(key).unwrap().unwrap();

        assert_eq!(restored.file_count, artifact.file_count);
        assert_eq!(restored.errors, artifact.errors);
        assert!(cache.poly_artifact_path(key).is_file());
        assert_eq!(cache.poly_artifact_path(key).extension().unwrap(), "yuir");

        let _ = fs::remove_dir_all(root);
    }

    fn source(path: &str, module: &[&str], text: &str) -> CollectedSource {
        CollectedSource {
            path: PathBuf::from(path),
            module_path: Path {
                segments: module
                    .iter()
                    .map(|segment| Name((*segment).to_string()))
                    .collect(),
            },
            source: text.to_string(),
        }
    }

    fn temp_root(name: &str) -> PathBuf {
        std::env::temp_dir().join(format!(
            "yulang-cache-{name}-{}",
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ))
    }
}
