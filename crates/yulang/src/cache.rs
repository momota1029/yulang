//! Persistent artifact cache used by the `yulang` CLI.
//!
//! The cache starts after source collection. It deliberately avoids owning the
//! collector or std lookup rules so a cache hit cannot change which files form
//! the program.

use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

use crate::source::CollectedSource;

const CONTROL_CACHE_FORMAT: u32 = 1;
const CONTROL_CACHE_SALT: &[u8] = b"yulang/control-vm-cache/v1";
const FNV_OFFSET: u64 = 0xcbf29ce484222325;
const FNV_PRIME: u64 = 0x100000001b3;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ControlArtifactCache {
    root: PathBuf,
}

impl ControlArtifactCache {
    pub fn new(root: impl Into<PathBuf>) -> Self {
        Self { root: root.into() }
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    pub fn control_artifact_path(&self, key: ControlCacheKey) -> PathBuf {
        self.control_artifact_dir()
            .join(format!("{}.json", key.to_hex()))
    }

    pub fn read_control_artifact(
        &self,
        key: ControlCacheKey,
    ) -> Result<Option<CachedControlArtifact>, CacheError> {
        let path = self.control_artifact_path(key);
        let source = match fs::read_to_string(&path) {
            Ok(source) => source,
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
            Err(error) => return Err(CacheError::Read { path, error }),
        };
        let envelope: ControlCacheEnvelope =
            serde_json::from_str(&source).map_err(|error| CacheError::Decode {
                path: path.clone(),
                error,
            })?;
        if envelope.format != CONTROL_CACHE_FORMAT {
            return Ok(None);
        }
        Ok(Some(CachedControlArtifact {
            program: envelope.program,
            file_count: envelope.file_count,
            errors: envelope.errors,
        }))
    }

    pub fn write_control_artifact(
        &self,
        key: ControlCacheKey,
        artifact: &CachedControlArtifact,
    ) -> Result<(), CacheError> {
        let path = self.control_artifact_path(key);
        let envelope = ControlCacheEnvelope {
            format: CONTROL_CACHE_FORMAT,
            program: artifact.program.clone(),
            file_count: artifact.file_count,
            errors: artifact.errors.clone(),
        };
        let mut source = serde_json::to_string(&envelope).map_err(|error| CacheError::Encode {
            path: path.clone(),
            error,
        })?;
        source.push('\n');

        let Some(parent) = path.parent() else {
            return Err(CacheError::NoParent { path });
        };
        fs::create_dir_all(parent).map_err(|error| CacheError::CreateDir {
            path: parent.to_path_buf(),
            error,
        })?;

        let tmp = path.with_extension(format!("json.tmp-{}", std::process::id()));
        fs::write(&tmp, source).map_err(|error| CacheError::Write {
            path: tmp.clone(),
            error,
        })?;
        if let Err(error) = fs::rename(&tmp, &path) {
            let _ = fs::remove_file(&tmp);
            return Err(CacheError::Rename {
                from: tmp,
                to: path,
                error,
            });
        }
        Ok(())
    }

    fn control_artifact_dir(&self) -> PathBuf {
        self.root.join("artifacts").join("control-vm")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct CachedControlArtifact {
    pub program: control_vm::Program,
    pub file_count: usize,
    pub errors: Vec<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ControlCacheKey {
    hash: u64,
}

impl ControlCacheKey {
    pub fn to_hex(self) -> String {
        format!("{:016x}", self.hash)
    }
}

pub fn control_cache_key(files: &[CollectedSource]) -> ControlCacheKey {
    let mut hasher = StableHasher::new();
    hasher.bytes(CONTROL_CACHE_SALT);
    hasher.usize(files.len());
    for file in files {
        hasher.string(&file.path.as_os_str().to_string_lossy());
        hasher.usize(file.module_path.segments.len());
        for segment in &file.module_path.segments {
            hasher.string(&segment.0);
        }
        hasher.string(&file.source);
    }
    ControlCacheKey {
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
        error: serde_json::Error,
    },
    Encode {
        path: PathBuf,
        error: serde_json::Error,
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
struct ControlCacheEnvelope {
    format: u32,
    program: control_vm::Program,
    file_count: usize,
    errors: Vec<String>,
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
    fn control_cache_key_tracks_source_path_and_module() {
        let base = source("main.yu", &[], "1\n");
        let same = source("main.yu", &[], "1\n");
        let changed_source = source("main.yu", &[], "2\n");
        let changed_path = source("other.yu", &[], "1\n");
        let changed_module = source("main.yu", &["app"], "1\n");

        assert_eq!(
            control_cache_key(&[base.clone()]),
            control_cache_key(&[same])
        );
        assert_ne!(
            control_cache_key(&[base.clone()]),
            control_cache_key(&[changed_source])
        );
        assert_ne!(
            control_cache_key(&[base.clone()]),
            control_cache_key(&[changed_path])
        );
        assert_ne!(
            control_cache_key(&[base]),
            control_cache_key(&[changed_module])
        );
    }

    #[test]
    fn control_cache_round_trips_artifact_envelope() {
        let root = temp_root("round-trip");
        let cache = ControlArtifactCache::new(&root);
        let key = control_cache_key(&[source("main.yu", &[], "1\n")]);
        let artifact = CachedControlArtifact {
            program: control_vm::Program::default(),
            file_count: 1,
            errors: vec!["lowering warning".to_string()],
        };

        cache.write_control_artifact(key, &artifact).unwrap();
        let restored = cache.read_control_artifact(key).unwrap().unwrap();

        assert_eq!(restored, artifact);
        assert!(cache.control_artifact_path(key).is_file());

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
