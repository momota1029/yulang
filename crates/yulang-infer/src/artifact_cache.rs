use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use yulang_sources::{
    COMPILED_UNIT_ARTIFACT_FORMAT_VERSION, COMPILED_UNIT_PARSER_FORMAT_VERSION,
    CompiledUnitManifest, YulangCachePaths,
};

use crate::source::CompiledUnitArtifact;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CompiledUnitArtifactCacheKey {
    pub artifact_format_version: u32,
    pub parser_format_version: u32,
    pub unit_index: usize,
    pub source_hash: u64,
    pub syntax_hash: u64,
}

impl CompiledUnitArtifactCacheKey {
    pub fn from_manifest(manifest: &CompiledUnitManifest) -> Self {
        Self {
            artifact_format_version: manifest.artifact_format_version,
            parser_format_version: manifest.parser_format_version,
            unit_index: manifest.unit_index,
            source_hash: manifest.source_hash,
            syntax_hash: manifest.syntax_hash,
        }
    }

    fn directory(&self, root: &Path) -> PathBuf {
        root.join(format!("v{}", self.artifact_format_version))
            .join(format!("parser-v{}", self.parser_format_version))
    }

    fn file_name(&self) -> String {
        format!(
            "unit-{}-{:016x}-{:016x}.json",
            self.unit_index, self.source_hash, self.syntax_hash
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompiledUnitArtifactCache {
    root: PathBuf,
}

impl CompiledUnitArtifactCache {
    pub fn new(root: impl Into<PathBuf>) -> Self {
        Self { root: root.into() }
    }

    pub fn from_paths(paths: &YulangCachePaths) -> Self {
        Self::new(paths.compiled_units.clone())
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    pub fn artifact_path(&self, key: &CompiledUnitArtifactCacheKey) -> PathBuf {
        key.directory(&self.root).join(key.file_name())
    }

    pub fn write(
        &self,
        artifact: &CompiledUnitArtifact,
    ) -> Result<PathBuf, CompiledUnitArtifactCacheError> {
        validate_manifest_for_current_compiler(&artifact.manifest)?;
        let key = CompiledUnitArtifactCacheKey::from_manifest(&artifact.manifest);
        let path = self.artifact_path(&key);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).map_err(|error| CompiledUnitArtifactCacheError::Io {
                path: parent.to_path_buf(),
                error: io_error_string(error),
            })?;
        }
        let bytes = serde_json::to_vec(artifact).map_err(|error| {
            CompiledUnitArtifactCacheError::Serialize {
                error: error.to_string(),
            }
        })?;
        fs::write(&path, bytes).map_err(|error| CompiledUnitArtifactCacheError::Io {
            path: path.clone(),
            error: io_error_string(error),
        })?;
        Ok(path)
    }

    pub fn read(
        &self,
        key: &CompiledUnitArtifactCacheKey,
    ) -> Result<CompiledUnitArtifact, CompiledUnitArtifactCacheError> {
        validate_key_for_current_compiler(key)?;
        let path = self.artifact_path(key);
        let bytes = fs::read(&path).map_err(|error| CompiledUnitArtifactCacheError::Io {
            path: path.clone(),
            error: io_error_string(error),
        })?;
        let artifact = serde_json::from_slice::<CompiledUnitArtifact>(&bytes).map_err(|error| {
            CompiledUnitArtifactCacheError::Deserialize {
                path: path.clone(),
                error: error.to_string(),
            }
        })?;
        let actual = CompiledUnitArtifactCacheKey::from_manifest(&artifact.manifest);
        if &actual != key {
            return Err(CompiledUnitArtifactCacheError::KeyMismatch {
                path,
                expected: key.clone(),
                actual,
            });
        }
        validate_manifest_for_current_compiler(&artifact.manifest)?;
        Ok(artifact)
    }

    pub fn read_for_manifest(
        &self,
        manifest: &CompiledUnitManifest,
    ) -> Result<CompiledUnitArtifact, CompiledUnitArtifactCacheError> {
        self.read(&CompiledUnitArtifactCacheKey::from_manifest(manifest))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompiledUnitArtifactCacheError {
    Io {
        path: PathBuf,
        error: String,
    },
    Serialize {
        error: String,
    },
    Deserialize {
        path: PathBuf,
        error: String,
    },
    UnsupportedFormat {
        artifact_format_version: u32,
        parser_format_version: u32,
    },
    KeyMismatch {
        path: PathBuf,
        expected: CompiledUnitArtifactCacheKey,
        actual: CompiledUnitArtifactCacheKey,
    },
}

fn validate_key_for_current_compiler(
    key: &CompiledUnitArtifactCacheKey,
) -> Result<(), CompiledUnitArtifactCacheError> {
    validate_versions(key.artifact_format_version, key.parser_format_version)
}

fn validate_manifest_for_current_compiler(
    manifest: &CompiledUnitManifest,
) -> Result<(), CompiledUnitArtifactCacheError> {
    validate_versions(
        manifest.artifact_format_version,
        manifest.parser_format_version,
    )
}

fn validate_versions(
    artifact_format_version: u32,
    parser_format_version: u32,
) -> Result<(), CompiledUnitArtifactCacheError> {
    if artifact_format_version != COMPILED_UNIT_ARTIFACT_FORMAT_VERSION
        || parser_format_version != COMPILED_UNIT_PARSER_FORMAT_VERSION
    {
        return Err(CompiledUnitArtifactCacheError::UnsupportedFormat {
            artifact_format_version,
            parser_format_version,
        });
    }
    Ok(())
}

fn io_error_string(error: io::Error) -> String {
    error.to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source::{CompiledRuntimeSurface, CompiledTypedSurface};
    use yulang_sources::{
        CompiledSourceFileIdentity, CompiledSyntaxSurface, SourceCompilationUnitOrigin,
        SourceOrigin,
    };
    use yulang_typed_ir::CoreProgram;

    #[test]
    fn writes_and_reads_compiled_unit_artifact() {
        let root = temp_root("compiled-unit-cache-round-trip");
        let _ = fs::remove_dir_all(&root);
        let cache = CompiledUnitArtifactCache::new(&root);
        let artifact = test_artifact(11, 22);
        let key = CompiledUnitArtifactCacheKey::from_manifest(&artifact.manifest);

        let path = cache.write(&artifact).unwrap();
        assert_eq!(path, cache.artifact_path(&key));
        let read = cache.read(&key).unwrap();

        assert_eq!(read, artifact);
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn rejects_artifact_with_wrong_manifest_key() {
        let root = temp_root("compiled-unit-cache-key-mismatch");
        let _ = fs::remove_dir_all(&root);
        let cache = CompiledUnitArtifactCache::new(&root);
        let artifact = test_artifact(11, 22);
        let mut wrong = CompiledUnitArtifactCacheKey::from_manifest(&artifact.manifest);
        wrong.syntax_hash = 99;
        let wrong_path = cache.artifact_path(&wrong);
        fs::create_dir_all(wrong_path.parent().unwrap()).unwrap();
        fs::write(&wrong_path, serde_json::to_vec(&artifact).unwrap()).unwrap();

        let err = cache.read(&wrong).unwrap_err();

        assert!(matches!(
            err,
            CompiledUnitArtifactCacheError::KeyMismatch { .. }
        ));
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn rejects_unsupported_versions() {
        let cache = CompiledUnitArtifactCache::new(temp_root("compiled-unit-cache-version"));
        let key = CompiledUnitArtifactCacheKey {
            artifact_format_version: COMPILED_UNIT_ARTIFACT_FORMAT_VERSION + 1,
            parser_format_version: COMPILED_UNIT_PARSER_FORMAT_VERSION,
            unit_index: 0,
            source_hash: 1,
            syntax_hash: 2,
        };

        let err = cache.read(&key).unwrap_err();

        assert!(matches!(
            err,
            CompiledUnitArtifactCacheError::UnsupportedFormat { .. }
        ));
    }

    fn test_artifact(source_hash: u64, syntax_hash: u64) -> CompiledUnitArtifact {
        CompiledUnitArtifact {
            manifest: CompiledUnitManifest {
                artifact_format_version: COMPILED_UNIT_ARTIFACT_FORMAT_VERSION,
                parser_format_version: COMPILED_UNIT_PARSER_FORMAT_VERSION,
                unit_index: 0,
                origin: SourceCompilationUnitOrigin::Entry,
                files: vec![CompiledSourceFileIdentity {
                    path: "main.yu".to_string(),
                    module_path: Default::default(),
                    origin: SourceOrigin::Entry,
                    source_len: 1,
                    source_hash,
                }],
                dependencies: Vec::new(),
                source_hash,
                syntax_hash,
            },
            syntax: CompiledSyntaxSurface {
                modules: Vec::new(),
                direct_exports: Vec::new(),
                public_exports: Vec::new(),
            },
            namespace: Default::default(),
            typed: CompiledTypedSurface::default(),
            runtime: CompiledRuntimeSurface {
                program: CoreProgram::default(),
            },
        }
    }

    fn temp_root(name: &str) -> PathBuf {
        std::env::temp_dir().join(format!(
            "yulang-infer-{name}-{}",
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ))
    }
}
