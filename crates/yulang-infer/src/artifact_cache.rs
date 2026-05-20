use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use yulang_sources::{
    COMPILED_UNIT_ARTIFACT_FORMAT_VERSION, COMPILED_UNIT_PARSER_FORMAT_VERSION,
    CompiledUnitManifest, YulangCachePaths,
};

use crate::source::{CompiledUnitArtifact, CompiledUnitArtifactBundle};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CompiledUnitArtifactCacheKey {
    pub artifact_format_version: u32,
    pub parser_format_version: u32,
    pub unit_index: usize,
    pub identity_hash: u64,
    pub source_hash: u64,
    pub syntax_hash: u64,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CompiledUnitArtifactBundleCacheKey {
    pub artifact_format_version: u32,
    pub parser_format_version: u32,
    pub unit_count: usize,
    pub manifest_hash: u64,
}

impl CompiledUnitArtifactCacheKey {
    pub fn from_manifest(manifest: &CompiledUnitManifest) -> Self {
        Self {
            artifact_format_version: manifest.artifact_format_version,
            parser_format_version: manifest.parser_format_version,
            unit_index: manifest.unit_index,
            identity_hash: hash_compiled_unit_identity(manifest),
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
            "unit-{}-{:016x}-{:016x}-{:016x}.json",
            self.unit_index, self.identity_hash, self.source_hash, self.syntax_hash
        )
    }
}

impl CompiledUnitArtifactBundleCacheKey {
    pub fn from_manifests(
        manifests: &[CompiledUnitManifest],
    ) -> Result<Self, CompiledUnitArtifactCacheError> {
        let Some(first) = manifests.first() else {
            return Err(CompiledUnitArtifactCacheError::EmptyBundle);
        };
        for manifest in manifests {
            validate_manifest_for_current_compiler(manifest)?;
            if manifest.artifact_format_version != first.artifact_format_version
                || manifest.parser_format_version != first.parser_format_version
            {
                return Err(CompiledUnitArtifactCacheError::UnsupportedFormat {
                    artifact_format_version: manifest.artifact_format_version,
                    parser_format_version: manifest.parser_format_version,
                });
            }
        }
        Ok(Self {
            artifact_format_version: first.artifact_format_version,
            parser_format_version: first.parser_format_version,
            unit_count: manifests.len(),
            manifest_hash: hash_compiled_unit_manifests(manifests),
        })
    }

    fn directory(&self, root: &Path) -> PathBuf {
        root.join(format!("v{}", self.artifact_format_version))
            .join(format!("parser-v{}", self.parser_format_version))
    }

    fn file_name(&self) -> String {
        format!("bundle-{}-{:016x}.bin", self.unit_count, self.manifest_hash)
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

    pub fn bundle_artifact_path(&self, key: &CompiledUnitArtifactBundleCacheKey) -> PathBuf {
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

    pub fn write_bundle(
        &self,
        bundle: &CompiledUnitArtifactBundle,
    ) -> Result<PathBuf, CompiledUnitArtifactCacheError> {
        let key = CompiledUnitArtifactBundleCacheKey::from_manifests(&bundle.manifests)?;
        let path = self.bundle_artifact_path(&key);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).map_err(|error| CompiledUnitArtifactCacheError::Io {
                path: parent.to_path_buf(),
                error: io_error_string(error),
            })?;
        }
        let bytes = postcard::to_allocvec(bundle).map_err(|error| {
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

    pub fn read_bundle(
        &self,
        key: &CompiledUnitArtifactBundleCacheKey,
    ) -> Result<CompiledUnitArtifactBundle, CompiledUnitArtifactCacheError> {
        validate_key_for_current_compiler_parts(
            key.artifact_format_version,
            key.parser_format_version,
        )?;
        let path = self.bundle_artifact_path(key);
        let bytes = fs::read(&path).map_err(|error| CompiledUnitArtifactCacheError::Io {
            path: path.clone(),
            error: io_error_string(error),
        })?;
        let bundle =
            postcard::from_bytes::<CompiledUnitArtifactBundle>(&bytes).map_err(|error| {
                CompiledUnitArtifactCacheError::Deserialize {
                    path: path.clone(),
                    error: error.to_string(),
                }
            })?;
        let actual = CompiledUnitArtifactBundleCacheKey::from_manifests(&bundle.manifests)?;
        if &actual != key {
            return Err(CompiledUnitArtifactCacheError::BundleKeyMismatch {
                path,
                expected: key.clone(),
                actual,
            });
        }
        Ok(bundle)
    }

    pub fn read_bundle_for_manifests(
        &self,
        manifests: &[CompiledUnitManifest],
    ) -> Result<CompiledUnitArtifactBundle, CompiledUnitArtifactCacheError> {
        self.read_bundle(&CompiledUnitArtifactBundleCacheKey::from_manifests(
            manifests,
        )?)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompiledUnitArtifactCacheError {
    EmptyBundle,
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
    BundleKeyMismatch {
        path: PathBuf,
        expected: CompiledUnitArtifactBundleCacheKey,
        actual: CompiledUnitArtifactBundleCacheKey,
    },
}

fn validate_key_for_current_compiler(
    key: &CompiledUnitArtifactCacheKey,
) -> Result<(), CompiledUnitArtifactCacheError> {
    validate_key_for_current_compiler_parts(key.artifact_format_version, key.parser_format_version)
}

fn validate_key_for_current_compiler_parts(
    artifact_format_version: u32,
    parser_format_version: u32,
) -> Result<(), CompiledUnitArtifactCacheError> {
    validate_versions(artifact_format_version, parser_format_version)
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

fn hash_compiled_unit_manifests(manifests: &[CompiledUnitManifest]) -> u64 {
    let mut hash = 0xcbf29ce484222325u64;
    hash_usize(&mut hash, manifests.len());
    for manifest in manifests {
        hash_u32(&mut hash, manifest.artifact_format_version);
        hash_u32(&mut hash, manifest.parser_format_version);
        hash_usize(&mut hash, manifest.unit_index);
        hash_u8(
            &mut hash,
            match manifest.origin {
                yulang_sources::SourceCompilationUnitOrigin::Entry => 0,
                yulang_sources::SourceCompilationUnitOrigin::Std => 1,
                yulang_sources::SourceCompilationUnitOrigin::User => 2,
                yulang_sources::SourceCompilationUnitOrigin::Mixed => 3,
            },
        );
        hash_manifest_realm_band_identity(&mut hash, manifest);
        hash_usize(&mut hash, manifest.files.len());
        for file in &manifest.files {
            hash_bytes(&mut hash, file.path.as_bytes());
            hash_usize(&mut hash, file.module_path.segments.len());
            for segment in &file.module_path.segments {
                hash_bytes(&mut hash, segment.0.as_bytes());
            }
            hash_u8(
                &mut hash,
                match file.origin {
                    yulang_sources::SourceOrigin::Entry => 0,
                    yulang_sources::SourceOrigin::Std => 1,
                    yulang_sources::SourceOrigin::User => 2,
                },
            );
            hash_usize(&mut hash, file.source_len);
            hash_u64(&mut hash, file.source_hash);
        }
        hash_usize(&mut hash, manifest.dependencies.len());
        for dependency in &manifest.dependencies {
            hash_usize(&mut hash, dependency.unit_index);
            hash_u64(&mut hash, dependency.source_hash);
            hash_u64(&mut hash, dependency.interface_hash);
        }
        hash_u64(&mut hash, manifest.source_hash);
        hash_u64(&mut hash, manifest.syntax_hash);
        hash_u64(&mut hash, manifest.interface_hash);
    }
    hash
}

fn hash_compiled_unit_identity(manifest: &CompiledUnitManifest) -> u64 {
    let mut hash = 0xcbf29ce484222325u64;
    hash_manifest_realm_band_identity(&mut hash, manifest);
    hash
}

fn hash_manifest_realm_band_identity(hash: &mut u64, manifest: &CompiledUnitManifest) {
    hash_usize(hash, manifest.realms.len());
    for realm in &manifest.realms {
        hash_bytes(hash, realm.identity.0.as_bytes());
        match &realm.version {
            Some(version) => {
                hash_u8(hash, 1);
                hash_bytes(hash, version.0.as_bytes());
            }
            None => hash_u8(hash, 0),
        }
    }
    hash_usize(hash, manifest.bands.len());
    for band in &manifest.bands {
        hash_bytes(hash, band.realm.identity.0.as_bytes());
        match &band.realm.version {
            Some(version) => {
                hash_u8(hash, 1);
                hash_bytes(hash, version.0.as_bytes());
            }
            None => hash_u8(hash, 0),
        }
        hash_usize(hash, band.band.segments.len());
        for segment in &band.band.segments {
            hash_bytes(hash, segment.0.as_bytes());
        }
    }
}

fn hash_usize(hash: &mut u64, value: usize) {
    hash_u64(hash, value as u64);
}

fn hash_u32(hash: &mut u64, value: u32) {
    hash_u64(hash, value as u64);
}

fn hash_u8(hash: &mut u64, value: u8) {
    hash_bytes(hash, &[value]);
}

fn hash_u64(hash: &mut u64, value: u64) {
    hash_bytes(hash, &value.to_le_bytes());
}

fn hash_bytes(hash: &mut u64, bytes: &[u8]) {
    for byte in bytes {
        *hash ^= u64::from(*byte);
        *hash = hash.wrapping_mul(0x100000001b3);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source::{CompiledRuntimeSurface, CompiledTypedSurface, CompiledUnitArtifactBundle};
    use yulang_sources::{
        BandPath, CompiledSourceFileIdentity, CompiledSyntaxSurface, RealmIdentity, ResolvedBandId,
        ResolvedRealmId, SourceCompilationUnitOrigin, SourceOrigin,
    };
    use yulang_typed_ir::CoreProgram;
    use yulang_typed_ir::Name;

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
    fn writes_and_reads_compiled_unit_artifact_bundle() {
        let root = temp_root("compiled-unit-bundle-cache-round-trip");
        let _ = fs::remove_dir_all(&root);
        let cache = CompiledUnitArtifactCache::new(&root);
        let bundle = test_bundle();
        let key = CompiledUnitArtifactBundleCacheKey::from_manifests(&bundle.manifests).unwrap();

        let path = cache.write_bundle(&bundle).unwrap();
        assert_eq!(path, cache.bundle_artifact_path(&key));
        let read = cache.read_bundle(&key).unwrap();

        assert_eq!(read, bundle);
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn rejects_bundle_with_wrong_manifest_key() {
        let root = temp_root("compiled-unit-bundle-cache-key-mismatch");
        let _ = fs::remove_dir_all(&root);
        let cache = CompiledUnitArtifactCache::new(&root);
        let bundle = test_bundle();
        let mut wrong_manifests = bundle.manifests.clone();
        wrong_manifests[0].syntax_hash = 99;
        let wrong = CompiledUnitArtifactBundleCacheKey::from_manifests(&wrong_manifests).unwrap();
        let wrong_path = cache.bundle_artifact_path(&wrong);
        fs::create_dir_all(wrong_path.parent().unwrap()).unwrap();
        fs::write(&wrong_path, postcard::to_allocvec(&bundle).unwrap()).unwrap();

        let err = cache.read_bundle(&wrong).unwrap_err();

        assert!(matches!(
            err,
            CompiledUnitArtifactCacheError::BundleKeyMismatch { .. }
        ));
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
    fn artifact_key_includes_realm_band_identity() {
        let first = test_artifact(11, 22);
        let mut second = test_artifact(11, 22);
        second.manifest.realms[0].identity.0 = "virtual:other".to_string();
        second.manifest.bands[0].realm = second.manifest.realms[0].clone();

        assert_ne!(
            CompiledUnitArtifactCacheKey::from_manifest(&first.manifest),
            CompiledUnitArtifactCacheKey::from_manifest(&second.manifest)
        );
    }

    #[test]
    fn rejects_unsupported_versions() {
        let cache = CompiledUnitArtifactCache::new(temp_root("compiled-unit-cache-version"));
        let key = CompiledUnitArtifactCacheKey {
            artifact_format_version: COMPILED_UNIT_ARTIFACT_FORMAT_VERSION + 1,
            parser_format_version: COMPILED_UNIT_PARSER_FORMAT_VERSION,
            unit_index: 0,
            identity_hash: 0,
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
                realms: vec![test_realm()],
                bands: vec![test_band()],
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
                interface_hash: syntax_hash,
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

    fn test_realm() -> ResolvedRealmId {
        ResolvedRealmId {
            identity: RealmIdentity("virtual:test".to_string()),
            version: None,
        }
    }

    fn test_band() -> ResolvedBandId {
        ResolvedBandId {
            realm: test_realm(),
            band: BandPath::from_segments(vec![Name("main".to_string())]),
        }
    }

    fn test_bundle() -> CompiledUnitArtifactBundle {
        CompiledUnitArtifactBundle {
            manifests: vec![
                test_artifact(11, 22).manifest,
                test_artifact(33, 44).manifest,
            ],
            namespace: Default::default(),
            typed: CompiledTypedSurface::default(),
            runtime: Default::default(),
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
