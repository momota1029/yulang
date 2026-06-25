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
const COMPILED_UNIT_CACHE_FORMAT: u32 = 2;
// Bump when compiler/cache semantics change without a serialized envelope bump.
const CACHE_SCHEMA_VERSION: u32 = 1;
const SOURCE_CACHE_SALT: &[u8] = b"yulang/source-set-cache/v2";
const SOURCE_FILE_HASH_SALT: &[u8] = b"yulang/source-file/v1";
const COMPILED_SYNTAX_HASH_SALT: &[u8] = b"yulang/compiled-syntax-surface/v1";
const COMPILED_NAMESPACE_HASH_SALT: &[u8] = b"yulang/compiled-namespace-surface/v1";
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

    pub fn compiled_unit_artifact_path(&self, key: SourceCacheKey) -> PathBuf {
        self.artifact_dir("compiled-unit")
            .join(format!("{}.yuunit", key.to_hex()))
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

    pub fn read_compiled_unit_artifact(
        &self,
        key: SourceCacheKey,
    ) -> Result<Option<CachedCompiledUnitArtifact>, CacheError> {
        let path = self.compiled_unit_artifact_path(key);
        let Some(envelope): Option<CompiledUnitCacheEnvelope> =
            read_cache_envelope(&path, COMPILED_UNIT_CACHE_FORMAT)?
        else {
            return Ok(None);
        };
        Ok(Some(CachedCompiledUnitArtifact {
            manifest: envelope.manifest,
            syntax: envelope.syntax,
            namespace: envelope.namespace,
        }))
    }

    pub fn write_compiled_unit_artifact(
        &self,
        key: SourceCacheKey,
        artifact: &CachedCompiledUnitArtifact,
    ) -> Result<(), CacheError> {
        let path = self.compiled_unit_artifact_path(key);
        let envelope = CompiledUnitCacheEnvelope {
            format: COMPILED_UNIT_CACHE_FORMAT,
            manifest: &artifact.manifest,
            syntax: &artifact.syntax,
            namespace: &artifact.namespace,
        };
        write_cache_envelope(&path, "yuunit", &envelope)
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CachedCompiledUnitArtifact {
    pub manifest: CompiledUnitManifest,
    pub syntax: sources::CompiledSyntaxSurface,
    pub namespace: infer::CompiledNamespaceSurface,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledUnitManifest {
    pub cache_schema_version: u32,
    pub compiled_unit_format: u32,
    pub source_hash: u64,
    pub syntax_hash: u64,
    pub namespace_hash: u64,
    pub files: Vec<CompiledUnitSourceFile>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledUnitSourceFile {
    pub path: String,
    pub module_path: Vec<String>,
    pub source_len: usize,
    pub source_hash: u64,
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

pub fn compiled_unit_artifact_from_loaded_files(
    files: &[CollectedSource],
    loaded: &[sources::LoadedFile],
) -> Result<CachedCompiledUnitArtifact, infer::LoadedFilesError> {
    let syntax = sources::CompiledSyntaxSurface::from_loaded_files(loaded);
    let namespace = infer::CompiledNamespaceSurface::from_loaded_files(loaded)?;
    let manifest = compiled_unit_manifest(files, &syntax, &namespace);
    Ok(CachedCompiledUnitArtifact {
        manifest,
        syntax,
        namespace,
    })
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

fn compiled_unit_manifest(
    files: &[CollectedSource],
    syntax: &sources::CompiledSyntaxSurface,
    namespace: &infer::CompiledNamespaceSurface,
) -> CompiledUnitManifest {
    CompiledUnitManifest {
        cache_schema_version: CACHE_SCHEMA_VERSION,
        compiled_unit_format: COMPILED_UNIT_CACHE_FORMAT,
        source_hash: source_cache_key(files).hash,
        syntax_hash: compiled_syntax_hash(syntax),
        namespace_hash: compiled_namespace_hash(namespace),
        files: files
            .iter()
            .map(|file| CompiledUnitSourceFile {
                path: file.path.as_os_str().to_string_lossy().into_owned(),
                module_path: file
                    .module_path
                    .segments
                    .iter()
                    .map(|segment| segment.0.clone())
                    .collect(),
                source_len: file.source.len(),
                source_hash: source_file_hash(file),
            })
            .collect(),
    }
}

fn source_file_hash(file: &CollectedSource) -> u64 {
    let mut hasher = StableHasher::new();
    hasher.bytes(SOURCE_FILE_HASH_SALT);
    hasher.string(&file.path.as_os_str().to_string_lossy());
    hasher.usize(file.module_path.segments.len());
    for segment in &file.module_path.segments {
        hasher.string(&segment.0);
    }
    hasher.string(&file.source);
    hasher.finish()
}

fn compiled_syntax_hash(syntax: &sources::CompiledSyntaxSurface) -> u64 {
    let mut hasher = StableHasher::new();
    hasher.bytes(COMPILED_SYNTAX_HASH_SALT);
    hasher.usize(syntax.files.len());
    for file in &syntax.files {
        hash_module_path(&mut hasher, &file.module_path);
        hasher.usize(file.uses.len());
        for use_decl in &file.uses {
            hash_visibility(&mut hasher, use_decl.visibility);
            hash_use_import(&mut hasher, &use_decl.import);
        }
        hasher.usize(file.ops.len());
        for op in &file.ops {
            hash_visibility(&mut hasher, op.visibility);
            hasher.string(&op.name.0);
            hash_compiled_op_def(&mut hasher, &op.op);
        }
        hasher.usize(file.module_loads.len());
        for request in &file.module_loads {
            hash_module_path(&mut hasher, &request.parent);
            hasher.string(&request.name.0);
            hash_module_load_kind(&mut hasher, request.kind);
        }
    }
    hasher.finish()
}

fn compiled_namespace_hash(namespace: &infer::CompiledNamespaceSurface) -> u64 {
    let mut hasher = StableHasher::new();
    hasher.bytes(COMPILED_NAMESPACE_HASH_SALT);

    hasher.usize(namespace.modules.len());
    for module in &namespace.modules {
        hasher.u32(module.id);
        hash_string_path(&mut hasher, &module.path);
        hash_optional_compiled_namespace_visibility(&mut hasher, module.visibility);

        hasher.usize(module.values.len());
        for value in &module.values {
            hasher.string(&value.name);
            hasher.u32(value.symbol);
            hash_compiled_namespace_visibility(&mut hasher, value.visibility);
            hasher.u32(value.order);
            hasher.bool(value.lazy);
        }

        hasher.usize(module.types.len());
        for ty in &module.types {
            hasher.string(&ty.name);
            hasher.u32(ty.symbol);
            hash_compiled_namespace_visibility(&mut hasher, ty.visibility);
            hasher.u32(ty.order);
            hash_compiled_namespace_type_kind(&mut hasher, ty.kind);
        }

        hasher.usize(module.modules.len());
        for child in &module.modules {
            hasher.string(&child.name);
            hasher.u32(child.module);
            hash_string_path(&mut hasher, &child.module_path);
            hash_compiled_namespace_visibility(&mut hasher, child.visibility);
            hasher.u32(child.order);
        }

        hasher.usize(module.imported_values.len());
        for value in &module.imported_values {
            hasher.string(&value.name);
            hasher.u32(value.symbol);
            hash_compiled_namespace_visibility(&mut hasher, value.visibility);
            hasher.u32(value.order);
        }

        hasher.usize(module.imported_types.len());
        for ty in &module.imported_types {
            hasher.string(&ty.name);
            hasher.u32(ty.symbol);
            hash_compiled_namespace_visibility(&mut hasher, ty.visibility);
            hasher.u32(ty.order);
            hash_compiled_namespace_type_kind(&mut hasher, ty.kind);
        }

        hasher.usize(module.imported_modules.len());
        for child in &module.imported_modules {
            hasher.string(&child.name);
            hasher.u32(child.module);
            hash_string_path(&mut hasher, &child.module_path);
            hash_compiled_namespace_visibility(&mut hasher, child.visibility);
            hasher.u32(child.order);
        }

        hasher.usize(module.aliases.len());
        for alias in &module.aliases {
            hash_compiled_namespace_visibility(&mut hasher, alias.visibility);
            hasher.u32(alias.order);
            hash_use_import(&mut hasher, &alias.import);
        }
    }

    hasher.usize(namespace.values.len());
    for value in &namespace.values {
        hasher.u32(value.unit_id);
        hash_string_path(&mut hasher, &value.path);
    }

    hasher.usize(namespace.types.len());
    for ty in &namespace.types {
        hasher.u32(ty.unit_id);
        hash_string_path(&mut hasher, &ty.path);
        hash_compiled_namespace_type_kind(&mut hasher, ty.kind);
    }

    hasher.finish()
}

fn hash_module_path(hasher: &mut StableHasher, path: &sources::Path) {
    hasher.usize(path.segments.len());
    for segment in &path.segments {
        hasher.string(&segment.0);
    }
}

fn hash_string_path(hasher: &mut StableHasher, path: &[String]) {
    hasher.usize(path.len());
    for segment in path {
        hasher.string(segment);
    }
}

fn hash_visibility(hasher: &mut StableHasher, visibility: sources::Visibility) {
    hasher.u8(match visibility {
        sources::Visibility::Pub => 0,
        sources::Visibility::Our => 1,
        sources::Visibility::My => 2,
    });
}

fn hash_optional_compiled_namespace_visibility(
    hasher: &mut StableHasher,
    visibility: Option<infer::CompiledNamespaceVisibility>,
) {
    match visibility {
        Some(visibility) => {
            hasher.bool(true);
            hash_compiled_namespace_visibility(hasher, visibility);
        }
        None => hasher.bool(false),
    }
}

fn hash_compiled_namespace_visibility(
    hasher: &mut StableHasher,
    visibility: infer::CompiledNamespaceVisibility,
) {
    hasher.u8(match visibility {
        infer::CompiledNamespaceVisibility::Pub => 0,
        infer::CompiledNamespaceVisibility::Our => 1,
        infer::CompiledNamespaceVisibility::My => 2,
    });
}

fn hash_compiled_namespace_type_kind(
    hasher: &mut StableHasher,
    kind: infer::CompiledNamespaceTypeKind,
) {
    hasher.u8(match kind {
        infer::CompiledNamespaceTypeKind::TypeAlias => 0,
        infer::CompiledNamespaceTypeKind::Struct => 1,
        infer::CompiledNamespaceTypeKind::Enum => 2,
        infer::CompiledNamespaceTypeKind::Error => 3,
        infer::CompiledNamespaceTypeKind::Role => 4,
        infer::CompiledNamespaceTypeKind::Act => 5,
    });
}

fn hash_use_import(hasher: &mut StableHasher, import: &sources::UseImport) {
    match import {
        sources::UseImport::Alias { name, path } => {
            hasher.u8(0);
            hasher.string(&name.0);
            hash_module_path(hasher, path);
        }
        sources::UseImport::Glob { prefix } => {
            hasher.u8(1);
            hash_module_path(hasher, prefix);
        }
    }
}

fn hash_module_load_kind(hasher: &mut StableHasher, kind: sources::ModuleLoadKind) {
    hasher.u8(match kind {
        sources::ModuleLoadKind::ModDecl => 0,
        sources::ModuleLoadKind::UseMod => 1,
    });
}

fn hash_compiled_op_def(hasher: &mut StableHasher, op: &sources::CompiledOpDef) {
    hash_optional_bp(hasher, op.prefix.as_deref());
    match op.infix.as_ref() {
        Some((left, right)) => {
            hasher.bool(true);
            hash_bp(hasher, left);
            hash_bp(hasher, right);
        }
        None => hasher.bool(false),
    }
    hash_optional_bp(hasher, op.suffix.as_deref());
    hasher.bool(op.nullfix);
}

fn hash_optional_bp(hasher: &mut StableHasher, bp: Option<&[i8]>) {
    match bp {
        Some(bp) => {
            hasher.bool(true);
            hash_bp(hasher, bp);
        }
        None => hasher.bool(false),
    }
}

fn hash_bp(hasher: &mut StableHasher, bp: &[i8]) {
    hasher.usize(bp.len());
    for value in bp {
        hasher.i8(*value);
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

#[derive(Debug, Clone, Serialize, Deserialize)]
struct CompiledUnitCacheEnvelope<
    M = CompiledUnitManifest,
    S = sources::CompiledSyntaxSurface,
    N = infer::CompiledNamespaceSurface,
> {
    format: u32,
    manifest: M,
    syntax: S,
    namespace: N,
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

impl<T, L, E> CacheEnvelope for PolyCacheEnvelope<T, L, E> {
    fn format(&self) -> u32 {
        self.format
    }
}

impl<T, L, E> CacheEnvelope for ControlCacheEnvelope<T, L, E> {
    fn format(&self) -> u32 {
        self.format
    }
}

impl<M, S, N> CacheEnvelope for CompiledUnitCacheEnvelope<M, S, N> {
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

    fn u8(&mut self, value: u8) {
        self.raw_bytes(&[value]);
    }

    fn i8(&mut self, value: i8) {
        self.raw_bytes(&value.to_le_bytes());
    }

    fn bool(&mut self, value: bool) {
        self.u8(u8::from(value));
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

    #[test]
    fn compiled_unit_cache_round_trips_manifest_and_syntax_surface() {
        let root = temp_root("compiled-unit-round-trip");
        let cache = ArtifactCache::new(&root);
        let files = vec![
            source("main.yu", &[], "mod ops;\n"),
            source(
                "ops.yu",
                &["ops"],
                "pub infix (<+>) 50 50 = add\nmy hidden = 1\n",
            ),
        ];
        let loaded = sources::load(collected_to_source_files(files.clone()));
        let key = source_cache_key(&files);
        let artifact = compiled_unit_artifact_from_loaded_files(&files, &loaded).unwrap();

        cache.write_compiled_unit_artifact(key, &artifact).unwrap();
        let restored = cache.read_compiled_unit_artifact(key).unwrap().unwrap();

        assert_eq!(restored, artifact);
        assert_eq!(restored.manifest.files.len(), 2);
        assert_eq!(restored.manifest.files[1].module_path, vec!["ops"]);
        let ops_path = vec!["ops".to_string()];
        let ops_syntax = restored
            .syntax
            .files
            .iter()
            .find(|file| infer::namespace_path(&file.module_path) == ops_path)
            .unwrap();
        assert_eq!(ops_syntax.ops.len(), 1);
        let ops_module = restored
            .namespace
            .modules
            .iter()
            .find(|module| module.path == ops_path)
            .unwrap();
        assert!(
            ops_module
                .values
                .iter()
                .any(|value| value.name == "#op:infix:<+>"
                    && value.visibility == infer::CompiledNamespaceVisibility::Pub)
        );
        assert!(ops_module.values.iter().any(|value| value.name == "hidden"
            && value.visibility == infer::CompiledNamespaceVisibility::My));
        assert!(cache.compiled_unit_artifact_path(key).is_file());
        assert_eq!(
            cache.compiled_unit_artifact_path(key).extension().unwrap(),
            "yuunit"
        );

        let suffix = sources::load_suffix_with_syntax_prefix(
            &restored.syntax,
            vec![sources::SourceFile {
                module_path: sources::Path::default(),
                source: "use ops::*\nmy y = 1 <+> 2\n".into(),
            }],
        );
        assert!(
            suffix[0].op_table.0.get("<+>".as_bytes()).is_some(),
            "cached syntax surface should rebuild downstream parser operators"
        );

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

    fn collected_to_source_files(files: Vec<CollectedSource>) -> Vec<sources::SourceFile> {
        files
            .into_iter()
            .map(|file| sources::SourceFile {
                module_path: file.module_path,
                source: file.source,
            })
            .collect()
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
