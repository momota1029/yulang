//! Persistent artifact cache used by the `yulang` CLI.
//!
//! The cache starts after source collection. It deliberately avoids owning the
//! collector or std lookup rules so a cache hit cannot change which files form
//! the program.

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};

use crate::source::{
    CollectedSource, SourceCompilationUnits, SourceUnitCacheSelection,
    SourceUnitLoweringInputError, source_unit_closure_file_indices,
    source_unit_closure_lowering_loaded_files, source_unit_lowering_loaded_files,
};

const POLY_CACHE_FORMAT: u32 = 7;
const MONO_CACHE_FORMAT: u32 = 1;
const CONTROL_CACHE_FORMAT: u32 = 7;
const COMPILED_UNIT_CACHE_FORMAT: u32 = 17;
const REALM_RESOLUTION_CACHE_FORMAT: u32 = 1;
// Bump when compiler/cache semantics change without a serialized envelope bump.
const CACHE_SCHEMA_VERSION: u32 = 4;
const SOURCE_CACHE_SALT: &[u8] = b"yulang/source-set-cache/v3";
const SOURCE_UNIT_CACHE_SALT: &[u8] = b"yulang/source-unit-cache/v2";
const REALM_CACHE_COMPONENT_SALT: &[u8] = b"yulang/realm-cache-component/v1";
const REALM_RESOLUTION_CACHE_SALT: &[u8] = b"yulang/realm-resolution-cache/v2";
const MERGED_COMPILED_UNIT_CACHE_SALT: &[u8] = b"yulang/merged-compiled-unit-cache/v1";
const SOURCE_FILE_HASH_SALT: &[u8] = b"yulang/source-file/v2";
const COMPILED_SYNTAX_HASH_SALT: &[u8] = b"yulang/compiled-syntax-surface/v2";
const COMPILED_NAMESPACE_HASH_SALT: &[u8] = b"yulang/compiled-namespace-surface/v2";
const COMPILED_LOWERING_HASH_SALT: &[u8] = b"yulang/compiled-lowering-surface/v4";
const COMPILED_TYPED_HASH_SALT: &[u8] = b"yulang/compiled-typed-surface/v1";
const COMPILED_RUNTIME_HASH_SALT: &[u8] = b"yulang/compiled-runtime-surface/v3";
const COMPILED_EXTERNAL_RUNTIME_HASH_SALT: &[u8] = b"yulang/compiled-external-runtime-refs/v2";
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

    pub fn mono_artifact_path(&self, key: SourceCacheKey) -> PathBuf {
        self.artifact_dir("mono")
            .join(format!("{}.yumo", key.to_hex()))
    }

    pub fn compiled_unit_artifact_path(&self, key: SourceCacheKey) -> PathBuf {
        self.artifact_dir("compiled-unit")
            .join(format!("{}.yucu", key.to_hex()))
    }

    pub fn realm_resolution_artifact_path(
        &self,
        source_realm: &sources::ResolvedRealmId,
        key: RealmResolutionCacheKey,
    ) -> PathBuf {
        self.realm_dir(source_realm)
            .join("resolution")
            .join(format!("{}.yures", key.to_hex()))
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

    pub fn read_mono_artifact(
        &self,
        key: SourceCacheKey,
    ) -> Result<Option<CachedMonoArtifact>, CacheError> {
        let path = self.mono_artifact_path(key);
        let Some(envelope): Option<MonoCacheEnvelope> =
            read_cache_envelope(&path, MONO_CACHE_FORMAT)?
        else {
            return Ok(None);
        };
        Ok(Some(CachedMonoArtifact {
            program: envelope.program,
            file_count: envelope.file_count,
            errors: envelope.errors,
        }))
    }

    pub fn write_mono_artifact(
        &self,
        key: SourceCacheKey,
        artifact: &CachedMonoArtifact,
    ) -> Result<(), CacheError> {
        let path = self.mono_artifact_path(key);
        let envelope = MonoCacheEnvelope {
            format: MONO_CACHE_FORMAT,
            program: &artifact.program,
            file_count: artifact.file_count,
            errors: &artifact.errors,
        };
        write_cache_envelope(&path, "yumo", &envelope)
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
        if !compiled_unit_envelope_matches_key(key, &envelope) {
            return Ok(None);
        }
        Ok(Some(cached_compiled_unit_artifact_from_envelope(envelope)))
    }

    pub fn read_source_unit_compiled_artifacts(
        &self,
        files: &[CollectedSource],
        units: &SourceCompilationUnits,
    ) -> Result<CachedSourceUnitCompiledArtifacts, CacheError> {
        let keys = source_compilation_unit_cache_keys(files, units);
        let mut artifacts = Vec::with_capacity(keys.len());
        let mut available = Vec::with_capacity(keys.len());

        for key in &keys {
            let artifact = self.read_compiled_unit_artifact(*key)?;
            available.push(artifact.is_some());
            artifacts.push(artifact);
        }

        Ok(CachedSourceUnitCompiledArtifacts {
            selection: units.cache_selection(&available),
            keys,
            artifacts,
        })
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
            lowering: &artifact.lowering,
            typed: &artifact.typed,
            runtime: &artifact.runtime,
            external_runtime: &artifact.external_runtime,
            errors: &artifact.errors,
        };
        write_cache_envelope(&path, "yucu", &envelope)
    }

    pub fn read_realm_resolution_artifact(
        &self,
        source_realm: &sources::ResolvedRealmId,
        key: RealmResolutionCacheKey,
    ) -> Result<Option<CachedRealmResolutionArtifact>, CacheError> {
        let path = self.realm_resolution_artifact_path(source_realm, key);
        let Some(envelope): Option<RealmResolutionCacheEnvelope> =
            read_cache_envelope(&path, REALM_RESOLUTION_CACHE_FORMAT)?
        else {
            return Ok(None);
        };
        if envelope.key_hash != key.hash {
            return Ok(None);
        }
        if envelope.source_realm != *source_realm {
            return Ok(None);
        }
        Ok(Some(CachedRealmResolutionArtifact {
            source_realm: envelope.source_realm,
            request: envelope.request,
            target: envelope.target,
        }))
    }

    pub fn write_realm_resolution_artifact(
        &self,
        source_realm: &sources::ResolvedRealmId,
        key: RealmResolutionCacheKey,
        artifact: &CachedRealmResolutionArtifact,
    ) -> Result<(), CacheError> {
        debug_assert_eq!(&artifact.source_realm, source_realm);
        let path = self.realm_resolution_artifact_path(source_realm, key);
        let envelope = RealmResolutionCacheEnvelope {
            format: REALM_RESOLUTION_CACHE_FORMAT,
            key_hash: key.hash,
            source_realm: &artifact.source_realm,
            request: &artifact.request,
            target: &artifact.target,
        };
        write_cache_envelope(&path, "yures", &envelope)
    }

    fn artifact_dir(&self, stage: &str) -> PathBuf {
        self.root.join("artifacts").join(stage)
    }

    fn realm_dir(&self, realm: &sources::ResolvedRealmId) -> PathBuf {
        self.root
            .join("realms")
            .join(format!("{:016x}", realm_cache_component_hash(realm)))
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

#[derive(Debug, Clone, PartialEq)]
pub struct CachedMonoArtifact {
    pub program: specialize::mono::Program,
    pub file_count: usize,
    pub errors: Vec<String>,
}

#[derive(Clone)]
pub struct CachedCompiledUnitArtifact {
    pub manifest: CompiledUnitManifest,
    pub syntax: sources::CompiledSyntaxSurface,
    pub namespace: infer::CompiledNamespaceSurface,
    pub lowering: infer::CompiledLoweringSurface,
    pub typed: infer::CompiledTypedSurface,
    pub runtime: infer::CompiledRuntimeSurface,
    pub external_runtime: CompiledUnitExternalRuntimeRefs,
    pub errors: Vec<String>,
}

impl CachedCompiledUnitArtifact {
    pub fn cache_key(&self) -> SourceCacheKey {
        SourceCacheKey {
            hash: self.manifest.source_hash,
        }
    }
}

pub fn encode_compiled_unit_artifact_bytes(
    artifact: &CachedCompiledUnitArtifact,
) -> Result<Vec<u8>, CacheError> {
    let envelope = CompiledUnitCacheEnvelope {
        format: COMPILED_UNIT_CACHE_FORMAT,
        manifest: &artifact.manifest,
        syntax: &artifact.syntax,
        namespace: &artifact.namespace,
        lowering: &artifact.lowering,
        typed: &artifact.typed,
        runtime: &artifact.runtime,
        external_runtime: &artifact.external_runtime,
        errors: &artifact.errors,
    };
    bincode::serialize(&envelope).map_err(|error| CacheError::Encode {
        path: embedded_compiled_unit_artifact_path(),
        error,
    })
}

pub fn decode_compiled_unit_artifact_bytes(
    bytes: &[u8],
    key: SourceCacheKey,
) -> Result<Option<CachedCompiledUnitArtifact>, CacheError> {
    let envelope: CompiledUnitCacheEnvelope =
        bincode::deserialize(bytes).map_err(|error| CacheError::Decode {
            path: embedded_compiled_unit_artifact_path(),
            error,
        })?;
    if envelope.format != COMPILED_UNIT_CACHE_FORMAT
        || !compiled_unit_envelope_matches_key(key, &envelope)
    {
        return Ok(None);
    }
    Ok(Some(cached_compiled_unit_artifact_from_envelope(envelope)))
}

pub struct CachedSourceUnitCompiledArtifacts {
    pub keys: Vec<SourceCacheKey>,
    pub artifacts: Vec<Option<CachedCompiledUnitArtifact>>,
    pub selection: SourceUnitCacheSelection,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CachedRealmResolutionArtifact {
    pub source_realm: sources::ResolvedRealmId,
    pub request: sources::UseImport,
    pub target: CachedRealmResolutionTarget,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CachedRealmResolutionTarget {
    pub realm: sources::ResolvedRealmId,
    pub band_path: sources::Path,
    pub module_path: sources::Path,
    pub source_path: String,
    pub source_len: usize,
    pub source_hash: u64,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledUnitManifest {
    pub cache_schema_version: u32,
    pub compiled_unit_format: u32,
    pub source_hash: u64,
    pub syntax_hash: u64,
    pub namespace_hash: u64,
    pub lowering_hash: u64,
    pub typed_hash: u64,
    pub runtime_hash: u64,
    pub external_runtime_hash: u64,
    pub files: Vec<CompiledUnitSourceFile>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledUnitExternalRuntimeRefs {
    pub imported_def_count: usize,
    pub defs: Vec<poly::expr::DefId>,
    pub modules: Vec<CompiledUnitExternalRuntimeModuleRef>,
    pub values: Vec<CompiledUnitExternalRuntimeValueRef>,
    #[serde(default)]
    pub type_field_methods: Vec<CompiledUnitExternalRuntimeTypeFieldMethodRef>,
    #[serde(default)]
    pub casts: Vec<CompiledUnitExternalRuntimeCastRef>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledUnitExternalRuntimeModuleRef {
    pub module: u32,
    pub module_path: Vec<String>,
    pub def: poly::expr::DefId,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledUnitExternalRuntimeValueRef {
    pub symbol: u32,
    pub value_path: Vec<String>,
    pub def: poly::expr::DefId,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledUnitExternalRuntimeTypeFieldMethodRef {
    pub owner_type_path: Vec<String>,
    pub name: String,
    pub receiver_kind: infer::TypeMethodReceiver,
    pub def: poly::expr::DefId,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledUnitExternalRuntimeCastRef {
    pub source_type_path: Vec<String>,
    pub target_type_path: Vec<String>,
    pub ordinal: u32,
    pub def: poly::expr::DefId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompiledUnitExternalRuntimeDefMapError {
    MissingModulePath {
        module_path: Vec<String>,
    },
    MissingValuePath {
        value_path: Vec<String>,
    },
    MissingTypeFieldMethod {
        owner_type_path: Vec<String>,
        name: String,
        receiver_kind: infer::TypeMethodReceiver,
    },
    MissingCast {
        source_type_path: Vec<String>,
        target_type_path: Vec<String>,
        ordinal: u32,
    },
    ConflictingDefMapping {
        source: poly::expr::DefId,
        first: poly::expr::DefId,
        second: poly::expr::DefId,
    },
    UnkeyedExternalDefs {
        defs: Vec<poly::expr::DefId>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledUnitSourceFile {
    pub path: String,
    pub module_path: Vec<String>,
    #[serde(default)]
    pub band_path: Vec<String>,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RealmResolutionCacheKey {
    hash: u64,
}

impl RealmResolutionCacheKey {
    pub fn to_hex(self) -> String {
        format!("{:016x}", self.hash)
    }
}

pub fn source_cache_key(files: &[CollectedSource]) -> SourceCacheKey {
    source_cache_key_with_schema(files, CURRENT_CACHE_SCHEMA)
}

pub fn realm_resolution_cache_key(
    source_file: &CollectedSource,
    request: &sources::UseImport,
) -> RealmResolutionCacheKey {
    let mut hasher = StableHasher::new();
    hasher.bytes(REALM_RESOLUTION_CACHE_SALT);
    hash_cache_schema(&mut hasher, CURRENT_CACHE_SCHEMA);
    hash_source_file_resolution_context(&mut hasher, source_file);
    hash_use_import(&mut hasher, request);
    RealmResolutionCacheKey {
        hash: hasher.finish(),
    }
}

pub fn write_current_realm_resolution_artifacts(
    cache: &ArtifactCache,
    files: &[CollectedSource],
) -> Result<usize, CacheError> {
    write_realm_resolution_artifacts_with_kind(cache, files, RealmResolutionArtifactKind::Current)
}

pub fn write_realm_resolution_artifacts(
    cache: &ArtifactCache,
    files: &[CollectedSource],
) -> Result<usize, CacheError> {
    write_realm_resolution_artifacts_with_kind(cache, files, RealmResolutionArtifactKind::All)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RealmResolutionArtifactKind {
    Current,
    All,
}

fn write_realm_resolution_artifacts_with_kind(
    cache: &ArtifactCache,
    files: &[CollectedSource],
    kind: RealmResolutionArtifactKind,
) -> Result<usize, CacheError> {
    let mut written = 0;
    for source_file in files {
        let source_realm = sources::local_realm_id(&source_file.path);
        for request in &source_file.resolution_imports {
            let Some((target_realm, target_file)) =
                realm_resolution_artifact_target(&source_realm, request, files, kind)
            else {
                continue;
            };
            let key = realm_resolution_cache_key(source_file, request);
            let artifact =
                realm_resolution_artifact(&source_realm, &target_realm, request, target_file);

            if cache
                .read_realm_resolution_artifact(&source_realm, key)?
                .as_ref()
                == Some(&artifact)
            {
                continue;
            }
            cache.write_realm_resolution_artifact(&source_realm, key, &artifact)?;
            written += 1;
        }
    }
    Ok(written)
}

fn realm_resolution_artifact_target<'a>(
    source_realm: &sources::ResolvedRealmId,
    request: &sources::UseImport,
    files: &'a [CollectedSource],
    kind: RealmResolutionArtifactKind,
) -> Option<(sources::ResolvedRealmId, &'a CollectedSource)> {
    if let Some(band_path) = current_realm_import_band_path(request) {
        let target_file = files
            .iter()
            .find(|file| file.module_path == band_path && file.band_path == band_path)?;
        return Some((source_realm.clone(), target_file));
    }
    if kind == RealmResolutionArtifactKind::Current {
        return None;
    }
    let module_path = crate::source::installed_local_import_module_path(request)?;
    let target_file = files
        .iter()
        .find(|file| file.module_path == module_path && file.band_path == module_path)?;
    Some((
        installed_local_realm_id_from_source_path(&target_file.path)?,
        target_file,
    ))
}

fn installed_local_realm_id_from_source_path(
    source_path: &Path,
) -> Option<sources::ResolvedRealmId> {
    source_path
        .ancestors()
        .map(|ancestor| ancestor.join("snapshot.json"))
        .find(|snapshot| snapshot.is_file())
        .and_then(|snapshot| sources::read_frozen_realm_snapshot(snapshot).ok())
        .map(|snapshot| sources::ResolvedRealmId {
            identity: snapshot.identity,
            version: Some(snapshot.version),
        })
}

fn realm_resolution_artifact(
    source_realm: &sources::ResolvedRealmId,
    target_realm: &sources::ResolvedRealmId,
    request: &sources::UseImport,
    target_file: &CollectedSource,
) -> CachedRealmResolutionArtifact {
    CachedRealmResolutionArtifact {
        source_realm: source_realm.clone(),
        request: request.clone(),
        target: CachedRealmResolutionTarget {
            realm: target_realm.clone(),
            band_path: target_file.band_path.clone(),
            module_path: target_file.module_path.clone(),
            source_path: target_file.path.to_string_lossy().into_owned(),
            source_len: target_file.source.len(),
            source_hash: source_file_hash(target_file),
        },
    }
}

pub(crate) fn current_realm_import_band_path(import: &sources::UseImport) -> Option<sources::Path> {
    let (path, route) = match import {
        sources::UseImport::Alias { path, route, .. } => (path, *route),
        sources::UseImport::Glob { prefix, route, .. } => (prefix, *route),
    };
    let sources::UsePathRoute::CurrentRealm { band_segments } = route else {
        return None;
    };
    if band_segments == 0 || band_segments > path.segments.len() {
        return None;
    }
    Some(sources::Path {
        segments: path.segments[..band_segments].to_vec(),
    })
}

pub fn source_compilation_unit_cache_keys(
    files: &[CollectedSource],
    units: &SourceCompilationUnits,
) -> Vec<SourceCacheKey> {
    let mut keys = vec![None; units.units.len()];
    for unit in 0..units.units.len() {
        compute_source_unit_cache_key(files, units, unit, &mut keys);
    }
    keys.into_iter()
        .map(|key| key.expect("source unit key should be computed"))
        .collect()
}

pub fn compiled_unit_artifact_from_loaded_files(
    files: &[CollectedSource],
    loaded: &[sources::LoadedFile],
) -> Result<CachedCompiledUnitArtifact, infer::LoadedFilesError> {
    compiled_unit_artifact_from_loaded_files_with_key(files, loaded, source_cache_key(files))
}

pub fn compiled_unit_artifact_from_loaded_files_with_key(
    files: &[CollectedSource],
    loaded: &[sources::LoadedFile],
    key: SourceCacheKey,
) -> Result<CachedCompiledUnitArtifact, infer::LoadedFilesError> {
    let lowering = infer::lowering::lower_loaded_files(loaded)?;
    Ok(compiled_unit_artifact_from_lowering_with_key(
        files,
        loaded,
        &lowering,
        lowering
            .errors
            .iter()
            .map(|error| format!("{error:?}"))
            .collect(),
        key,
    ))
}

pub fn compiled_unit_artifact_from_standalone_source_unit(
    files: &[CollectedSource],
    units: &SourceCompilationUnits,
    unit: usize,
) -> Result<CachedCompiledUnitArtifact, SourceUnitCompiledArtifactError> {
    let keys = source_compilation_unit_cache_keys(files, units);
    let key = *keys
        .get(unit)
        .ok_or(SourceUnitCompiledArtifactError::UnknownUnit { unit })?;
    let source_unit = units
        .units
        .get(unit)
        .ok_or(SourceUnitCompiledArtifactError::UnknownUnit { unit })?;
    let unit_files = source_unit
        .files
        .iter()
        .map(|file| files[*file].clone())
        .collect::<Vec<_>>();
    let loaded = source_unit_lowering_loaded_files(files, units, unit)
        .map_err(SourceUnitCompiledArtifactError::LoweringInput)?;
    let lowering = infer::lowering::lower_loaded_files(&loaded)
        .map_err(SourceUnitCompiledArtifactError::Lower)?;
    Ok(compiled_unit_artifact_from_lowering_with_key(
        &unit_files,
        &loaded,
        &lowering,
        lowering
            .errors
            .iter()
            .map(|error| format!("{error:?}"))
            .collect(),
        key,
    ))
}

pub fn compiled_unit_artifact_from_source_unit_closure(
    files: &[CollectedSource],
    units: &SourceCompilationUnits,
    unit: usize,
) -> Result<CachedCompiledUnitArtifact, SourceUnitCompiledArtifactError> {
    let keys = source_compilation_unit_cache_keys(files, units);
    let key = *keys
        .get(unit)
        .ok_or(SourceUnitCompiledArtifactError::UnknownUnit { unit })?;
    let closure_files = source_unit_closure_file_indices(units, unit)
        .map_err(SourceUnitCompiledArtifactError::LoweringInput)?
        .into_iter()
        .map(|file| files[file].clone())
        .collect::<Vec<_>>();
    let loaded = source_unit_closure_lowering_loaded_files(files, units, unit)
        .map_err(SourceUnitCompiledArtifactError::LoweringInput)?;
    let lowering = infer::lowering::lower_loaded_files(&loaded)
        .map_err(SourceUnitCompiledArtifactError::Lower)?;
    Ok(compiled_unit_artifact_from_lowering_with_key(
        &closure_files,
        &loaded,
        &lowering,
        lowering
            .errors
            .iter()
            .map(|error| format!("{error:?}"))
            .collect(),
        key,
    ))
}

pub fn compiled_unit_artifact_from_lowering(
    files: &[CollectedSource],
    loaded: &[sources::LoadedFile],
    lowering: &infer::lowering::BodyLowering,
    errors: Vec<String>,
) -> CachedCompiledUnitArtifact {
    compiled_unit_artifact_from_lowering_with_key(
        files,
        loaded,
        lowering,
        errors,
        source_cache_key(files),
    )
}

pub fn compiled_unit_artifact_from_lowering_with_key(
    files: &[CollectedSource],
    loaded: &[sources::LoadedFile],
    lowering: &infer::lowering::BodyLowering,
    errors: Vec<String>,
    key: SourceCacheKey,
) -> CachedCompiledUnitArtifact {
    let syntax = sources::CompiledSyntaxSurface::from_loaded_files(loaded);
    compiled_unit_artifact_from_lowering_with_syntax_and_key(files, syntax, lowering, errors, key)
}

pub fn compiled_unit_artifact_from_lowering_with_syntax_and_key(
    files: &[CollectedSource],
    syntax: sources::CompiledSyntaxSurface,
    lowering: &infer::lowering::BodyLowering,
    errors: Vec<String>,
    key: SourceCacheKey,
) -> CachedCompiledUnitArtifact {
    let namespace = infer::CompiledNamespaceSurface::from_module_table(&lowering.modules);
    let lowering_surface =
        infer::CompiledLoweringSurface::from_module_table(&lowering.modules, &namespace);
    let typed = infer::CompiledTypedSurface::from_lowering(lowering, &namespace);
    let runtime = infer::CompiledRuntimeSurface::from_lowering_with_namespace(lowering, &namespace);
    let external_runtime = compiled_unit_external_runtime_refs(lowering, &namespace);
    let manifest = compiled_unit_manifest(
        files,
        &syntax,
        &namespace,
        &lowering_surface,
        &typed,
        &runtime,
        &external_runtime,
        key,
    );
    CachedCompiledUnitArtifact {
        manifest,
        syntax,
        namespace,
        lowering: lowering_surface,
        typed,
        runtime,
        external_runtime,
        errors,
    }
}

fn compiled_unit_external_runtime_refs(
    lowering: &infer::lowering::BodyLowering,
    namespace: &infer::CompiledNamespaceSurface,
) -> CompiledUnitExternalRuntimeRefs {
    let module_paths = namespace
        .modules
        .iter()
        .map(|module| (module.id, module.path.clone()))
        .collect::<std::collections::HashMap<_, _>>();
    let value_paths = namespace
        .values
        .iter()
        .map(|value| (value.unit_id, value.path.clone()))
        .collect::<std::collections::HashMap<_, _>>();

    let mut defs = lowering.prefix_runtime().def_ids().collect::<Vec<_>>();
    defs.sort_by_key(|def| def.0);
    defs.dedup();

    let mut modules = lowering
        .prefix_runtime()
        .module_defs()
        .map(|entry| CompiledUnitExternalRuntimeModuleRef {
            module: entry.module,
            module_path: if entry.module_path.is_empty() {
                module_paths.get(&entry.module).cloned().unwrap_or_default()
            } else {
                entry.module_path.clone()
            },
            def: entry.def,
        })
        .collect::<Vec<_>>();
    modules.sort_by(|left, right| {
        left.module_path
            .cmp(&right.module_path)
            .then_with(|| left.module.cmp(&right.module))
            .then_with(|| left.def.0.cmp(&right.def.0))
    });

    let mut values = lowering
        .prefix_runtime()
        .value_defs()
        .map(|entry| CompiledUnitExternalRuntimeValueRef {
            symbol: entry.symbol,
            value_path: if entry.value_path.is_empty() {
                value_paths.get(&entry.symbol).cloned().unwrap_or_default()
            } else {
                entry.value_path.clone()
            },
            def: entry.def,
        })
        .collect::<Vec<_>>();
    values.sort_by(|left, right| {
        left.value_path
            .cmp(&right.value_path)
            .then_with(|| left.symbol.cmp(&right.symbol))
            .then_with(|| left.def.0.cmp(&right.def.0))
    });

    let mut type_field_methods = lowering
        .prefix_runtime()
        .type_field_method_defs()
        .map(|entry| CompiledUnitExternalRuntimeTypeFieldMethodRef {
            owner_type_path: entry.owner_type_path.clone(),
            name: entry.name.clone(),
            receiver_kind: entry.receiver_kind,
            def: entry.def,
        })
        .collect::<Vec<_>>();
    type_field_methods.sort_by(|left, right| {
        left.owner_type_path
            .cmp(&right.owner_type_path)
            .then_with(|| left.name.cmp(&right.name))
            .then_with(|| (left.receiver_kind as u8).cmp(&(right.receiver_kind as u8)))
            .then_with(|| left.def.0.cmp(&right.def.0))
    });

    let mut casts = lowering
        .prefix_runtime()
        .cast_defs()
        .map(|entry| CompiledUnitExternalRuntimeCastRef {
            source_type_path: entry.source_type_path.clone(),
            target_type_path: entry.target_type_path.clone(),
            ordinal: entry.ordinal,
            def: entry.def,
        })
        .collect::<Vec<_>>();
    casts.sort_by(|left, right| {
        left.source_type_path
            .cmp(&right.source_type_path)
            .then_with(|| left.target_type_path.cmp(&right.target_type_path))
            .then_with(|| left.ordinal.cmp(&right.ordinal))
            .then_with(|| left.def.0.cmp(&right.def.0))
    });

    CompiledUnitExternalRuntimeRefs {
        imported_def_count: lowering.prefix_runtime().def_count(),
        defs,
        modules,
        values,
        type_field_methods,
        casts,
    }
}

pub fn compiled_unit_external_runtime_def_pairs(
    artifact: &CachedCompiledUnitArtifact,
    prefix_runtime: &infer::lowering::BodyLoweringPrefixRuntime,
) -> Result<Vec<(poly::expr::DefId, poly::expr::DefId)>, CompiledUnitExternalRuntimeDefMapError> {
    let prefix_modules = prefix_runtime
        .module_defs()
        .map(|entry| (entry.module_path.clone(), entry.def))
        .collect::<HashMap<_, _>>();
    let prefix_values = prefix_runtime
        .value_defs()
        .map(|entry| (entry.value_path.clone(), entry.def))
        .collect::<HashMap<_, _>>();
    let prefix_type_field_methods = prefix_runtime
        .type_field_method_defs()
        .map(|entry| {
            (
                (
                    entry.owner_type_path.clone(),
                    entry.name.clone(),
                    entry.receiver_kind as u8,
                ),
                entry.def,
            )
        })
        .collect::<HashMap<_, _>>();
    let prefix_casts = prefix_runtime
        .cast_defs()
        .map(|entry| {
            (
                (
                    entry.source_type_path.clone(),
                    entry.target_type_path.clone(),
                    entry.ordinal,
                ),
                entry.def,
            )
        })
        .collect::<HashMap<_, _>>();

    let mut pairs = HashMap::new();
    for module in &artifact.external_runtime.modules {
        let target = prefix_modules
            .get(&module.module_path)
            .copied()
            .ok_or_else(
                || CompiledUnitExternalRuntimeDefMapError::MissingModulePath {
                    module_path: module.module_path.clone(),
                },
            )?;
        insert_external_runtime_def_pair(&mut pairs, module.def, target)?;
    }
    for value in &artifact.external_runtime.values {
        let target = prefix_values
            .get(&value.value_path)
            .copied()
            .ok_or_else(
                || CompiledUnitExternalRuntimeDefMapError::MissingValuePath {
                    value_path: value.value_path.clone(),
                },
            )?;
        insert_external_runtime_def_pair(&mut pairs, value.def, target)?;
    }
    for method in &artifact.external_runtime.type_field_methods {
        let target = prefix_type_field_methods
            .get(&(
                method.owner_type_path.clone(),
                method.name.clone(),
                method.receiver_kind as u8,
            ))
            .copied()
            .ok_or_else(
                || CompiledUnitExternalRuntimeDefMapError::MissingTypeFieldMethod {
                    owner_type_path: method.owner_type_path.clone(),
                    name: method.name.clone(),
                    receiver_kind: method.receiver_kind,
                },
            )?;
        insert_external_runtime_def_pair(&mut pairs, method.def, target)?;
    }
    for cast in &artifact.external_runtime.casts {
        let target = prefix_casts
            .get(&(
                cast.source_type_path.clone(),
                cast.target_type_path.clone(),
                cast.ordinal,
            ))
            .copied()
            .ok_or_else(|| CompiledUnitExternalRuntimeDefMapError::MissingCast {
                source_type_path: cast.source_type_path.clone(),
                target_type_path: cast.target_type_path.clone(),
                ordinal: cast.ordinal,
            })?;
        insert_external_runtime_def_pair(&mut pairs, cast.def, target)?;
    }

    let mut pairs = pairs.into_iter().collect::<Vec<_>>();
    pairs.sort_by_key(|(source, target)| (source.0, target.0));
    Ok(pairs)
}

pub fn compiled_unit_complete_external_runtime_def_pairs(
    artifact: &CachedCompiledUnitArtifact,
    prefix_runtime: &infer::lowering::BodyLoweringPrefixRuntime,
) -> Result<Vec<(poly::expr::DefId, poly::expr::DefId)>, CompiledUnitExternalRuntimeDefMapError> {
    let pairs = compiled_unit_external_runtime_def_pairs(artifact, prefix_runtime)?;
    let keyed = pairs
        .iter()
        .map(|(source, _)| *source)
        .collect::<HashSet<_>>();
    let mut unkeyed = compiled_unit_required_external_defs_for_import(artifact)
        .into_iter()
        .filter(|def| !keyed.contains(def))
        .collect::<Vec<_>>();
    unkeyed.sort_by_key(|def| def.0);
    unkeyed.dedup();
    if !unkeyed.is_empty() {
        return Err(CompiledUnitExternalRuntimeDefMapError::UnkeyedExternalDefs { defs: unkeyed });
    }
    Ok(pairs)
}

fn compiled_unit_required_external_defs_for_import(
    artifact: &CachedCompiledUnitArtifact,
) -> Vec<poly::expr::DefId> {
    let external_defs = artifact
        .external_runtime
        .defs
        .iter()
        .copied()
        .collect::<HashSet<_>>();
    let mut required = artifact
        .runtime
        .required_external_defs_for_reachable_import(external_defs.iter().copied());
    required.extend(
        artifact
            .lowering
            .required_runtime_defs()
            .into_iter()
            .filter(|def| external_defs.contains(def)),
    );
    required.sort_by_key(|def| def.0);
    required.dedup();
    required
}

fn insert_external_runtime_def_pair(
    pairs: &mut HashMap<poly::expr::DefId, poly::expr::DefId>,
    source: poly::expr::DefId,
    target: poly::expr::DefId,
) -> Result<(), CompiledUnitExternalRuntimeDefMapError> {
    if let Some(first) = pairs.insert(source, target) {
        if first != target {
            return Err(
                CompiledUnitExternalRuntimeDefMapError::ConflictingDefMapping {
                    source,
                    first,
                    second: target,
                },
            );
        }
    }
    Ok(())
}

#[derive(Debug)]
pub enum CompiledUnitMergeError {
    Empty,
    ConflictingFile { path: String },
    Syntax(sources::CompiledSyntaxMergeError),
    Namespace(infer::CompiledNamespaceMergeError),
    Runtime(infer::CompiledRuntimeMergeError),
    ExternalRuntime(CompiledUnitExternalRuntimeMergeError),
    Typed(infer::CompiledTypedMergeError),
    Lowering(infer::CompiledLoweringMergeError),
}

#[derive(Debug)]
pub enum CompiledUnitExternalRuntimeMergeError {
    MissingModule {
        prefix: usize,
        module: u32,
    },
    MissingValue {
        prefix: usize,
        symbol: u32,
    },
    MissingDef {
        prefix: usize,
        def: poly::expr::DefId,
    },
}

pub fn merge_compiled_unit_artifacts(
    artifacts: Vec<CachedCompiledUnitArtifact>,
) -> Result<CachedCompiledUnitArtifact, CompiledUnitMergeError> {
    if artifacts.is_empty() {
        return Err(CompiledUnitMergeError::Empty);
    }
    let key = merged_compiled_unit_artifact_key(&artifacts)?;
    let files = merge_compiled_unit_manifest_files(&artifacts)?;
    let syntax =
        sources::CompiledSyntaxSurface::merge_prefixes(artifacts.iter().map(|unit| &unit.syntax))
            .map_err(CompiledUnitMergeError::Syntax)?;
    let namespace = infer::CompiledNamespaceSurface::merge_prefixes_with_remap(
        artifacts.iter().map(|unit| &unit.namespace),
    )
    .map_err(CompiledUnitMergeError::Namespace)?;
    let runtime = infer::CompiledRuntimeSurface::merge_prefixes_with_remap(
        artifacts.iter().map(|unit| &unit.runtime),
        &namespace,
    )
    .map_err(CompiledUnitMergeError::Runtime)?;
    let external_runtime =
        merge_compiled_unit_external_runtime_refs(&artifacts, &namespace, &runtime)
            .map_err(CompiledUnitMergeError::ExternalRuntime)?;
    let typed = infer::CompiledTypedSurface::merge_prefixes(
        artifacts.iter().map(|unit| &unit.typed),
        &namespace,
    )
    .map_err(CompiledUnitMergeError::Typed)?;
    let lowering = infer::CompiledLoweringSurface::merge_prefixes(
        artifacts.iter().map(|unit| &unit.lowering),
        &namespace,
        &runtime,
    )
    .map_err(CompiledUnitMergeError::Lowering)?;
    let namespace = namespace.surface;
    let runtime = runtime.surface;
    let manifest = CompiledUnitManifest {
        cache_schema_version: CACHE_SCHEMA_VERSION,
        compiled_unit_format: COMPILED_UNIT_CACHE_FORMAT,
        source_hash: key.hash,
        syntax_hash: compiled_syntax_hash(&syntax),
        namespace_hash: compiled_namespace_hash(&namespace),
        lowering_hash: compiled_lowering_hash(&lowering),
        typed_hash: compiled_typed_hash(&typed),
        runtime_hash: compiled_runtime_hash(&runtime),
        external_runtime_hash: compiled_external_runtime_hash(&external_runtime),
        files,
    };
    Ok(CachedCompiledUnitArtifact {
        manifest,
        syntax,
        namespace,
        lowering,
        typed,
        runtime,
        external_runtime,
        errors: artifacts
            .into_iter()
            .flat_map(|artifact| artifact.errors)
            .collect(),
    })
}

fn merge_compiled_unit_external_runtime_refs(
    artifacts: &[CachedCompiledUnitArtifact],
    namespace: &infer::CompiledNamespaceMergeOutput,
    runtime: &infer::CompiledRuntimeMergeOutput,
) -> Result<CompiledUnitExternalRuntimeRefs, CompiledUnitExternalRuntimeMergeError> {
    let mut imported_def_count = 0;
    let mut modules = Vec::new();
    let mut values = Vec::new();
    let mut type_field_methods = Vec::new();
    let mut casts = Vec::new();

    for (prefix, artifact) in artifacts.iter().enumerate() {
        imported_def_count += artifact.external_runtime.imported_def_count;
        for module in &artifact.external_runtime.modules {
            let module_id = namespace.map_module(prefix, module.module).ok_or(
                CompiledUnitExternalRuntimeMergeError::MissingModule {
                    prefix,
                    module: module.module,
                },
            )?;
            let def = runtime.map_def(prefix, module.def).ok_or(
                CompiledUnitExternalRuntimeMergeError::MissingDef {
                    prefix,
                    def: module.def,
                },
            )?;
            modules.push(CompiledUnitExternalRuntimeModuleRef {
                module: module_id,
                module_path: module.module_path.clone(),
                def,
            });
        }
        for value in &artifact.external_runtime.values {
            let symbol = namespace.map_value(prefix, value.symbol).ok_or(
                CompiledUnitExternalRuntimeMergeError::MissingValue {
                    prefix,
                    symbol: value.symbol,
                },
            )?;
            let def = runtime.map_def(prefix, value.def).ok_or(
                CompiledUnitExternalRuntimeMergeError::MissingDef {
                    prefix,
                    def: value.def,
                },
            )?;
            values.push(CompiledUnitExternalRuntimeValueRef {
                symbol,
                value_path: value.value_path.clone(),
                def,
            });
        }
        for method in &artifact.external_runtime.type_field_methods {
            let def = runtime.map_def(prefix, method.def).ok_or(
                CompiledUnitExternalRuntimeMergeError::MissingDef {
                    prefix,
                    def: method.def,
                },
            )?;
            type_field_methods.push(CompiledUnitExternalRuntimeTypeFieldMethodRef {
                owner_type_path: method.owner_type_path.clone(),
                name: method.name.clone(),
                receiver_kind: method.receiver_kind,
                def,
            });
        }
        for cast in &artifact.external_runtime.casts {
            let def = runtime.map_def(prefix, cast.def).ok_or(
                CompiledUnitExternalRuntimeMergeError::MissingDef {
                    prefix,
                    def: cast.def,
                },
            )?;
            casts.push(CompiledUnitExternalRuntimeCastRef {
                source_type_path: cast.source_type_path.clone(),
                target_type_path: cast.target_type_path.clone(),
                ordinal: cast.ordinal,
                def,
            });
        }
    }
    let mut defs = Vec::new();
    for (prefix, artifact) in artifacts.iter().enumerate() {
        for def in &artifact.external_runtime.defs {
            let def = runtime
                .map_def(prefix, *def)
                .ok_or(CompiledUnitExternalRuntimeMergeError::MissingDef { prefix, def: *def })?;
            defs.push(def);
        }
    }

    modules.sort_by(|left, right| {
        left.module_path
            .cmp(&right.module_path)
            .then_with(|| left.module.cmp(&right.module))
            .then_with(|| left.def.0.cmp(&right.def.0))
    });
    modules.dedup();
    values.sort_by(|left, right| {
        left.value_path
            .cmp(&right.value_path)
            .then_with(|| left.symbol.cmp(&right.symbol))
            .then_with(|| left.def.0.cmp(&right.def.0))
    });
    values.dedup();
    type_field_methods.sort_by(|left, right| {
        left.owner_type_path
            .cmp(&right.owner_type_path)
            .then_with(|| left.name.cmp(&right.name))
            .then_with(|| (left.receiver_kind as u8).cmp(&(right.receiver_kind as u8)))
            .then_with(|| left.def.0.cmp(&right.def.0))
    });
    type_field_methods.dedup();
    casts.sort_by(|left, right| {
        left.source_type_path
            .cmp(&right.source_type_path)
            .then_with(|| left.target_type_path.cmp(&right.target_type_path))
            .then_with(|| left.ordinal.cmp(&right.ordinal))
            .then_with(|| left.def.0.cmp(&right.def.0))
    });
    casts.dedup();
    defs.sort_by_key(|def| def.0);
    defs.dedup();

    Ok(CompiledUnitExternalRuntimeRefs {
        imported_def_count,
        defs,
        modules,
        values,
        type_field_methods,
        casts,
    })
}

pub fn merged_compiled_unit_artifact_key(
    artifacts: &[CachedCompiledUnitArtifact],
) -> Result<SourceCacheKey, CompiledUnitMergeError> {
    if artifacts.is_empty() {
        return Err(CompiledUnitMergeError::Empty);
    }
    let files = merge_compiled_unit_manifest_files(artifacts)?;
    Ok(merged_compiled_unit_cache_key(artifacts, &files))
}

fn merge_compiled_unit_manifest_files(
    artifacts: &[CachedCompiledUnitArtifact],
) -> Result<Vec<CompiledUnitSourceFile>, CompiledUnitMergeError> {
    let mut files = Vec::<CompiledUnitSourceFile>::new();
    for artifact in artifacts {
        for file in &artifact.manifest.files {
            if let Some(existing) = files.iter().find(|existing| existing.path == file.path) {
                if existing != file {
                    return Err(CompiledUnitMergeError::ConflictingFile {
                        path: file.path.clone(),
                    });
                }
                continue;
            }
            files.push(file.clone());
        }
    }
    Ok(files)
}

fn merged_compiled_unit_cache_key(
    artifacts: &[CachedCompiledUnitArtifact],
    files: &[CompiledUnitSourceFile],
) -> SourceCacheKey {
    let mut hasher = StableHasher::new();
    hasher.bytes(MERGED_COMPILED_UNIT_CACHE_SALT);
    hash_cache_schema(&mut hasher, CURRENT_CACHE_SCHEMA);
    hasher.usize(artifacts.len());
    for artifact in artifacts {
        hasher.u64(artifact.manifest.source_hash);
    }
    hasher.usize(files.len());
    for file in files {
        hasher.string(&file.path);
        hasher.usize(file.module_path.len());
        for segment in &file.module_path {
            hasher.string(segment);
        }
        hasher.usize(file.source_len);
        hasher.u64(file.source_hash);
    }
    SourceCacheKey {
        hash: hasher.finish(),
    }
}

#[derive(Debug)]
pub enum SourceUnitCompiledArtifactError {
    UnknownUnit { unit: usize },
    LoweringInput(SourceUnitLoweringInputError),
    Lower(infer::LoadedFilesError),
}

fn compiled_unit_envelope_matches_key(
    key: SourceCacheKey,
    envelope: &CompiledUnitCacheEnvelope,
) -> bool {
    let manifest = &envelope.manifest;
    manifest.cache_schema_version == CACHE_SCHEMA_VERSION
        && manifest.compiled_unit_format == COMPILED_UNIT_CACHE_FORMAT
        && manifest.source_hash == key.hash
        && manifest.syntax_hash == compiled_syntax_hash(&envelope.syntax)
        && manifest.namespace_hash == compiled_namespace_hash(&envelope.namespace)
        && manifest.lowering_hash == compiled_lowering_hash(&envelope.lowering)
        && manifest.typed_hash == compiled_typed_hash(&envelope.typed)
        && manifest.runtime_hash == compiled_runtime_hash(&envelope.runtime)
        && manifest.external_runtime_hash
            == compiled_external_runtime_hash(&envelope.external_runtime)
}

fn cached_compiled_unit_artifact_from_envelope(
    envelope: CompiledUnitCacheEnvelope,
) -> CachedCompiledUnitArtifact {
    CachedCompiledUnitArtifact {
        manifest: envelope.manifest,
        syntax: envelope.syntax,
        namespace: envelope.namespace,
        lowering: envelope.lowering,
        typed: envelope.typed,
        runtime: envelope.runtime,
        external_runtime: envelope.external_runtime,
        errors: envelope.errors,
    }
}

fn embedded_compiled_unit_artifact_path() -> PathBuf {
    PathBuf::from("<embedded-compiled-unit-artifact>")
}

fn source_cache_key_with_schema(files: &[CollectedSource], schema: CacheSchema) -> SourceCacheKey {
    let mut hasher = StableHasher::new();
    hasher.bytes(SOURCE_CACHE_SALT);
    hash_cache_schema(&mut hasher, schema);
    hasher.usize(files.len());
    for file in files {
        hash_collected_source(&mut hasher, file);
    }
    SourceCacheKey {
        hash: hasher.finish(),
    }
}

fn compute_source_unit_cache_key(
    files: &[CollectedSource],
    units: &SourceCompilationUnits,
    unit: usize,
    keys: &mut [Option<SourceCacheKey>],
) -> SourceCacheKey {
    if let Some(key) = keys[unit] {
        return key;
    }

    let mut hasher = StableHasher::new();
    hasher.bytes(SOURCE_UNIT_CACHE_SALT);
    hash_cache_schema(&mut hasher, CURRENT_CACHE_SCHEMA);
    let source_unit = &units.units[unit];
    hasher.usize(source_unit.files.len());
    for file in &source_unit.files {
        hash_collected_source(&mut hasher, &files[*file]);
    }
    hasher.usize(source_unit.dependencies.len());
    for dep in &source_unit.dependencies {
        let dep_key = compute_source_unit_cache_key(files, units, *dep, keys);
        hasher.u64(dep_key.hash);
    }
    let key = SourceCacheKey {
        hash: hasher.finish(),
    };
    keys[unit] = Some(key);
    key
}

fn hash_cache_schema(hasher: &mut StableHasher, schema: CacheSchema) {
    hasher.u32(schema.version);
    hasher.u32(schema.poly_format);
    hasher.u32(schema.control_format);
}

fn realm_cache_component_hash(realm: &sources::ResolvedRealmId) -> u64 {
    let mut hasher = StableHasher::new();
    hasher.bytes(REALM_CACHE_COMPONENT_SALT);
    hash_resolved_realm_id(&mut hasher, realm);
    hasher.finish()
}

fn hash_resolved_realm_id(hasher: &mut StableHasher, realm: &sources::ResolvedRealmId) {
    hasher.string(&realm.identity.0);
    match &realm.version {
        Some(version) => {
            hasher.bool(true);
            hasher.string(&version.0);
        }
        None => hasher.bool(false),
    }
}

fn hash_source_file_resolution_context(hasher: &mut StableHasher, file: &CollectedSource) {
    hasher.string(&file.path.as_os_str().to_string_lossy());
    hasher.usize(file.module_path.segments.len());
    for segment in &file.module_path.segments {
        hasher.string(&segment.0);
    }
    hash_band_path(hasher, &file.band_path);
    hasher.string(&file.source);
}

fn hash_collected_source(hasher: &mut StableHasher, file: &CollectedSource) {
    hasher.string(&file.path.as_os_str().to_string_lossy());
    hasher.usize(file.module_path.segments.len());
    for segment in &file.module_path.segments {
        hasher.string(&segment.0);
    }
    hash_band_path(hasher, &file.band_path);
    hasher.string(&file.source);
    hasher.usize(file.resolution_imports.len());
    for import in &file.resolution_imports {
        hash_use_import(hasher, import);
    }
}

fn hash_band_path(hasher: &mut StableHasher, band_path: &sources::Path) {
    hasher.usize(band_path.segments.len());
    for segment in &band_path.segments {
        hasher.string(&segment.0);
    }
}

fn compiled_unit_manifest(
    files: &[CollectedSource],
    syntax: &sources::CompiledSyntaxSurface,
    namespace: &infer::CompiledNamespaceSurface,
    lowering: &infer::CompiledLoweringSurface,
    typed: &infer::CompiledTypedSurface,
    runtime: &infer::CompiledRuntimeSurface,
    external_runtime: &CompiledUnitExternalRuntimeRefs,
    key: SourceCacheKey,
) -> CompiledUnitManifest {
    CompiledUnitManifest {
        cache_schema_version: CACHE_SCHEMA_VERSION,
        compiled_unit_format: COMPILED_UNIT_CACHE_FORMAT,
        source_hash: key.hash,
        syntax_hash: compiled_syntax_hash(syntax),
        namespace_hash: compiled_namespace_hash(namespace),
        lowering_hash: compiled_lowering_hash(lowering),
        typed_hash: compiled_typed_hash(typed),
        runtime_hash: compiled_runtime_hash(runtime),
        external_runtime_hash: compiled_external_runtime_hash(external_runtime),
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
                band_path: file
                    .band_path
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

pub(crate) fn source_file_hash(file: &CollectedSource) -> u64 {
    let mut hasher = StableHasher::new();
    hasher.bytes(SOURCE_FILE_HASH_SALT);
    hasher.string(&file.path.as_os_str().to_string_lossy());
    hasher.usize(file.module_path.segments.len());
    for segment in &file.module_path.segments {
        hasher.string(&segment.0);
    }
    hasher.usize(file.band_path.segments.len());
    for segment in &file.band_path.segments {
        hasher.string(&segment.0);
    }
    hasher.string(&file.source);
    hasher.usize(file.resolution_imports.len());
    for import in &file.resolution_imports {
        hash_use_import(&mut hasher, import);
    }
    hasher.finish()
}

fn compiled_syntax_hash(syntax: &sources::CompiledSyntaxSurface) -> u64 {
    let mut hasher = StableHasher::new();
    hasher.bytes(COMPILED_SYNTAX_HASH_SALT);
    hasher.usize(syntax.files.len());
    for file in &syntax.files {
        hash_module_path(&mut hasher, &file.module_path);
        hash_band_path(&mut hasher, &file.band_path);
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
            hash_visibility(&mut hasher, request.visibility);
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
        hash_string_path(&mut hasher, &module.band_path);
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

fn compiled_typed_hash(typed: &infer::CompiledTypedSurface) -> u64 {
    let mut hasher = StableHasher::new();
    hasher.bytes(COMPILED_TYPED_HASH_SALT);
    hash_compiled_type_arena(&mut hasher, &typed.types);
    hasher.usize(typed.values.len());
    for value in &typed.values {
        hasher.u32(value.symbol);
        hash_scheme(&mut hasher, &value.scheme);
    }
    hasher.finish()
}

fn compiled_lowering_hash(lowering: &infer::CompiledLoweringSurface) -> u64 {
    let mut hasher = StableHasher::new();
    hasher.bytes(COMPILED_LOWERING_HASH_SALT);

    hasher.usize(lowering.act_type_vars.len());
    for entry in &lowering.act_type_vars {
        hasher.u32(entry.type_symbol);
        hash_string_path(&mut hasher, &entry.type_path);
        hasher.usize(entry.vars.len());
        for var in &entry.vars {
            hasher.string(var);
        }
    }

    hasher.usize(lowering.act_templates.len());
    for entry in &lowering.act_templates {
        hasher.u32(entry.type_symbol);
        hash_string_path(&mut hasher, &entry.type_path);
        hasher.string(&entry.source);
    }

    hasher.usize(lowering.constructor_payloads.len());
    for entry in &lowering.constructor_payloads {
        hasher.u32(entry.value_symbol);
        hash_string_path(&mut hasher, &entry.value_path);
        hasher.u32(entry.owner_type_symbol);
        hash_string_path(&mut hasher, &entry.owner_type_path);
        hasher.usize(entry.owner_type_vars.len());
        for var in &entry.owner_type_vars {
            hasher.string(var);
        }
        hash_compiled_constructor_payload(&mut hasher, &entry.payload);
    }

    hasher.usize(lowering.act_operations.len());
    for entry in &lowering.act_operations {
        hasher.u32(entry.type_symbol);
        hash_string_path(&mut hasher, &entry.type_path);
        hash_optional_def_id(&mut hasher, entry.source_def);
        hash_optional_u32(&mut hasher, entry.value_symbol);
        hash_optional_string_path(&mut hasher, entry.value_path.as_deref());
        hasher.string(&entry.name);
        hash_optional_compiled_signature_type(&mut hasher, &entry.signature);
    }

    hasher.usize(lowering.role_shapes.len());
    for entry in &lowering.role_shapes {
        hasher.u32(entry.type_symbol);
        hash_string_path(&mut hasher, &entry.type_path);
        hasher.usize(entry.inputs.len());
        for input in &entry.inputs {
            hasher.string(input);
        }
        hasher.usize(entry.associated.len());
        for associated in &entry.associated {
            hasher.string(associated);
        }
    }

    hasher.usize(lowering.type_methods.len());
    for entry in &lowering.type_methods {
        hasher.u32(entry.owner_type_symbol);
        hash_string_path(&mut hasher, &entry.owner_type_path);
        hash_def_id(&mut hasher, entry.source_def);
        hash_optional_u32(&mut hasher, entry.value_symbol);
        hash_optional_string_path(&mut hasher, entry.value_path.as_deref());
        hasher.string(&entry.name);
        hasher.string(&entry.receiver);
        hash_type_method_receiver(&mut hasher, entry.receiver_kind);
        hash_compiled_namespace_visibility(&mut hasher, entry.visibility);
        hasher.u32(entry.order);
    }

    hasher.usize(lowering.type_field_methods.len());
    for entry in &lowering.type_field_methods {
        hasher.u32(entry.owner_type_symbol);
        hash_string_path(&mut hasher, &entry.owner_type_path);
        hash_def_id(&mut hasher, entry.source_def);
        hasher.string(&entry.name);
        hash_type_method_receiver(&mut hasher, entry.receiver_kind);
        hash_compiled_namespace_visibility(&mut hasher, entry.visibility);
    }

    hasher.usize(lowering.act_methods.len());
    for entry in &lowering.act_methods {
        hasher.u32(entry.owner_type_symbol);
        hash_string_path(&mut hasher, &entry.owner_type_path);
        hash_def_id(&mut hasher, entry.source_def);
        hash_optional_u32(&mut hasher, entry.value_symbol);
        hash_optional_string_path(&mut hasher, entry.value_path.as_deref());
        hasher.string(&entry.name);
        hasher.string(&entry.receiver);
        hash_compiled_namespace_visibility(&mut hasher, entry.visibility);
        hasher.u32(entry.order);
    }

    hasher.usize(lowering.role_methods.len());
    for entry in &lowering.role_methods {
        hasher.u32(entry.type_symbol);
        hash_string_path(&mut hasher, &entry.type_path);
        hash_def_id(&mut hasher, entry.source_def);
        hash_optional_u32(&mut hasher, entry.value_symbol);
        hash_optional_string_path(&mut hasher, entry.value_path.as_deref());
        hasher.string(&entry.name);
        match &entry.receiver {
            Some(receiver) => {
                hasher.bool(true);
                hasher.string(receiver);
            }
            None => hasher.bool(false),
        }
        hash_compiled_namespace_visibility(&mut hasher, entry.visibility);
        hasher.u32(entry.order);
        hash_optional_compiled_signature_type(&mut hasher, &entry.signature);
    }

    hasher.finish()
}

fn hash_optional_u32(hasher: &mut StableHasher, value: Option<u32>) {
    match value {
        Some(value) => {
            hasher.bool(true);
            hasher.u32(value);
        }
        None => hasher.bool(false),
    }
}

fn hash_optional_string_path(hasher: &mut StableHasher, path: Option<&[String]>) {
    match path {
        Some(path) => {
            hasher.bool(true);
            hash_string_path(hasher, path);
        }
        None => hasher.bool(false),
    }
}

fn hash_compiled_constructor_payload(
    hasher: &mut StableHasher,
    payload: &infer::CompiledConstructorPayload,
) {
    match payload {
        infer::CompiledConstructorPayload::Unit => hasher.u8(0),
        infer::CompiledConstructorPayload::Tuple(items) => {
            hasher.u8(1);
            hasher.usize(items.len());
            for item in items {
                hash_optional_compiled_signature_type(hasher, item);
            }
        }
        infer::CompiledConstructorPayload::Record(fields) => {
            hasher.u8(2);
            hasher.usize(fields.len());
            for field in fields {
                hasher.string(&field.name);
                hash_optional_compiled_signature_type(hasher, &field.ty);
            }
        }
    }
}

fn hash_optional_compiled_signature_type(
    hasher: &mut StableHasher,
    signature: &Option<infer::CompiledSignatureType>,
) {
    match signature {
        Some(signature) => {
            hasher.bool(true);
            hash_compiled_signature_type(hasher, signature);
        }
        None => hasher.bool(false),
    }
}

fn hash_compiled_signature_type(
    hasher: &mut StableHasher,
    signature: &infer::CompiledSignatureType,
) {
    match signature {
        infer::CompiledSignatureType::Builtin(builtin) => {
            hasher.u8(0);
            hasher.string(builtin.surface_name());
        }
        infer::CompiledSignatureType::Named(path) => {
            hasher.u8(1);
            hash_string_path(hasher, path);
        }
        infer::CompiledSignatureType::Var(name) => {
            hasher.u8(2);
            hasher.string(name);
        }
        infer::CompiledSignatureType::EffectRow(row) => {
            hasher.u8(3);
            hash_compiled_signature_effect_row(hasher, row);
        }
        infer::CompiledSignatureType::Effectful { eff, ret } => {
            hasher.u8(4);
            hash_compiled_signature_effect_row(hasher, eff);
            hash_compiled_signature_type(hasher, ret);
        }
        infer::CompiledSignatureType::Tuple(items) => {
            hasher.u8(5);
            hasher.usize(items.len());
            for item in items {
                hash_compiled_signature_type(hasher, item);
            }
        }
        infer::CompiledSignatureType::Apply { callee, args } => {
            hasher.u8(6);
            hash_compiled_signature_type(hasher, callee);
            hasher.usize(args.len());
            for arg in args {
                hash_compiled_signature_type(hasher, arg);
            }
        }
        infer::CompiledSignatureType::Function {
            param,
            arg_eff,
            ret_eff,
            ret,
        } => {
            hasher.u8(7);
            hash_compiled_signature_type(hasher, param);
            hash_optional_compiled_signature_effect_row(hasher, arg_eff);
            hash_optional_compiled_signature_effect_row(hasher, ret_eff);
            hash_compiled_signature_type(hasher, ret);
        }
    }
}

fn hash_optional_compiled_signature_effect_row(
    hasher: &mut StableHasher,
    row: &Option<infer::CompiledSignatureEffectRow>,
) {
    match row {
        Some(row) => {
            hasher.bool(true);
            hash_compiled_signature_effect_row(hasher, row);
        }
        None => hasher.bool(false),
    }
}

fn hash_compiled_signature_effect_row(
    hasher: &mut StableHasher,
    row: &infer::CompiledSignatureEffectRow,
) {
    hasher.usize(row.items.len());
    for item in &row.items {
        match item {
            infer::CompiledSignatureEffectAtom::Type(ty) => {
                hasher.u8(0);
                hash_compiled_signature_type(hasher, ty);
            }
            infer::CompiledSignatureEffectAtom::Wildcard => hasher.u8(1),
        }
    }
    match &row.tail {
        Some(tail) => {
            hasher.bool(true);
            hasher.string(tail);
        }
        None => hasher.bool(false),
    }
}

fn compiled_runtime_hash(runtime: &infer::CompiledRuntimeSurface) -> u64 {
    let mut hasher = StableHasher::new();
    hasher.bytes(COMPILED_RUNTIME_HASH_SALT);
    hash_poly_arena(&mut hasher, &runtime.arena);
    hasher.usize(runtime.modules.len());
    for module in &runtime.modules {
        hasher.u32(module.module);
        hash_string_path(&mut hasher, &module.module_path);
        hash_def_id(&mut hasher, module.def);
    }
    hasher.usize(runtime.values.len());
    for value in &runtime.values {
        hasher.u32(value.symbol);
        hash_def_id(&mut hasher, value.def);
    }
    hasher.finish()
}

fn compiled_external_runtime_hash(external: &CompiledUnitExternalRuntimeRefs) -> u64 {
    let mut hasher = StableHasher::new();
    hasher.bytes(COMPILED_EXTERNAL_RUNTIME_HASH_SALT);
    hasher.usize(external.imported_def_count);
    hash_def_ids(&mut hasher, &external.defs);
    hasher.usize(external.modules.len());
    for module in &external.modules {
        hasher.u32(module.module);
        hash_string_path(&mut hasher, &module.module_path);
        hash_def_id(&mut hasher, module.def);
    }
    hasher.usize(external.values.len());
    for value in &external.values {
        hasher.u32(value.symbol);
        hash_string_path(&mut hasher, &value.value_path);
        hash_def_id(&mut hasher, value.def);
    }
    hasher.usize(external.type_field_methods.len());
    for method in &external.type_field_methods {
        hash_string_path(&mut hasher, &method.owner_type_path);
        hasher.string(&method.name);
        hash_type_method_receiver(&mut hasher, method.receiver_kind);
        hash_def_id(&mut hasher, method.def);
    }
    hasher.usize(external.casts.len());
    for cast in &external.casts {
        hash_string_path(&mut hasher, &cast.source_type_path);
        hash_string_path(&mut hasher, &cast.target_type_path);
        hasher.u32(cast.ordinal);
        hash_def_id(&mut hasher, cast.def);
    }
    hasher.finish()
}

fn hash_poly_arena(hasher: &mut StableHasher, arena: &poly::expr::Arena) {
    hash_def_ids(hasher, &arena.roots);
    hash_runtime_roots(hasher, &arena.runtime_roots);
    hash_expr_ids(hasher, &arena.root_exprs);
    let mut root_expr_defs = arena.root_expr_defs.iter().collect::<Vec<_>>();
    root_expr_defs.sort_by_key(|(expr, _)| expr.0);
    hasher.usize(root_expr_defs.len());
    for (expr, def) in root_expr_defs {
        hash_expr_id(hasher, *expr);
        hash_def_id(hasher, *def);
    }
    hash_def_arena(hasher, &arena.defs);
    hash_refs(hasher, arena.refs());
    hash_selects(hasher, arena.selects());
    hash_cast_rules(hasher, &arena.cast_rules);
    hash_role_impl_table(hasher, &arena.role_impls);
    hash_effect_operations(hasher, &arena.effect_operations);
    hash_constructors(hasher, &arena.constructors);
    hash_arg_effect_contracts(hasher, &arena.arg_effect_contracts);
    hash_field_projections(hasher, &arena.field_projections);
    hash_exprs(hasher, arena.exprs());
    hash_pats(hasher, arena.pats());
    hash_type_arena(hasher, &arena.typ);
}

fn hash_def_arena(hasher: &mut StableHasher, defs: &poly::expr::DefArena) {
    let mut entries = defs.iter().collect::<Vec<_>>();
    entries.sort_by_key(|(id, _)| id.0);
    hasher.usize(entries.len());
    for (id, def) in entries {
        hash_def_id(hasher, id);
        hash_def(hasher, def);
    }
}

fn hash_def(hasher: &mut StableHasher, def: &poly::expr::Def) {
    match def {
        poly::expr::Def::Mod { vis, children } => {
            hasher.u8(0);
            hash_poly_vis(hasher, *vis);
            hash_def_ids(hasher, children);
        }
        poly::expr::Def::Let {
            vis,
            scheme,
            body,
            children,
        } => {
            hasher.u8(1);
            hash_poly_vis(hasher, *vis);
            hash_optional_scheme(hasher, scheme.as_ref());
            hash_optional_expr_id(hasher, *body);
            hash_def_ids(hasher, children);
        }
        poly::expr::Def::Arg => hasher.u8(2),
    }
}

fn hash_runtime_roots(hasher: &mut StableHasher, roots: &[poly::expr::RuntimeRoot]) {
    hasher.usize(roots.len());
    for root in roots {
        match root {
            poly::expr::RuntimeRoot::Expr(id) => {
                hasher.u8(0);
                hash_expr_id(hasher, *id);
            }
            poly::expr::RuntimeRoot::ComputedDef(id) => {
                hasher.u8(1);
                hash_def_id(hasher, *id);
            }
        }
    }
}

fn hash_refs(hasher: &mut StableHasher, refs: &[Option<poly::expr::DefId>]) {
    hasher.usize(refs.len());
    for target in refs {
        hash_optional_def_id(hasher, *target);
    }
}

fn hash_selects(hasher: &mut StableHasher, selects: &[poly::expr::Select]) {
    hasher.usize(selects.len());
    for select in selects {
        hasher.string(&select.name);
        match select.resolution {
            Some(poly::expr::SelectResolution::RecordField) => {
                hasher.bool(true);
                hasher.u8(0);
            }
            Some(poly::expr::SelectResolution::Method { def }) => {
                hasher.bool(true);
                hasher.u8(1);
                hash_def_id(hasher, def);
            }
            Some(poly::expr::SelectResolution::TypeclassMethod { member }) => {
                hasher.bool(true);
                hasher.u8(2);
                hash_def_id(hasher, member);
            }
            None => hasher.bool(false),
        }
    }
}

fn hash_cast_rules(hasher: &mut StableHasher, rules: &[poly::expr::CastRule]) {
    hasher.usize(rules.len());
    for rule in rules {
        hash_def_id(hasher, rule.def);
        hash_string_path(hasher, &rule.source);
        hash_string_path(hasher, &rule.target);
        hash_scheme(hasher, &rule.scheme);
    }
}

fn hash_role_impl_table(hasher: &mut StableHasher, table: &poly::roles::RoleImplTable) {
    let mut candidates = table
        .iter()
        .map(|candidate| {
            (
                bincode::serialize(candidate)
                    .expect("role impl candidate should be serializable for cache hashing"),
                candidate,
            )
        })
        .collect::<Vec<_>>();
    candidates.sort_by(|left, right| left.0.cmp(&right.0));
    hasher.usize(candidates.len());
    for (bytes, _) in candidates {
        hasher.bytes(&bytes);
    }
}

fn hash_effect_operations<'a>(
    hasher: &mut StableHasher,
    operations: impl IntoIterator<Item = (&'a poly::expr::DefId, &'a poly::expr::EffectOperation)>,
) {
    let mut entries = operations.into_iter().collect::<Vec<_>>();
    entries.sort_by_key(|(def, _)| def.0);
    hasher.usize(entries.len());
    for (def, operation) in entries {
        hash_def_id(hasher, *def);
        hash_string_path(hasher, &operation.path);
    }
}

fn hash_constructors<'a>(
    hasher: &mut StableHasher,
    constructors: impl IntoIterator<Item = (&'a poly::expr::DefId, &'a poly::expr::Constructor)>,
) {
    let mut entries = constructors.into_iter().collect::<Vec<_>>();
    entries.sort_by_key(|(def, _)| def.0);
    hasher.usize(entries.len());
    for (def, constructor) in entries {
        hash_def_id(hasher, *def);
        hash_string_path(hasher, &constructor.owner_path);
        hasher.string(&constructor.name);
        hasher.usize(constructor.arity);
    }
}

fn hash_arg_effect_contracts<'a>(
    hasher: &mut StableHasher,
    contracts: impl IntoIterator<Item = (&'a poly::expr::DefId, &'a poly::expr::ArgEffectContract)>,
) {
    let mut entries = contracts.into_iter().collect::<Vec<_>>();
    entries.sort_by_key(|(def, _)| def.0);
    hasher.usize(entries.len());
    for (def, contract) in entries {
        hash_def_id(hasher, *def);
        hasher.usize(contract.markers.len());
        for marker in &contract.markers {
            hash_string_path(hasher, &marker.path);
            hasher.u32(marker.depth);
            hasher.u8(match marker.resume {
                poly::expr::ContractResumePolicy::PreserveMatchingPath => 0,
                poly::expr::ContractResumePolicy::ForeignOnly => 1,
            });
        }
    }
}

fn hash_field_projections<'a>(
    hasher: &mut StableHasher,
    projections: impl IntoIterator<Item = &'a poly::expr::DefId>,
) {
    let mut defs = projections.into_iter().copied().collect::<Vec<_>>();
    defs.sort_by_key(|def| def.0);
    hash_def_ids(hasher, &defs);
}

fn hash_exprs(hasher: &mut StableHasher, exprs: &[poly::expr::Expr]) {
    hasher.usize(exprs.len());
    for expr in exprs {
        hash_expr(hasher, expr);
    }
}

fn hash_expr(hasher: &mut StableHasher, expr: &poly::expr::Expr) {
    match expr {
        poly::expr::Expr::Lit(lit) => {
            hasher.u8(0);
            hash_lit(hasher, lit);
        }
        poly::expr::Expr::PrimitiveOp(op) => {
            hasher.u8(1);
            hash_primitive_op(hasher, *op);
        }
        poly::expr::Expr::Var(id) => {
            hasher.u8(2);
            hash_ref_id(hasher, *id);
        }
        poly::expr::Expr::App(callee, arg) => {
            hasher.u8(3);
            hash_expr_id(hasher, *callee);
            hash_expr_id(hasher, *arg);
        }
        poly::expr::Expr::RefSet(place, value) => {
            hasher.u8(4);
            hash_expr_id(hasher, *place);
            hash_expr_id(hasher, *value);
        }
        poly::expr::Expr::Lambda(pat, body) => {
            hasher.u8(5);
            hash_pat_id(hasher, *pat);
            hash_expr_id(hasher, *body);
        }
        poly::expr::Expr::Tuple(items) => {
            hasher.u8(6);
            hash_expr_ids(hasher, items);
        }
        poly::expr::Expr::Record { fields, spread } => {
            hasher.u8(7);
            hasher.usize(fields.len());
            for (name, value) in fields {
                hasher.string(name);
                hash_expr_id(hasher, *value);
            }
            hash_expr_record_spread(hasher, spread);
        }
        poly::expr::Expr::PolyVariant(name, payloads) => {
            hasher.u8(8);
            hasher.string(name);
            hash_expr_ids(hasher, payloads);
        }
        poly::expr::Expr::Select(receiver, select) => {
            hasher.u8(9);
            hash_expr_id(hasher, *receiver);
            hash_select_id(hasher, *select);
        }
        poly::expr::Expr::Case(scrutinee, arms) => {
            hasher.u8(10);
            hash_expr_id(hasher, *scrutinee);
            hasher.usize(arms.len());
            for arm in arms {
                hash_pat_id(hasher, arm.pat);
                hash_optional_expr_id(hasher, arm.guard);
                hash_expr_id(hasher, arm.body);
            }
        }
        poly::expr::Expr::Catch(body, arms) => {
            hasher.u8(11);
            hash_expr_id(hasher, *body);
            hasher.usize(arms.len());
            for arm in arms {
                hash_optional_catch_operation(hasher, arm.operation.as_ref());
                hash_pat_id(hasher, arm.pat);
                hash_optional_pat_id(hasher, arm.continuation);
                hash_optional_expr_id(hasher, arm.guard);
                hash_expr_id(hasher, arm.body);
            }
        }
        poly::expr::Expr::Block(stmts, tail) => {
            hasher.u8(12);
            hasher.usize(stmts.len());
            for stmt in stmts {
                hash_stmt(hasher, stmt);
            }
            hash_optional_expr_id(hasher, *tail);
        }
    }
}

fn hash_stmt(hasher: &mut StableHasher, stmt: &poly::expr::Stmt) {
    match stmt {
        poly::expr::Stmt::Let(vis, pat, value) => {
            hasher.u8(0);
            hash_poly_vis(hasher, *vis);
            hash_pat_id(hasher, *pat);
            hash_expr_id(hasher, *value);
        }
        poly::expr::Stmt::Expr(expr) => {
            hasher.u8(1);
            hash_expr_id(hasher, *expr);
        }
        poly::expr::Stmt::Module(def, stmts) => {
            hasher.u8(2);
            hash_def_id(hasher, *def);
            hasher.usize(stmts.len());
            for stmt in stmts {
                hash_stmt(hasher, stmt);
            }
        }
    }
}

fn hash_pats(hasher: &mut StableHasher, pats: &[poly::expr::Pat]) {
    hasher.usize(pats.len());
    for pat in pats {
        hash_pat(hasher, pat);
    }
}

fn hash_pat(hasher: &mut StableHasher, pat: &poly::expr::Pat) {
    match pat {
        poly::expr::Pat::Wild => hasher.u8(0),
        poly::expr::Pat::Lit(lit) => {
            hasher.u8(1);
            hash_lit(hasher, lit);
        }
        poly::expr::Pat::Tuple(items) => {
            hasher.u8(2);
            hash_pat_ids(hasher, items);
        }
        poly::expr::Pat::List {
            prefix,
            spread,
            suffix,
        } => {
            hasher.u8(3);
            hash_pat_ids(hasher, prefix);
            hash_optional_pat_id(hasher, *spread);
            hash_pat_ids(hasher, suffix);
        }
        poly::expr::Pat::Record { fields, spread } => {
            hasher.u8(4);
            hasher.usize(fields.len());
            for field in fields {
                hasher.string(&field.name);
                hash_pat_id(hasher, field.pat);
                hash_optional_expr_id(hasher, field.default);
            }
            hash_def_record_spread(hasher, spread);
        }
        poly::expr::Pat::PolyVariant(name, payloads) => {
            hasher.u8(5);
            hasher.string(name);
            hash_pat_ids(hasher, payloads);
        }
        poly::expr::Pat::Con(target, payloads) => {
            hasher.u8(6);
            hash_ref_id(hasher, *target);
            hash_pat_ids(hasher, payloads);
        }
        poly::expr::Pat::Ref(target) => {
            hasher.u8(7);
            hash_ref_id(hasher, *target);
        }
        poly::expr::Pat::Var(def) => {
            hasher.u8(8);
            hash_def_id(hasher, *def);
        }
        poly::expr::Pat::Or(left, right) => {
            hasher.u8(9);
            hash_pat_id(hasher, *left);
            hash_pat_id(hasher, *right);
        }
        poly::expr::Pat::As(inner, def) => {
            hasher.u8(10);
            hash_pat_id(hasher, *inner);
            hash_def_id(hasher, *def);
        }
    }
}

fn hash_lit(hasher: &mut StableHasher, lit: &poly::expr::Lit) {
    match lit {
        poly::expr::Lit::Int(value) => {
            hasher.u8(0);
            hasher.i64(*value);
        }
        poly::expr::Lit::BigInt(value) => {
            hasher.u8(1);
            hasher.bytes(&value.to_signed_bytes_le());
        }
        poly::expr::Lit::Float(value) => {
            hasher.u8(2);
            hasher.u64(value.to_bits());
        }
        poly::expr::Lit::Str(value) => {
            hasher.u8(3);
            hasher.string(value);
        }
        poly::expr::Lit::Bool(value) => {
            hasher.u8(4);
            hasher.bool(*value);
        }
        poly::expr::Lit::Unit => hasher.u8(5),
    }
}

fn hash_optional_catch_operation(
    hasher: &mut StableHasher,
    operation: Option<&poly::expr::CatchOperation>,
) {
    match operation {
        Some(operation) => {
            hasher.bool(true);
            hash_string_path(hasher, &operation.path);
            hash_optional_def_id(hasher, operation.def);
        }
        None => hasher.bool(false),
    }
}

fn hash_expr_record_spread(
    hasher: &mut StableHasher,
    spread: &poly::expr::RecordSpread<poly::expr::ExprId>,
) {
    match spread {
        poly::expr::RecordSpread::Head(id) => {
            hasher.u8(0);
            hash_expr_id(hasher, *id);
        }
        poly::expr::RecordSpread::Tail(id) => {
            hasher.u8(1);
            hash_expr_id(hasher, *id);
        }
        poly::expr::RecordSpread::None => hasher.u8(2),
    }
}

fn hash_def_record_spread(
    hasher: &mut StableHasher,
    spread: &poly::expr::RecordSpread<poly::expr::DefId>,
) {
    match spread {
        poly::expr::RecordSpread::Head(id) => {
            hasher.u8(0);
            hash_def_id(hasher, *id);
        }
        poly::expr::RecordSpread::Tail(id) => {
            hasher.u8(1);
            hash_def_id(hasher, *id);
        }
        poly::expr::RecordSpread::None => hasher.u8(2),
    }
}

fn hash_type_arena(hasher: &mut StableHasher, types: &poly::types::TypeArena) {
    hasher.usize(types.pos_nodes().len());
    for node in types.pos_nodes() {
        hash_pos(hasher, node);
    }
    hasher.usize(types.neg_nodes().len());
    for node in types.neg_nodes() {
        hash_neg(hasher, node);
    }
    hasher.usize(types.neu_nodes().len());
    for node in types.neu_nodes() {
        hash_neu(hasher, node);
    }
}

fn hash_optional_scheme(hasher: &mut StableHasher, scheme: Option<&poly::types::Scheme>) {
    match scheme {
        Some(scheme) => {
            hasher.bool(true);
            hash_scheme(hasher, scheme);
        }
        None => hasher.bool(false),
    }
}

fn hash_compiled_type_arena(hasher: &mut StableHasher, types: &infer::CompiledTypeArena) {
    hasher.usize(types.pos.len());
    for node in &types.pos {
        hash_pos(hasher, node);
    }
    hasher.usize(types.neg.len());
    for node in &types.neg {
        hash_neg(hasher, node);
    }
    hasher.usize(types.neu.len());
    for node in &types.neu {
        hash_neu(hasher, node);
    }
}

fn hash_scheme(hasher: &mut StableHasher, scheme: &poly::types::Scheme) {
    hasher.usize(scheme.quantifiers.len());
    for var in &scheme.quantifiers {
        hash_type_var(hasher, *var);
    }
    hasher.usize(scheme.role_predicates.len());
    for predicate in &scheme.role_predicates {
        hash_role_predicate(hasher, predicate);
    }
    hasher.usize(scheme.recursive_bounds.len());
    for bound in &scheme.recursive_bounds {
        hash_type_var(hasher, bound.var);
        hash_neu_id(hasher, bound.bounds);
    }
    hasher.usize(scheme.stack_quantifiers.len());
    for id in &scheme.stack_quantifiers {
        hash_subtract_id(hasher, *id);
    }
    hash_pos_id(hasher, scheme.predicate);
}

fn hash_role_predicate(hasher: &mut StableHasher, predicate: &poly::types::RolePredicate) {
    hash_string_path(hasher, &predicate.role);
    hasher.usize(predicate.inputs.len());
    for input in &predicate.inputs {
        match input {
            poly::types::RolePredicateArg::Covariant(id) => {
                hasher.u8(0);
                hash_pos_id(hasher, *id);
            }
            poly::types::RolePredicateArg::Contravariant(id) => {
                hasher.u8(1);
                hash_neg_id(hasher, *id);
            }
            poly::types::RolePredicateArg::Invariant(id) => {
                hasher.u8(2);
                hash_neu_id(hasher, *id);
            }
        }
    }
    hasher.usize(predicate.associated.len());
    for associated in &predicate.associated {
        hasher.string(&associated.name);
        hash_neu_id(hasher, associated.value);
    }
}

fn hash_pos(hasher: &mut StableHasher, pos: &poly::types::Pos) {
    match pos {
        poly::types::Pos::Bot => hasher.u8(0),
        poly::types::Pos::Var(var) => {
            hasher.u8(1);
            hash_type_var(hasher, *var);
        }
        poly::types::Pos::Con(path, args) => {
            hasher.u8(2);
            hash_string_path(hasher, path);
            hash_neu_ids(hasher, args);
        }
        poly::types::Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            hasher.u8(3);
            hash_neg_id(hasher, *arg);
            hash_neg_id(hasher, *arg_eff);
            hash_pos_id(hasher, *ret_eff);
            hash_pos_id(hasher, *ret);
        }
        poly::types::Pos::Record(fields) => {
            hasher.u8(4);
            hash_record_fields(hasher, fields, hash_pos_id);
        }
        poly::types::Pos::RecordTailSpread { fields, tail } => {
            hasher.u8(5);
            hash_record_fields(hasher, fields, hash_pos_id);
            hash_pos_id(hasher, *tail);
        }
        poly::types::Pos::RecordHeadSpread { tail, fields } => {
            hasher.u8(6);
            hash_pos_id(hasher, *tail);
            hash_record_fields(hasher, fields, hash_pos_id);
        }
        poly::types::Pos::PolyVariant(variants) => {
            hasher.u8(7);
            hash_variant_pos_fields(hasher, variants);
        }
        poly::types::Pos::Tuple(items) => {
            hasher.u8(8);
            hash_pos_ids(hasher, items);
        }
        poly::types::Pos::Row(items) => {
            hasher.u8(9);
            hash_pos_ids(hasher, items);
        }
        poly::types::Pos::Stack { inner, weight } => {
            hasher.u8(10);
            hash_pos_id(hasher, *inner);
            hash_stack_weight(hasher, weight);
        }
        poly::types::Pos::NonSubtract(inner, weight) => {
            hasher.u8(11);
            hash_pos_id(hasher, *inner);
            hash_stack_weight(hasher, weight);
        }
        poly::types::Pos::Union(left, right) => {
            hasher.u8(12);
            hash_pos_id(hasher, *left);
            hash_pos_id(hasher, *right);
        }
    }
}

fn hash_neg(hasher: &mut StableHasher, neg: &poly::types::Neg) {
    match neg {
        poly::types::Neg::Top => hasher.u8(0),
        poly::types::Neg::Bot => hasher.u8(1),
        poly::types::Neg::Var(var) => {
            hasher.u8(2);
            hash_type_var(hasher, *var);
        }
        poly::types::Neg::Con(path, args) => {
            hasher.u8(3);
            hash_string_path(hasher, path);
            hash_neu_ids(hasher, args);
        }
        poly::types::Neg::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            hasher.u8(4);
            hash_pos_id(hasher, *arg);
            hash_pos_id(hasher, *arg_eff);
            hash_neg_id(hasher, *ret_eff);
            hash_neg_id(hasher, *ret);
        }
        poly::types::Neg::Record(fields) => {
            hasher.u8(5);
            hash_record_fields(hasher, fields, hash_neg_id);
        }
        poly::types::Neg::PolyVariant(variants) => {
            hasher.u8(6);
            hash_variant_neg_fields(hasher, variants);
        }
        poly::types::Neg::Tuple(items) => {
            hasher.u8(7);
            hash_neg_ids(hasher, items);
        }
        poly::types::Neg::Row(items, tail) => {
            hasher.u8(8);
            hash_neg_ids(hasher, items);
            hash_neg_id(hasher, *tail);
        }
        poly::types::Neg::Stack { inner, weight } => {
            hasher.u8(9);
            hash_neg_id(hasher, *inner);
            hash_stack_weight(hasher, weight);
        }
        poly::types::Neg::Intersection(left, right) => {
            hasher.u8(10);
            hash_neg_id(hasher, *left);
            hash_neg_id(hasher, *right);
        }
    }
}

fn hash_neu(hasher: &mut StableHasher, neu: &poly::types::Neu) {
    match neu {
        poly::types::Neu::Bounds(lower, upper) => {
            hasher.u8(0);
            hash_pos_id(hasher, *lower);
            hash_neg_id(hasher, *upper);
        }
        poly::types::Neu::Con(path, args) => {
            hasher.u8(1);
            hash_string_path(hasher, path);
            hash_neu_ids(hasher, args);
        }
        poly::types::Neu::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            hasher.u8(2);
            hash_neu_id(hasher, *arg);
            hash_neu_id(hasher, *arg_eff);
            hash_neu_id(hasher, *ret_eff);
            hash_neu_id(hasher, *ret);
        }
        poly::types::Neu::Record(fields) => {
            hasher.u8(3);
            hash_record_fields(hasher, fields, hash_neu_id);
        }
        poly::types::Neu::PolyVariant(variants) => {
            hasher.u8(4);
            hash_variant_neu_fields(hasher, variants);
        }
        poly::types::Neu::Tuple(items) => {
            hasher.u8(5);
            hash_neu_ids(hasher, items);
        }
    }
}

fn hash_record_fields<T: Copy>(
    hasher: &mut StableHasher,
    fields: &[poly::types::RecordField<T>],
    hash_value: fn(&mut StableHasher, T),
) {
    hasher.usize(fields.len());
    for field in fields {
        hasher.string(&field.name);
        hasher.bool(field.optional);
        hash_value(hasher, field.value);
    }
}

fn hash_variant_pos_fields(
    hasher: &mut StableHasher,
    variants: &[(String, Vec<poly::types::PosId>)],
) {
    hasher.usize(variants.len());
    for (name, fields) in variants {
        hasher.string(name);
        hash_pos_ids(hasher, fields);
    }
}

fn hash_variant_neg_fields(
    hasher: &mut StableHasher,
    variants: &[(String, Vec<poly::types::NegId>)],
) {
    hasher.usize(variants.len());
    for (name, fields) in variants {
        hasher.string(name);
        hash_neg_ids(hasher, fields);
    }
}

fn hash_variant_neu_fields(
    hasher: &mut StableHasher,
    variants: &[(String, Vec<poly::types::NeuId>)],
) {
    hasher.usize(variants.len());
    for (name, fields) in variants {
        hasher.string(name);
        hash_neu_ids(hasher, fields);
    }
}

fn hash_stack_weight(hasher: &mut StableHasher, weight: &poly::types::StackWeight) {
    hash_subtractability(hasher, weight.filter_set());
    hasher.usize(weight.entries().len());
    for entry in weight.entries() {
        hash_subtract_id(hasher, entry.id);
        hasher.u32(entry.pops);
        hasher.usize(entry.floor.len());
        for subtractability in &entry.floor {
            hash_subtractability(hasher, subtractability);
        }
        hasher.usize(entry.stack.len());
        for subtractability in &entry.stack {
            hash_subtractability(hasher, subtractability);
        }
    }
}

fn hash_subtractability(hasher: &mut StableHasher, subtractability: &poly::types::Subtractability) {
    match subtractability {
        poly::types::Subtractability::Empty => hasher.u8(0),
        poly::types::Subtractability::All => hasher.u8(1),
        poly::types::Subtractability::AllExcept(path, args) => {
            hasher.u8(2);
            hash_string_path(hasher, path);
            hash_neu_ids(hasher, args);
        }
        poly::types::Subtractability::AllExceptMany(families) => {
            hasher.u8(3);
            hash_effect_families(hasher, families);
        }
        poly::types::Subtractability::Set(path, args) => {
            hasher.u8(4);
            hash_string_path(hasher, path);
            hash_neu_ids(hasher, args);
        }
        poly::types::Subtractability::SetMany(families) => {
            hasher.u8(5);
            hash_effect_families(hasher, families);
        }
    }
}

fn hash_effect_families(
    hasher: &mut StableHasher,
    families: &[(Vec<String>, Vec<poly::types::NeuId>)],
) {
    hasher.usize(families.len());
    for (path, args) in families {
        hash_string_path(hasher, path);
        hash_neu_ids(hasher, args);
    }
}

fn hash_pos_ids(hasher: &mut StableHasher, ids: &[poly::types::PosId]) {
    hasher.usize(ids.len());
    for id in ids {
        hash_pos_id(hasher, *id);
    }
}

fn hash_neg_ids(hasher: &mut StableHasher, ids: &[poly::types::NegId]) {
    hasher.usize(ids.len());
    for id in ids {
        hash_neg_id(hasher, *id);
    }
}

fn hash_neu_ids(hasher: &mut StableHasher, ids: &[poly::types::NeuId]) {
    hasher.usize(ids.len());
    for id in ids {
        hash_neu_id(hasher, *id);
    }
}

fn hash_pos_id(hasher: &mut StableHasher, id: poly::types::PosId) {
    hasher.u32(id.0);
}

fn hash_neg_id(hasher: &mut StableHasher, id: poly::types::NegId) {
    hasher.u32(id.0);
}

fn hash_neu_id(hasher: &mut StableHasher, id: poly::types::NeuId) {
    hasher.u32(id.0);
}

fn hash_type_var(hasher: &mut StableHasher, var: poly::types::TypeVar) {
    hasher.u32(var.0);
}

fn hash_subtract_id(hasher: &mut StableHasher, id: poly::types::SubtractId) {
    hasher.u32(id.0);
}

fn hash_def_ids(hasher: &mut StableHasher, ids: &[poly::expr::DefId]) {
    hasher.usize(ids.len());
    for id in ids {
        hash_def_id(hasher, *id);
    }
}

fn hash_expr_ids(hasher: &mut StableHasher, ids: &[poly::expr::ExprId]) {
    hasher.usize(ids.len());
    for id in ids {
        hash_expr_id(hasher, *id);
    }
}

fn hash_pat_ids(hasher: &mut StableHasher, ids: &[poly::expr::PatId]) {
    hasher.usize(ids.len());
    for id in ids {
        hash_pat_id(hasher, *id);
    }
}

fn hash_def_id(hasher: &mut StableHasher, id: poly::expr::DefId) {
    hasher.u32(id.0);
}

fn hash_expr_id(hasher: &mut StableHasher, id: poly::expr::ExprId) {
    hasher.u32(id.0);
}

fn hash_pat_id(hasher: &mut StableHasher, id: poly::expr::PatId) {
    hasher.u32(id.0);
}

fn hash_ref_id(hasher: &mut StableHasher, id: poly::expr::RefId) {
    hasher.u32(id.0);
}

fn hash_select_id(hasher: &mut StableHasher, id: poly::expr::SelectId) {
    hasher.u32(id.0);
}

fn hash_optional_def_id(hasher: &mut StableHasher, id: Option<poly::expr::DefId>) {
    match id {
        Some(id) => {
            hasher.bool(true);
            hash_def_id(hasher, id);
        }
        None => hasher.bool(false),
    }
}

fn hash_optional_expr_id(hasher: &mut StableHasher, id: Option<poly::expr::ExprId>) {
    match id {
        Some(id) => {
            hasher.bool(true);
            hash_expr_id(hasher, id);
        }
        None => hasher.bool(false),
    }
}

fn hash_optional_pat_id(hasher: &mut StableHasher, id: Option<poly::expr::PatId>) {
    match id {
        Some(id) => {
            hasher.bool(true);
            hash_pat_id(hasher, id);
        }
        None => hasher.bool(false),
    }
}

fn hash_poly_vis(hasher: &mut StableHasher, visibility: poly::expr::Vis) {
    hasher.u8(match visibility {
        poly::expr::Vis::Pub => 0,
        poly::expr::Vis::Our => 1,
        poly::expr::Vis::My => 2,
    });
}

fn hash_primitive_op(hasher: &mut StableHasher, op: poly::expr::PrimitiveOp) {
    hasher.u8(op as u8);
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

fn hash_type_method_receiver(hasher: &mut StableHasher, receiver: infer::TypeMethodReceiver) {
    hasher.u8(match receiver {
        infer::TypeMethodReceiver::Value => 0,
        infer::TypeMethodReceiver::Ref => 1,
    });
}

fn hash_use_import(hasher: &mut StableHasher, import: &sources::UseImport) {
    match import {
        sources::UseImport::Alias {
            name,
            path,
            route,
            version,
            anchor,
        } => {
            hasher.u8(0);
            hasher.string(&name.0);
            hash_module_path(hasher, path);
            hash_use_path_route(hasher, *route);
            hash_optional_string(hasher, version.as_deref());
            hash_use_anchor(hasher, anchor.as_ref());
        }
        sources::UseImport::Glob {
            prefix,
            route,
            version,
            anchor,
        } => {
            hasher.u8(1);
            hash_module_path(hasher, prefix);
            hash_use_path_route(hasher, *route);
            hash_optional_string(hasher, version.as_deref());
            hash_use_anchor(hasher, anchor.as_ref());
        }
    }
}

fn hash_use_anchor(hasher: &mut StableHasher, anchor: Option<&sources::UseAnchor>) {
    match anchor {
        Some(anchor) => {
            hasher.bool(true);
            hash_module_path(hasher, &anchor.path);
            hash_use_path_route(hasher, anchor.route);
        }
        None => hasher.bool(false),
    }
}

fn hash_use_path_route(hasher: &mut StableHasher, route: sources::UsePathRoute) {
    match route {
        sources::UsePathRoute::Relative => hasher.u8(0),
        sources::UsePathRoute::CurrentBand => hasher.u8(1),
        sources::UsePathRoute::CurrentRealm { band_segments } => {
            hasher.u8(2);
            hasher.usize(band_segments);
        }
        sources::UsePathRoute::SlashQualified { prefix_segments } => {
            hasher.u8(3);
            hasher.usize(prefix_segments);
        }
    }
}

fn hash_optional_string(hasher: &mut StableHasher, value: Option<&str>) {
    match value {
        Some(value) => {
            hasher.bool(true);
            hasher.string(value);
        }
        None => hasher.bool(false),
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
struct MonoCacheEnvelope<T = specialize::mono::Program, E = Vec<String>> {
    format: u32,
    program: T,
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
    L = infer::CompiledLoweringSurface,
    T = infer::CompiledTypedSurface,
    R = infer::CompiledRuntimeSurface,
    X = CompiledUnitExternalRuntimeRefs,
    E = Vec<String>,
> {
    format: u32,
    manifest: M,
    syntax: S,
    namespace: N,
    lowering: L,
    typed: T,
    runtime: R,
    external_runtime: X,
    errors: E,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct RealmResolutionCacheEnvelope<
    R = sources::ResolvedRealmId,
    Q = sources::UseImport,
    T = CachedRealmResolutionTarget,
> {
    format: u32,
    key_hash: u64,
    source_realm: R,
    request: Q,
    target: T,
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

impl<T, E> CacheEnvelope for MonoCacheEnvelope<T, E> {
    fn format(&self) -> u32 {
        self.format
    }
}

impl<T, L, E> CacheEnvelope for ControlCacheEnvelope<T, L, E> {
    fn format(&self) -> u32 {
        self.format
    }
}

impl<M, S, N, L, T, R, X, E> CacheEnvelope for CompiledUnitCacheEnvelope<M, S, N, L, T, R, X, E> {
    fn format(&self) -> u32 {
        self.format
    }
}

impl<R, Q, T> CacheEnvelope for RealmResolutionCacheEnvelope<R, Q, T> {
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

    fn u64(&mut self, value: u64) {
        self.bytes(&value.to_le_bytes());
    }

    fn i64(&mut self, value: i64) {
        self.bytes(&value.to_le_bytes());
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
    fn source_cache_key_tracks_resolution_import_metadata() {
        let base = source("main.yu", &[], "use ui/widget::a with program::ui\n");
        let mut with_request = base.clone();
        with_request
            .resolution_imports
            .push(sources::UseImport::Alias {
                name: Name("a".into()),
                path: Path {
                    segments: vec![Name("ui".into()), Name("widget".into()), Name("a".into())],
                },
                route: sources::UsePathRoute::SlashQualified { prefix_segments: 2 },
                version: None,
                anchor: Some(sources::UseAnchor {
                    path: Path {
                        segments: vec![Name("program".into()), Name("ui".into())],
                    },
                    route: sources::UsePathRoute::Relative,
                }),
            });

        assert_ne!(source_cache_key(&[base]), source_cache_key(&[with_request]));
    }

    #[test]
    fn source_cache_key_tracks_band_path() {
        let default_band = source("helper.yu", &["helper"], "pub value = 1\n");
        let current_realm_band = CollectedSource::with_band_path(
            PathBuf::from("helper.yu"),
            path(&["helper"]),
            path(&["helper"]),
            "pub value = 1\n".to_string(),
        );

        assert_ne!(
            source_cache_key(&[default_band]),
            source_cache_key(&[current_realm_band])
        );
    }

    #[test]
    fn realm_resolution_cache_key_tracks_source_band_path() {
        let request = sources::UseImport::Alias {
            name: Name("value".into()),
            path: path(&["nested", "value"]),
            route: sources::UsePathRoute::CurrentRealm { band_segments: 1 },
            version: None,
            anchor: None,
        };
        let default_band = CollectedSource::with_resolution_imports(
            PathBuf::from("helper.yu"),
            path(&["helper"]),
            "use realm/nested::value\nvalue\n".to_string(),
            vec![request.clone()],
        );
        let current_realm_band = CollectedSource::with_band_path_and_resolution_imports(
            PathBuf::from("helper.yu"),
            path(&["helper"]),
            path(&["helper"]),
            "use realm/nested::value\nvalue\n".to_string(),
            vec![request.clone()],
        );

        assert_ne!(
            realm_resolution_cache_key(&default_band, &request),
            realm_resolution_cache_key(&current_realm_band, &request)
        );
    }

    #[test]
    fn source_unit_cache_key_tracks_band_path() {
        let default_band = vec![source("helper.yu", &["helper"], "pub value = 1\n")];
        let current_realm_band = vec![CollectedSource::with_band_path(
            PathBuf::from("helper.yu"),
            path(&["helper"]),
            path(&["helper"]),
            "pub value = 1\n".to_string(),
        )];
        let default_units = crate::source::source_compilation_units(&default_band);
        let current_realm_units = crate::source::source_compilation_units(&current_realm_band);

        assert_ne!(
            source_compilation_unit_cache_keys(&default_band, &default_units),
            source_compilation_unit_cache_keys(&current_realm_band, &current_realm_units)
        );
    }

    #[test]
    fn realm_resolution_cache_round_trips_under_source_realm() {
        let root = temp_root("realm-resolution-round-trip");
        let cache = ArtifactCache::new(&root);
        let source_realm = realm_id("file:///app", None);
        let request = slash_import_request();
        let file = source("main.yu", &[], "use ui/widget::a with program::ui\n");
        let key = realm_resolution_cache_key(&file, &request);
        let artifact = CachedRealmResolutionArtifact {
            source_realm: source_realm.clone(),
            request: request.clone(),
            target: CachedRealmResolutionTarget {
                realm: realm_id("github.com/user/ui", Some("1.2.3")),
                band_path: path(&["widget"]),
                module_path: path(&["a"]),
                source_path: "widget.yu".into(),
                source_len: 12,
                source_hash: 0x1234,
            },
        };

        cache
            .write_realm_resolution_artifact(&source_realm, key, &artifact)
            .unwrap();
        let restored = cache
            .read_realm_resolution_artifact(&source_realm, key)
            .unwrap()
            .unwrap();

        assert_eq!(restored, artifact);
        assert!(
            cache
                .realm_resolution_artifact_path(&source_realm, key)
                .to_string_lossy()
                .contains("realms")
        );

        let _ = std::fs::remove_dir_all(&root);
    }

    #[test]
    fn current_realm_resolution_artifacts_are_populated_from_collected_sources() {
        let root = temp_root("current-realm-resolution-populate");
        std::fs::create_dir_all(&root).unwrap();
        let cache = ArtifactCache::new(root.join("cache"));
        let main_path = root.join("main.yu");
        let helper_path = root.join("helper.yu");
        let request = sources::UseImport::Alias {
            name: Name("value".into()),
            path: path(&["helper", "value"]),
            route: sources::UsePathRoute::CurrentRealm { band_segments: 1 },
            version: None,
            anchor: None,
        };
        let main = CollectedSource::with_resolution_imports(
            main_path.clone(),
            Path::default(),
            "use realm/helper::value\nvalue\n".to_string(),
            vec![request.clone()],
        );
        let helper = CollectedSource::with_band_path(
            helper_path,
            path(&["helper"]),
            path(&["helper"]),
            "pub value = 7\n".to_string(),
        );
        let files = vec![main.clone(), helper.clone()];
        let source_realm = sources::local_realm_id(&main_path);
        let key = realm_resolution_cache_key(&main, &request);

        assert_eq!(
            write_current_realm_resolution_artifacts(&cache, &files).unwrap(),
            1
        );
        assert_eq!(
            write_current_realm_resolution_artifacts(&cache, &files).unwrap(),
            0
        );

        let restored = cache
            .read_realm_resolution_artifact(&source_realm, key)
            .unwrap()
            .unwrap();
        assert_eq!(restored.source_realm, source_realm);
        assert_eq!(restored.request, request);
        assert_eq!(restored.target.realm, source_realm);
        assert_eq!(restored.target.band_path, path(&["helper"]));
        assert_eq!(restored.target.module_path, path(&["helper"]));
        assert_eq!(restored.target.source_len, helper.source.len());
        assert_eq!(restored.target.source_hash, source_file_hash(&helper));

        let _ = std::fs::remove_dir_all(&root);
    }

    #[test]
    fn installed_realm_resolution_artifacts_are_populated_from_collected_sources() {
        let root = temp_root("installed-realm-resolution-populate");
        std::fs::create_dir_all(&root).unwrap();
        let cache = ArtifactCache::new(root.join("cache"));
        let installed_root = root
            .join("lib")
            .join("realms")
            .join("local")
            .join("theme")
            .join("1.0.0");
        std::fs::create_dir_all(&installed_root).unwrap();
        let snapshot = sources::FrozenRealmSnapshot {
            format_version: 2,
            identity: sources::RealmIdentity("local/theme".into()),
            version: sources::RealmVersion("1.0.0".into()),
            source_hash: 0xabc,
            files: Vec::new(),
        };
        std::fs::write(
            installed_root.join("snapshot.json"),
            serde_json::to_string(&snapshot).unwrap(),
        )
        .unwrap();
        let main_path = root.join("main.yu");
        let target_path = installed_root.join("colors.yu");
        let request = sources::UseImport::Alias {
            name: Name("value".into()),
            path: path(&["local", "theme", "colors", "value"]),
            route: sources::UsePathRoute::SlashQualified { prefix_segments: 3 },
            version: Some("v1.0.0".into()),
            anchor: None,
        };
        let main = CollectedSource::with_resolution_imports(
            main_path.clone(),
            Path::default(),
            "use local/theme/colors::value v1.0.0\nvalue\n".to_string(),
            vec![request.clone()],
        );
        let target = CollectedSource::with_band_path(
            target_path,
            path(&["local", "theme", "colors"]),
            path(&["local", "theme", "colors"]),
            "pub value = 7\n".to_string(),
        );
        let files = vec![main.clone(), target.clone()];
        let source_realm = sources::local_realm_id(&main_path);
        let key = realm_resolution_cache_key(&main, &request);

        assert_eq!(write_realm_resolution_artifacts(&cache, &files).unwrap(), 1);

        let restored = cache
            .read_realm_resolution_artifact(&source_realm, key)
            .unwrap()
            .unwrap();
        assert_eq!(
            restored.target.realm,
            realm_id("local/theme", Some("1.0.0"))
        );
        assert_eq!(
            restored.target.band_path,
            path(&["local", "theme", "colors"])
        );
        assert_eq!(
            restored.target.module_path,
            path(&["local", "theme", "colors"])
        );
        assert_eq!(restored.target.source_hash, source_file_hash(&target));

        let _ = std::fs::remove_dir_all(&root);
    }

    #[test]
    fn current_realm_resolution_artifacts_require_target_band_path() {
        let root = temp_root("current-realm-resolution-target-band");
        std::fs::create_dir_all(&root).unwrap();
        let cache = ArtifactCache::new(root.join("cache"));
        let main_path = root.join("main.yu");
        let helper_path = root.join("helper.yu");
        let request = sources::UseImport::Alias {
            name: Name("value".into()),
            path: path(&["helper", "value"]),
            route: sources::UsePathRoute::CurrentRealm { band_segments: 1 },
            version: None,
            anchor: None,
        };
        let main = CollectedSource::with_resolution_imports(
            main_path,
            Path::default(),
            "use realm/helper::value\nvalue\n".to_string(),
            vec![request],
        );
        let helper = CollectedSource::new(
            helper_path,
            path(&["helper"]),
            "pub value = 7\n".to_string(),
        );

        assert_eq!(
            write_current_realm_resolution_artifacts(&cache, &[main, helper]).unwrap(),
            0
        );

        let _ = std::fs::remove_dir_all(&root);
    }

    #[test]
    fn source_unit_closure_artifact_preserves_current_realm_band_path() {
        let request = sources::UseImport::Alias {
            name: Name("run".into()),
            path: path(&["helper", "run"]),
            route: sources::UsePathRoute::CurrentRealm { band_segments: 1 },
            version: None,
            anchor: None,
        };
        let files = vec![
            CollectedSource::with_resolution_imports(
                PathBuf::from("main.yu"),
                Path::default(),
                "use realm/helper::run\nmy x = run\n".to_string(),
                vec![request],
            ),
            CollectedSource::with_band_path(
                PathBuf::from("helper.yu"),
                path(&["helper"]),
                path(&["helper"]),
                "mod inner;\nuse band::inner::value\npub run = value\n".to_string(),
            ),
            CollectedSource::with_band_path(
                PathBuf::from("helper/inner.yu"),
                path(&["helper", "inner"]),
                path(&["helper"]),
                "our value = 1\n".to_string(),
            ),
        ];
        let units = crate::source::source_compilation_units(&files);
        let helper_unit = units.unit_for_file(1).unwrap();

        let artifact =
            compiled_unit_artifact_from_source_unit_closure(&files, &units, helper_unit).unwrap();

        assert_eq!(artifact.errors, Vec::<String>::new());
        assert_eq!(
            artifact
                .namespace
                .modules
                .iter()
                .find(|module| module.path == vec!["helper".to_string()])
                .map(|module| module.band_path.clone()),
            Some(vec!["helper".to_string()])
        );
        assert_eq!(
            artifact
                .namespace
                .modules
                .iter()
                .find(|module| module.path == vec!["helper".to_string(), "inner".to_string()])
                .map(|module| module.band_path.clone()),
            Some(vec!["helper".to_string()])
        );
        let namespace = infer::CompiledNamespaceIndex::new(&artifact.namespace);
        assert!(
            namespace
                .exported_value_symbol(&["helper".to_string()], "run")
                .is_some()
        );
    }

    #[test]
    fn realm_resolution_cache_path_is_split_by_source_realm() {
        let root = temp_root("realm-resolution-source-realm");
        let cache = ArtifactCache::new(&root);
        let request = slash_import_request();
        let file = source("main.yu", &[], "use ui/widget::a\n");
        let key = realm_resolution_cache_key(&file, &request);

        assert_ne!(
            cache.realm_resolution_artifact_path(&realm_id("file:///left", None), key),
            cache.realm_resolution_artifact_path(&realm_id("file:///right", None), key)
        );
    }

    #[test]
    fn source_unit_cache_keys_track_dependency_unit_hashes() {
        let base = module_chain_sources("mod a;\nx\n", "mod b;\npub x = b::y\n", "pub y = 7\n");
        let base_units = crate::source::source_compilation_units(&base);
        let base_keys = source_compilation_unit_cache_keys(&base, &base_units);
        let base_root = base_units.unit_for_file(0).unwrap();
        let base_a = base_units.unit_for_file(1).unwrap();
        let base_b = base_units.unit_for_file(2).unwrap();

        let changed_leaf =
            module_chain_sources("mod a;\nx\n", "mod b;\npub x = b::y\n", "pub y = 8\n");
        let changed_leaf_units = crate::source::source_compilation_units(&changed_leaf);
        let changed_leaf_keys =
            source_compilation_unit_cache_keys(&changed_leaf, &changed_leaf_units);
        assert_ne!(
            base_keys[base_b],
            changed_leaf_keys[changed_leaf_units.unit_for_file(2).unwrap()]
        );
        assert_ne!(
            base_keys[base_a],
            changed_leaf_keys[changed_leaf_units.unit_for_file(1).unwrap()]
        );
        assert_ne!(
            base_keys[base_root],
            changed_leaf_keys[changed_leaf_units.unit_for_file(0).unwrap()]
        );

        let changed_root =
            module_chain_sources("mod a;\n1\n", "mod b;\npub x = b::y\n", "pub y = 7\n");
        let changed_root_units = crate::source::source_compilation_units(&changed_root);
        let changed_root_keys =
            source_compilation_unit_cache_keys(&changed_root, &changed_root_units);
        assert_eq!(
            base_keys[base_b],
            changed_root_keys[changed_root_units.unit_for_file(2).unwrap()]
        );
        assert_eq!(
            base_keys[base_a],
            changed_root_keys[changed_root_units.unit_for_file(1).unwrap()]
        );
        assert_ne!(
            base_keys[base_root],
            changed_root_keys[changed_root_units.unit_for_file(0).unwrap()]
        );
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
    fn mono_cache_round_trips_binary_artifact_envelope() {
        let root = temp_root("mono-round-trip");
        let cache = ArtifactCache::new(&root);
        let key = source_cache_key(&[source("main.yu", &[], "1\n")]);
        let artifact = CachedMonoArtifact {
            program: specialize::mono::Program::default(),
            file_count: 1,
            errors: vec!["specialize warning".to_string()],
        };

        cache.write_mono_artifact(key, &artifact).unwrap();
        let restored = cache.read_mono_artifact(key).unwrap().unwrap();

        assert_eq!(restored, artifact);
        assert!(cache.mono_artifact_path(key).is_file());
        assert_eq!(cache.mono_artifact_path(key).extension().unwrap(), "yumo");

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
                "pub infix (<+>) 50 50 = \\x -> \\y -> x\npub act signal 'a 'b:\n  pub ping: unit -> never\n\npub struct Box { value: int }\n\npub role Display 'a:\n  pub x.display: self\n\npub x = 1\nmy hidden = 1\n",
            ),
        ];
        let loaded = sources::load(collected_to_source_files(files.clone()));
        let key = source_cache_key(&files);
        let artifact = compiled_unit_artifact_from_loaded_files(&files, &loaded).unwrap();

        cache.write_compiled_unit_artifact(key, &artifact).unwrap();
        let restored = cache.read_compiled_unit_artifact(key).unwrap().unwrap();

        assert_eq!(restored.manifest, artifact.manifest);
        assert_ne!(restored.manifest.lowering_hash, 0);
        assert_ne!(restored.manifest.runtime_hash, 0);
        assert_ne!(restored.manifest.external_runtime_hash, 0);
        assert_eq!(restored.syntax, artifact.syntax);
        assert_eq!(restored.namespace, artifact.namespace);
        assert_eq!(restored.lowering, artifact.lowering);
        assert_eq!(restored.external_runtime, artifact.external_runtime);
        assert_eq!(restored.external_runtime.imported_def_count, 0);
        assert_eq!(restored.errors, artifact.errors);
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
        assert!(
            restored
                .lowering
                .act_type_vars
                .iter()
                .any(|entry| entry.type_path == vec!["ops", "signal"]
                    && entry.vars == vec!["a", "b"])
        );
        assert!(
            restored
                .lowering
                .act_templates
                .iter()
                .any(|entry| entry.type_path == vec!["ops", "signal"]
                    && entry.source.contains("pub ping"))
        );
        assert!(
            restored
                .lowering
                .constructor_payloads
                .iter()
                .any(|entry| entry.value_path == vec!["ops", "Box"]
                    && entry.owner_type_path == vec!["ops", "Box"]
                    && entry.owner_type_vars.is_empty()
                    && matches!(entry.payload, infer::CompiledConstructorPayload::Record(_)))
        );
        assert!(
            restored
                .lowering
                .act_operations
                .iter()
                .any(|entry| entry.type_path == vec!["ops", "signal"]
                    && entry.value_symbol.is_some()
                    && entry.value_path.is_some()
                    && entry.name == "ping"
                    && entry.signature.is_some())
        );
        assert!(
            restored
                .lowering
                .role_shapes
                .iter()
                .any(|entry| entry.type_path == vec!["ops", "Display"]
                    && entry.inputs == vec!["a"]
                    && entry.associated.is_empty())
        );
        assert!(
            restored
                .lowering
                .type_field_methods
                .iter()
                .any(|entry| entry.owner_type_path == vec!["ops", "Box"] && entry.name == "value")
        );
        assert!(
            restored
                .lowering
                .role_methods
                .iter()
                .any(|entry| entry.type_path == vec!["ops", "Display"]
                    && entry.source_def.0 > 0
                    && entry.value_symbol.is_some()
                    && entry.value_path.is_some()
                    && entry.name == "display"
                    && entry.receiver.as_deref() == Some("x")
                    && entry.signature.is_some())
        );
        let x_symbol = ops_module
            .values
            .iter()
            .find(|value| value.name == "x")
            .unwrap()
            .symbol;
        assert!(
            restored
                .typed
                .values
                .iter()
                .any(|value| value.symbol == x_symbol)
        );
        assert!(
            restored
                .runtime
                .values
                .iter()
                .any(|value| value.symbol == x_symbol)
        );
        let hidden_symbol = ops_module
            .values
            .iter()
            .find(|value| value.name == "hidden")
            .unwrap()
            .symbol;
        assert!(
            restored
                .runtime
                .values
                .iter()
                .any(|value| value.symbol == hidden_symbol)
        );
        assert!(
            restored
                .runtime
                .modules
                .iter()
                .any(|module| module.module_path == ops_path)
        );
        assert_eq!(restored.typed.values.len(), artifact.typed.values.len());
        assert_eq!(
            restored.runtime.arena.defs.len(),
            artifact.runtime.arena.defs.len()
        );
        assert_eq!(restored.runtime.labels, artifact.runtime.labels);
        assert!(cache.compiled_unit_artifact_path(key).is_file());
        assert_eq!(
            cache.compiled_unit_artifact_path(key).extension().unwrap(),
            "yucu"
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

    #[test]
    fn compiled_unit_cache_rejects_mismatched_manifest() {
        let root = temp_root("compiled-unit-manifest-mismatch");
        let cache = ArtifactCache::new(&root);
        let files = vec![source("main.yu", &[], "pub x = 1\n")];
        let loaded = sources::load(collected_to_source_files(files.clone()));
        let key = source_cache_key(&files);
        let artifact = compiled_unit_artifact_from_loaded_files(&files, &loaded).unwrap();

        let mut wrong_source_hash = artifact.clone();
        wrong_source_hash.manifest.source_hash ^= 1;
        cache
            .write_compiled_unit_artifact(key, &wrong_source_hash)
            .unwrap();
        assert!(cache.read_compiled_unit_artifact(key).unwrap().is_none());

        let mut wrong_runtime_hash = artifact.clone();
        wrong_runtime_hash.manifest.runtime_hash ^= 1;
        cache
            .write_compiled_unit_artifact(key, &wrong_runtime_hash)
            .unwrap();
        assert!(cache.read_compiled_unit_artifact(key).unwrap().is_none());

        let mut wrong_external_runtime_hash = artifact.clone();
        wrong_external_runtime_hash.manifest.external_runtime_hash ^= 1;
        cache
            .write_compiled_unit_artifact(key, &wrong_external_runtime_hash)
            .unwrap();
        assert!(cache.read_compiled_unit_artifact(key).unwrap().is_none());

        cache.write_compiled_unit_artifact(key, &artifact).unwrap();
        assert!(cache.read_compiled_unit_artifact(key).unwrap().is_some());

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn compiled_unit_cache_accepts_explicit_source_unit_key() {
        let root = temp_root("compiled-unit-source-unit-key");
        let cache = ArtifactCache::new(&root);
        let files = vec![source("main.yu", &[], "pub x = 1\n")];
        let units = crate::source::source_compilation_units(&files);
        let keys = source_compilation_unit_cache_keys(&files, &units);
        let unit_key = keys[units.unit_for_file(0).unwrap()];
        let loaded = sources::load(collected_to_source_files(files.clone()));

        let artifact =
            compiled_unit_artifact_from_loaded_files_with_key(&files, &loaded, unit_key).unwrap();
        cache
            .write_compiled_unit_artifact(unit_key, &artifact)
            .unwrap();
        assert!(
            cache
                .read_compiled_unit_artifact(unit_key)
                .unwrap()
                .is_some()
        );

        let bundle_key_artifact =
            compiled_unit_artifact_from_loaded_files(&files, &loaded).unwrap();
        cache
            .write_compiled_unit_artifact(unit_key, &bundle_key_artifact)
            .unwrap();
        assert!(
            cache
                .read_compiled_unit_artifact(unit_key)
                .unwrap()
                .is_none()
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn source_unit_compiled_artifact_reads_select_dependency_closed_units() {
        let root = temp_root("source-unit-compiled-artifacts");
        let cache = ArtifactCache::new(&root);
        let files = module_chain_sources("mod a;\nx\n", "mod b;\npub x = b::y\n", "pub y = 7\n");
        let units = crate::source::source_compilation_units(&files);
        let keys = source_compilation_unit_cache_keys(&files, &units);

        cache
            .write_compiled_unit_artifact(keys[0], &empty_compiled_unit_artifact(keys[0]))
            .unwrap();
        cache
            .write_compiled_unit_artifact(keys[2], &empty_compiled_unit_artifact(keys[2]))
            .unwrap();

        let cached = cache
            .read_source_unit_compiled_artifacts(&files, &units)
            .unwrap();

        assert_eq!(cached.keys, keys);
        assert!(cached.artifacts[0].is_some());
        assert!(cached.artifacts[1].is_none());
        assert!(cached.artifacts[2].is_some());
        assert_eq!(cached.selection.cached_units, vec![0]);
        assert_eq!(cached.selection.cached_files, vec![2]);
        assert_eq!(cached.selection.source_files, vec![0, 1]);

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn compiled_unit_cache_writes_non_root_standalone_source_unit() {
        let root = temp_root("compiled-unit-non-root-source-unit");
        let cache = ArtifactCache::new(&root);
        let files =
            module_chain_sources("pub mod a;\nx\n", "mod b;\npub x = b::y\n", "pub y = 7\n");
        let units = crate::source::source_compilation_units(&files);
        let keys = source_compilation_unit_cache_keys(&files, &units);
        let b_unit = units.unit_for_file(2).unwrap();
        let artifact =
            compiled_unit_artifact_from_standalone_source_unit(&files, &units, b_unit).unwrap();

        assert_eq!(artifact.manifest.files.len(), 1);
        assert_eq!(artifact.manifest.files[0].module_path, vec!["a", "b"]);
        assert_eq!(artifact.syntax.files.len(), 3);
        assert!(
            artifact
                .namespace
                .modules
                .iter()
                .any(|module| module.path == vec!["a".to_string(), "b".to_string()])
        );
        cache
            .write_compiled_unit_artifact(keys[b_unit], &artifact)
            .unwrap();
        let restored = cache
            .read_compiled_unit_artifact(keys[b_unit])
            .unwrap()
            .unwrap();

        assert_eq!(restored.manifest, artifact.manifest);
        assert_eq!(restored.syntax, artifact.syntax);
        assert_eq!(restored.namespace, artifact.namespace);
        assert_eq!(restored.lowering, artifact.lowering);
        assert_eq!(restored.typed.values.len(), artifact.typed.values.len());
        assert_eq!(
            restored.runtime.arena.defs.len(),
            artifact.runtime.arena.defs.len()
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn compiled_unit_cache_writes_dependent_source_unit_closure() {
        let files =
            module_chain_sources("pub mod a;\nx\n", "mod b;\npub x = b::y\n", "pub y = 7\n");
        let units = crate::source::source_compilation_units(&files);
        let a_unit = units.unit_for_file(1).unwrap();
        let artifact =
            compiled_unit_artifact_from_source_unit_closure(&files, &units, a_unit).unwrap();

        assert!(artifact.errors.is_empty(), "{:?}", artifact.errors);
        assert_eq!(artifact.manifest.files.len(), 2);
        assert_eq!(artifact.manifest.files[0].module_path, vec!["a"]);
        assert_eq!(artifact.manifest.files[1].module_path, vec!["a", "b"]);

        let namespace = infer::CompiledNamespaceIndex::new(&artifact.namespace);
        let x = namespace
            .exported_value_symbol(&["a".to_string()], "x")
            .unwrap();
        let y = namespace
            .exported_value_symbol(&["a".to_string(), "b".to_string()], "y")
            .unwrap();
        assert!(
            artifact
                .runtime
                .values
                .iter()
                .any(|value| value.symbol == x)
        );
        assert!(
            artifact
                .runtime
                .values
                .iter()
                .any(|value| value.symbol == y)
        );
    }

    #[test]
    fn compiled_unit_artifact_records_prefix_external_runtime_refs() {
        let prefix_files = vec![
            source("prefix.yu", &[], "mod deps;\npub use deps::*\n"),
            source("deps.yu", &["deps"], "pub id x = x\n"),
        ];
        let prefix_loaded = sources::load(collected_to_source_files(prefix_files));
        let prefix_lowering = infer::lowering::lower_loaded_files(&prefix_loaded).unwrap();
        let prefix_namespace =
            infer::CompiledNamespaceSurface::from_module_table(&prefix_lowering.modules);
        let prefix_lowering_surface = infer::CompiledLoweringSurface::from_module_table(
            &prefix_lowering.modules,
            &prefix_namespace,
        );
        let prefix_runtime = infer::CompiledRuntimeSurface::from_lowering_with_namespace(
            &prefix_lowering,
            &prefix_namespace,
        );
        let prefix = infer::lowering::BodyLoweringPrefix::from_compiled_unit_surfaces(
            &prefix_namespace,
            &prefix_lowering_surface,
            &prefix_runtime,
        )
        .unwrap();
        let suffix_files = vec![source("main.yu", &[], "pub y = id 1\n")];
        let suffix_loaded = sources::load(collected_to_source_files(suffix_files.clone()));
        let suffix_root = suffix_loaded.into_iter().next().unwrap();
        let lowered =
            infer::lowering::lower_root_loaded_file_with_prefix(&prefix, &suffix_root).unwrap();
        let syntax =
            sources::CompiledSyntaxSurface::from_loaded_files(std::slice::from_ref(&suffix_root));
        let key = source_cache_key(&suffix_files);

        let artifact = compiled_unit_artifact_from_lowering_with_syntax_and_key(
            &suffix_files,
            syntax,
            &lowered,
            lowered
                .errors
                .iter()
                .map(|error| format!("{error:?}"))
                .collect(),
            key,
        );

        assert!(artifact.external_runtime.imported_def_count > 0);
        assert_eq!(
            artifact.external_runtime.imported_def_count,
            artifact.external_runtime.defs.len()
        );
        assert!(
            artifact
                .external_runtime
                .modules
                .iter()
                .any(|module| module.module_path == vec!["deps"])
        );
        assert!(
            artifact
                .external_runtime
                .values
                .iter()
                .any(|value| value.value_path == vec!["deps", "id"]
                    && artifact.runtime.arena.defs.get(value.def).is_some())
        );
        assert!(
            !artifact
                .external_runtime
                .values
                .iter()
                .any(|value| value.value_path == vec!["y"])
        );
        assert_eq!(
            artifact.manifest.external_runtime_hash,
            compiled_external_runtime_hash(&artifact.external_runtime)
        );
    }

    #[test]
    fn compiled_unit_external_runtime_def_pairs_resolve_prefix_paths() {
        let prefix_files = vec![
            source("prefix.yu", &[], "mod deps;\npub use deps::*\n"),
            source("deps.yu", &["deps"], "pub id x = x\n"),
        ];
        let prefix = compiled_unit_prefix_from_sources(prefix_files);
        let (artifact, lowered) = dependent_artifact_with_prefix(&prefix, "pub y = id 1\n");
        assert_eq!(lowered.errors, Vec::new());
        let source_id = artifact
            .external_runtime
            .values
            .iter()
            .find(|value| value.value_path == vec!["deps".to_string(), "id".to_string()])
            .expect("suffix artifact should record deps::id as an external value")
            .def;
        let target_id = prefix
            .runtime()
            .value_defs()
            .find(|value| value.value_path == vec!["deps".to_string(), "id".to_string()])
            .expect("prefix runtime should retain deps::id by path")
            .def;

        let external_defs =
            compiled_unit_external_runtime_def_pairs(&artifact, prefix.runtime()).unwrap();
        let required_external_defs = artifact
            .runtime
            .required_external_defs_for_reachable_import(
                artifact.external_runtime.defs.iter().copied(),
            );
        assert!(required_external_defs.contains(&source_id));
        assert!(
            required_external_defs
                .iter()
                .all(|required| external_defs.iter().any(|(source, _)| source == required))
        );
        assert!(
            artifact
                .external_runtime
                .defs
                .iter()
                .any(|def| !required_external_defs.contains(def))
        );
        let complete_external_defs =
            compiled_unit_complete_external_runtime_def_pairs(&artifact, prefix.runtime()).unwrap();
        let extended = prefix
            .extend_with_compiled_unit_surfaces_and_external_defs(
                &artifact.namespace,
                &artifact.lowering,
                &artifact.runtime,
                complete_external_defs.clone(),
            )
            .expect("suffix artifact should extend the existing prefix");
        let rebuilt_id = extended
            .runtime()
            .value_defs()
            .find(|value| value.value_path == vec!["deps".to_string(), "id".to_string()])
            .expect("extended prefix should keep deps::id visible")
            .def;
        let y = extended
            .runtime()
            .value_defs()
            .find(|value| value.value_path == vec!["y".to_string()])
            .expect("extended prefix should include the suffix value")
            .def;

        assert!(external_defs.contains(&(source_id, target_id)));
        assert_eq!(complete_external_defs, external_defs);
        assert_eq!(rebuilt_id, target_id);
        assert_ne!(y, target_id);
        assert!(!prefix.runtime().contains_def(y));

        let mut value_only_artifact = artifact.clone();
        value_only_artifact.external_runtime.modules.clear();
        let error =
            compiled_unit_external_runtime_def_pairs(&value_only_artifact, &Default::default())
                .unwrap_err();
        assert!(matches!(
            error,
            CompiledUnitExternalRuntimeDefMapError::MissingValuePath { value_path }
                if value_path == vec!["deps".to_string(), "id".to_string()]
        ));

        let mut incomplete_artifact = artifact.clone();
        incomplete_artifact.external_runtime.values.clear();
        let error = compiled_unit_complete_external_runtime_def_pairs(
            &incomplete_artifact,
            prefix.runtime(),
        )
        .unwrap_err();
        assert!(matches!(
            error,
            CompiledUnitExternalRuntimeDefMapError::UnkeyedExternalDefs { defs }
                if defs == vec![source_id]
        ));
    }

    #[test]
    fn compiled_unit_reachable_external_refs_cover_dependency_metadata() {
        let prefix = compiled_unit_prefix_from_sources(vec![
            source("prefix.yu", &[], "mod deps;\npub use deps::*\n"),
            source(
                "deps.yu",
                &["deps"],
                concat!(
                    "pub act signal:\n",
                    "  pub ping: () -> int\n",
                    "pub role Display 'a:\n",
                    "  pub x.display: int\n",
                    "pub id x = x\n",
                ),
            ),
        ]);
        let (artifact, lowered) = dependent_artifact_with_prefix(
            &prefix,
            concat!(
                "pub handled = catch signal::ping():\n",
                "    signal::ping(), k -> k 1\n",
                "    v -> v\n",
                "impl int: Display:\n",
                "  pub x.display = id x\n",
                "id 2\n",
            ),
        );

        assert_eq!(lowered.errors, Vec::new());
        assert!(!artifact.runtime.arena.root_exprs.is_empty());
        let external_defs =
            compiled_unit_complete_external_runtime_def_pairs(&artifact, prefix.runtime()).unwrap();
        let required = compiled_unit_required_external_defs_for_import(&artifact);
        assert!(required.len() >= 3);
        assert!(
            required
                .iter()
                .all(|required| external_defs.iter().any(|(source, _)| source == required))
        );

        let extended = prefix
            .extend_with_compiled_unit_surfaces_and_external_defs(
                &artifact.namespace,
                &artifact.lowering,
                &artifact.runtime,
                external_defs,
            )
            .expect("metadata-heavy suffix artifact should extend the prefix");
        for name in ["handled"] {
            assert!(
                extended
                    .runtime()
                    .value_defs()
                    .any(|value| value.value_path == vec![name.to_string()]),
                "extended prefix should include suffix value {name}"
            );
        }
    }

    #[test]
    fn compiled_unit_reachable_external_refs_key_effect_operations() {
        let prefix = compiled_unit_prefix_from_sources(vec![
            source("prefix.yu", &[], "mod deps;\npub use deps::*\n"),
            source(
                "deps.yu",
                &["deps"],
                "pub act signal:\n  pub ping: () -> int\n",
            ),
        ]);
        let (artifact, lowered) = dependent_artifact_with_prefix(
            &prefix,
            concat!(
                "our handle(action: [signal] _) = catch action:\n",
                "  signal::ping(), k -> k 5\n",
                "  v -> v\n",
                "pub handled = handle: signal::ping()\n",
            ),
        );

        assert_eq!(lowered.errors, Vec::new());
        let op_def = artifact
            .external_runtime
            .values
            .iter()
            .find(|value| value.value_path == vec!["deps", "signal", "ping"])
            .map(|value| value.def)
            .expect("effect operation should be externally keyed by value path");
        assert!(
            artifact
                .runtime
                .arena
                .effect_operations
                .contains_key(&op_def)
        );
        let external_defs =
            compiled_unit_complete_external_runtime_def_pairs(&artifact, prefix.runtime()).unwrap();
        assert!(external_defs.iter().any(|(source, _)| *source == op_def));
        let extended = prefix
            .extend_with_compiled_unit_surfaces_and_external_defs(
                &artifact.namespace,
                &artifact.lowering,
                &artifact.runtime,
                external_defs,
            )
            .expect("effect-operation suffix artifact should extend the prefix");
        assert!(
            extended
                .runtime()
                .value_defs()
                .any(|value| value.value_path == vec!["handled".to_string()])
        );
    }

    #[test]
    fn compiled_unit_reachable_external_refs_key_constructors() {
        let prefix = compiled_unit_prefix_from_sources(vec![
            source("prefix.yu", &[], "mod deps;\npub use deps::*\n"),
            source("deps.yu", &["deps"], "pub struct Box { value: int }\n"),
        ]);
        let (artifact, lowered) =
            dependent_artifact_with_prefix(&prefix, "pub made = Box { value: 1 }\n");

        assert_eq!(lowered.errors, Vec::new());
        let constructor_def = artifact
            .external_runtime
            .values
            .iter()
            .find(|value| value.value_path == vec!["deps", "Box"])
            .map(|value| value.def)
            .expect("constructor should be externally keyed by value path");
        assert!(
            artifact
                .runtime
                .arena
                .constructors
                .contains_key(&constructor_def)
        );
        let external_defs =
            compiled_unit_complete_external_runtime_def_pairs(&artifact, prefix.runtime()).unwrap();
        assert!(
            external_defs
                .iter()
                .any(|(source, _)| *source == constructor_def)
        );
        let extended = prefix
            .extend_with_compiled_unit_surfaces_and_external_defs(
                &artifact.namespace,
                &artifact.lowering,
                &artifact.runtime,
                external_defs,
            )
            .expect("constructor suffix artifact should extend the prefix");
        assert!(
            extended
                .runtime()
                .value_defs()
                .any(|value| value.value_path == vec!["made".to_string()])
        );
    }

    #[test]
    fn compiled_unit_reachable_external_refs_reuse_arg_effect_contracts() {
        let prefix = compiled_unit_prefix_from_sources(vec![
            source("prefix.yu", &[], "mod deps;\npub use deps::*\n"),
            source(
                "deps.yu",
                &["deps"],
                concat!(
                    "pub act signal:\n",
                    "  pub ping: () -> int\n",
                    "pub use_it(f: () -> [signal] int) = f ()\n",
                ),
            ),
        ]);
        let (artifact, lowered) = dependent_artifact_with_prefix(
            &prefix,
            concat!(
                "our handle(action: [signal] _) = catch action:\n",
                "  signal::ping(), k -> k 5\n",
                "  v -> v\n",
                "pub handled = handle: use_it \\() -> signal::ping()\n",
            ),
        );

        assert_eq!(lowered.errors, Vec::new());
        assert!(
            artifact
                .runtime
                .arena
                .arg_effect_contracts
                .keys()
                .any(|def| artifact.external_runtime.defs.contains(def)),
            "prefix callback contract metadata should stay attached to an imported prefix def"
        );
        let external_defs =
            compiled_unit_complete_external_runtime_def_pairs(&artifact, prefix.runtime()).unwrap();
        let extended = prefix
            .extend_with_compiled_unit_surfaces_and_external_defs(
                &artifact.namespace,
                &artifact.lowering,
                &artifact.runtime,
                external_defs,
            )
            .expect("arg-effect-contract suffix artifact should extend the prefix");
        assert!(
            extended
                .runtime()
                .value_defs()
                .any(|value| value.value_path == vec!["handled".to_string()])
        );
    }

    #[test]
    fn compiled_unit_reachable_external_refs_key_type_field_methods() {
        let prefix = compiled_unit_prefix_from_sources(vec![
            source("prefix.yu", &[], "mod deps;\npub use deps::*\n"),
            source("deps.yu", &["deps"], "pub struct Box { value: int }\n"),
        ]);
        let (artifact, lowered) =
            dependent_artifact_with_prefix(&prefix, "pub made = Box { value: 1 }\n");

        assert_eq!(lowered.errors, Vec::new());
        let field_defs = artifact
            .lowering
            .type_field_methods
            .iter()
            .filter(|entry| entry.owner_type_path == vec!["deps", "Box"] && entry.name == "value")
            .map(|entry| entry.source_def)
            .collect::<Vec<_>>();
        assert!(!field_defs.is_empty());
        assert!(!artifact.external_runtime.type_field_methods.is_empty());
        let external_defs =
            compiled_unit_complete_external_runtime_def_pairs(&artifact, prefix.runtime()).unwrap();
        assert!(
            field_defs
                .iter()
                .all(|field| external_defs.iter().any(|(source, _)| source == field))
        );
        let extended = prefix
            .extend_with_compiled_unit_surfaces_and_external_defs(
                &artifact.namespace,
                &artifact.lowering,
                &artifact.runtime,
                external_defs,
            )
            .expect("type-field suffix artifact should extend the prefix");
        assert!(
            extended
                .runtime()
                .value_defs()
                .any(|value| value.value_path == vec!["made".to_string()])
        );
    }

    #[test]
    fn compiled_unit_reachable_external_refs_key_casts() {
        let prefix = compiled_unit_prefix_from_sources(vec![
            source("prefix.yu", &[], "mod deps;\npub use deps::*\n"),
            source(
                "deps.yu",
                &["deps"],
                concat!(
                    "pub struct Box { value: int }\n",
                    "pub cast(x: int): Box = Box { value: x }\n",
                ),
            ),
        ]);
        let (artifact, lowered) = dependent_artifact_with_prefix(
            &prefix,
            "pub wants_box(x: Box) = x\npub casted = wants_box 1\n",
        );

        assert_eq!(lowered.errors, Vec::new());
        assert!(!artifact.external_runtime.casts.is_empty());
        let external_defs =
            compiled_unit_complete_external_runtime_def_pairs(&artifact, prefix.runtime()).unwrap();
        let cast_defs = artifact
            .external_runtime
            .casts
            .iter()
            .map(|cast| cast.def)
            .collect::<Vec<_>>();
        assert!(
            cast_defs
                .iter()
                .all(|cast| external_defs.iter().any(|(source, _)| source == cast))
        );
        let extended = prefix
            .extend_with_compiled_unit_surfaces_and_external_defs(
                &artifact.namespace,
                &artifact.lowering,
                &artifact.runtime,
                external_defs,
            )
            .expect("cast suffix artifact should extend the prefix");
        for name in ["wants_box", "casted"] {
            assert!(
                extended
                    .runtime()
                    .value_defs()
                    .any(|value| value.value_path == vec![name.to_string()]),
                "extended prefix should include suffix value {name}"
            );
        }
    }

    #[test]
    fn compiled_unit_reachable_external_refs_reuse_prefix_role_impls() {
        let prefix = compiled_unit_prefix_from_sources(vec![
            source("prefix.yu", &[], "mod deps;\npub use deps::*\n"),
            source(
                "deps.yu",
                &["deps"],
                concat!(
                    "pub role Display 'a:\n",
                    "  pub x.display: int\n",
                    "impl int: Display:\n",
                    "  pub x.display = x\n",
                ),
            ),
        ]);
        let (artifact, lowered) =
            dependent_artifact_with_prefix(&prefix, "pub shown = 1.display\n");

        assert_eq!(lowered.errors, Vec::new());
        let external_defs =
            compiled_unit_complete_external_runtime_def_pairs(&artifact, prefix.runtime()).unwrap();
        let extended = prefix
            .extend_with_compiled_unit_surfaces_and_external_defs(
                &artifact.namespace,
                &artifact.lowering,
                &artifact.runtime,
                external_defs,
            )
            .expect("role-impl suffix artifact should extend the prefix");
        assert!(
            extended
                .runtime()
                .value_defs()
                .any(|value| value.value_path == vec!["shown".to_string()])
        );
    }

    #[test]
    fn compiled_unit_artifact_merge_combines_independent_leaf_units() {
        let files = vec![
            source("main.yu", &[], "mod left;\nmod right;\n"),
            source(
                "left.yu",
                &["left"],
                "pub act signal 'a:\n  pub ping: () -> 'a\n",
            ),
            source("right.yu", &["right"], "pub struct Box { value: int }\n"),
        ];
        let units = crate::source::source_compilation_units(&files);
        let left_unit = units.unit_for_file(1).unwrap();
        let right_unit = units.unit_for_file(2).unwrap();
        let left =
            compiled_unit_artifact_from_standalone_source_unit(&files, &units, left_unit).unwrap();
        let right =
            compiled_unit_artifact_from_standalone_source_unit(&files, &units, right_unit).unwrap();

        let key = merged_compiled_unit_artifact_key(&[left.clone(), right.clone()]).unwrap();
        let merged = merge_compiled_unit_artifacts(vec![left, right]).unwrap();
        let namespace = infer::CompiledNamespaceIndex::new(&merged.namespace);
        let signal = namespace
            .exported_type_symbol(&["left".to_string()], "signal")
            .unwrap();
        let box_ctor = namespace
            .exported_value_symbol(&["right".to_string()], "Box")
            .unwrap();

        assert_eq!(merged.manifest.files.len(), 2);
        assert_eq!(merged.manifest.files[0].path, "left.yu");
        assert_eq!(merged.manifest.files[1].path, "right.yu");
        assert_eq!(merged.cache_key(), key);
        assert!(
            merged
                .lowering
                .act_type_vars
                .iter()
                .any(|entry| entry.type_symbol == signal)
        );
        assert!(
            merged
                .lowering
                .constructor_payloads
                .iter()
                .any(|entry| entry.value_symbol == box_ctor)
        );
        assert!(
            merged
                .runtime
                .values
                .iter()
                .any(|value| value.symbol == box_ctor)
        );
        assert!(
            merged
                .typed
                .values
                .iter()
                .any(|value| value.symbol == box_ctor)
        );
        assert_eq!(
            merged.manifest.syntax_hash,
            compiled_syntax_hash(&merged.syntax)
        );
        assert_eq!(
            merged.manifest.namespace_hash,
            compiled_namespace_hash(&merged.namespace)
        );
        assert_eq!(
            merged.manifest.lowering_hash,
            compiled_lowering_hash(&merged.lowering)
        );
        assert_eq!(
            merged.manifest.typed_hash,
            compiled_typed_hash(&merged.typed)
        );
        assert_eq!(
            merged.manifest.runtime_hash,
            compiled_runtime_hash(&merged.runtime)
        );
        assert_eq!(
            merged.manifest.external_runtime_hash,
            compiled_external_runtime_hash(&merged.external_runtime)
        );
    }

    #[test]
    fn compiled_unit_artifact_merge_coalesces_shared_parent_modules() {
        let files = vec![
            source("main.yu", &[], "mod a;\n"),
            source("a.yu", &["a"], "mod b;\nmod c;\n"),
            source("a/b.yu", &["a", "b"], "pub x = 1\n"),
            source("a/c.yu", &["a", "c"], "pub y = 2\n"),
        ];
        let units = crate::source::source_compilation_units(&files);
        let b_unit = units.unit_for_file(2).unwrap();
        let c_unit = units.unit_for_file(3).unwrap();
        let b = compiled_unit_artifact_from_standalone_source_unit(&files, &units, b_unit).unwrap();
        let c = compiled_unit_artifact_from_standalone_source_unit(&files, &units, c_unit).unwrap();

        let merged = merge_compiled_unit_artifacts(vec![b, c]).unwrap();
        let namespace = infer::CompiledNamespaceIndex::new(&merged.namespace);
        let a_module = namespace.exported_module_id(&[], "a").unwrap();
        let b_module = namespace
            .exported_module_id(&["a".to_string()], "b")
            .unwrap();
        let c_module = namespace
            .exported_module_id(&["a".to_string()], "c")
            .unwrap();
        let a_def = merged
            .runtime
            .modules
            .iter()
            .find(|module| module.module == a_module)
            .unwrap()
            .def;
        let b_def = merged
            .runtime
            .modules
            .iter()
            .find(|module| module.module == b_module)
            .unwrap()
            .def;
        let c_def = merged
            .runtime
            .modules
            .iter()
            .find(|module| module.module == c_module)
            .unwrap()
            .def;

        let Some(poly::expr::Def::Mod { children, .. }) = merged.runtime.arena.defs.get(a_def)
        else {
            panic!("merged parent module should remain a module def");
        };
        assert!(children.contains(&b_def));
        assert!(children.contains(&c_def));
        assert!(merged.runtime.values.iter().any(|value| {
            value.symbol
                == namespace
                    .exported_value_symbol(&["a".to_string(), "b".to_string()], "x")
                    .unwrap()
        }));
        assert!(merged.runtime.values.iter().any(|value| {
            value.symbol
                == namespace
                    .exported_value_symbol(&["a".to_string(), "c".to_string()], "y")
                    .unwrap()
        }));
    }

    #[test]
    fn compiled_unit_artifact_merge_rejects_conflicting_manifest_file() {
        let files = vec![
            source("main.yu", &[], "mod unit;\n"),
            source("unit.yu", &["unit"], "pub x = 1\n"),
        ];
        let units = crate::source::source_compilation_units(&files);
        let unit = units.unit_for_file(1).unwrap();
        let artifact =
            compiled_unit_artifact_from_standalone_source_unit(&files, &units, unit).unwrap();
        let mut conflicting = artifact.clone();
        conflicting.manifest.files[0].source_hash ^= 1;
        let error = match merge_compiled_unit_artifacts(vec![artifact, conflicting]) {
            Ok(_) => panic!("merge should reject conflicting files with the same path"),
            Err(error) => error,
        };

        assert!(matches!(
            error,
            CompiledUnitMergeError::ConflictingFile { path } if path == "unit.yu"
        ));
    }

    fn source(path: &str, module: &[&str], text: &str) -> CollectedSource {
        CollectedSource::new(
            PathBuf::from(path),
            path_from_segments(module),
            text.to_string(),
        )
    }

    fn slash_import_request() -> sources::UseImport {
        sources::UseImport::Alias {
            name: Name("a".into()),
            path: path_from_segments(&["ui", "widget", "a"]),
            route: sources::UsePathRoute::SlashQualified { prefix_segments: 2 },
            version: None,
            anchor: Some(sources::UseAnchor {
                path: path_from_segments(&["program", "ui"]),
                route: sources::UsePathRoute::Relative,
            }),
        }
    }

    fn realm_id(identity: &str, version: Option<&str>) -> sources::ResolvedRealmId {
        sources::ResolvedRealmId {
            identity: sources::RealmIdentity(identity.to_string()),
            version: version.map(|version| sources::RealmVersion(version.to_string())),
        }
    }

    fn path(segments: &[&str]) -> Path {
        path_from_segments(segments)
    }

    fn path_from_segments(segments: &[&str]) -> Path {
        Path {
            segments: segments
                .iter()
                .map(|segment| Name((*segment).to_string()))
                .collect(),
        }
    }

    fn module_chain_sources(
        root_source: &str,
        a_source: &str,
        b_source: &str,
    ) -> Vec<CollectedSource> {
        vec![
            source("main.yu", &[], root_source),
            source("a.yu", &["a"], a_source),
            source("a/b.yu", &["a", "b"], b_source),
        ]
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

    fn compiled_unit_prefix_from_sources(
        files: Vec<CollectedSource>,
    ) -> infer::lowering::BodyLoweringPrefix {
        let loaded = sources::load(collected_to_source_files(files));
        let lowering = infer::lowering::lower_loaded_files(&loaded).unwrap();
        let namespace = infer::CompiledNamespaceSurface::from_module_table(&lowering.modules);
        let lowering_surface =
            infer::CompiledLoweringSurface::from_module_table(&lowering.modules, &namespace);
        let runtime =
            infer::CompiledRuntimeSurface::from_lowering_with_namespace(&lowering, &namespace);
        infer::lowering::BodyLoweringPrefix::from_compiled_unit_surfaces(
            &namespace,
            &lowering_surface,
            &runtime,
        )
        .unwrap()
    }

    fn dependent_artifact_with_prefix(
        prefix: &infer::lowering::BodyLoweringPrefix,
        text: &str,
    ) -> (CachedCompiledUnitArtifact, infer::lowering::BodyLowering) {
        let suffix_files = vec![source("main.yu", &[], text)];
        let suffix_loaded = sources::load(collected_to_source_files(suffix_files.clone()));
        let suffix_root = suffix_loaded.into_iter().next().unwrap();
        let lowered =
            infer::lowering::lower_root_loaded_file_with_prefix(prefix, &suffix_root).unwrap();
        let syntax =
            sources::CompiledSyntaxSurface::from_loaded_files(std::slice::from_ref(&suffix_root));
        let key = source_cache_key(&suffix_files);
        let artifact = compiled_unit_artifact_from_lowering_with_syntax_and_key(
            &suffix_files,
            syntax,
            &lowered,
            lowered
                .errors
                .iter()
                .map(|error| format!("{error:?}"))
                .collect(),
            key,
        );
        (artifact, lowered)
    }

    fn empty_compiled_unit_artifact(key: SourceCacheKey) -> CachedCompiledUnitArtifact {
        let syntax = sources::CompiledSyntaxSurface::default();
        let namespace = infer::CompiledNamespaceSurface::default();
        let lowering = infer::CompiledLoweringSurface::default();
        let typed = infer::CompiledTypedSurface {
            types: infer::CompiledTypeArena {
                pos: Vec::new(),
                neg: Vec::new(),
                neu: Vec::new(),
            },
            values: Vec::new(),
        };
        let runtime = infer::CompiledRuntimeSurface {
            arena: poly::expr::Arena::new(),
            labels: poly::dump::DumpLabels::new(),
            modules: Vec::new(),
            values: Vec::new(),
        };
        let external_runtime = CompiledUnitExternalRuntimeRefs::default();
        let manifest = compiled_unit_manifest(
            &[],
            &syntax,
            &namespace,
            &lowering,
            &typed,
            &runtime,
            &external_runtime,
            key,
        );
        CachedCompiledUnitArtifact {
            manifest,
            syntax,
            namespace,
            lowering,
            typed,
            runtime,
            external_runtime,
            errors: Vec::new(),
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
