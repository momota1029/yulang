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
const COMPILED_UNIT_CACHE_FORMAT: u32 = 9;
// Bump when compiler/cache semantics change without a serialized envelope bump.
const CACHE_SCHEMA_VERSION: u32 = 1;
const SOURCE_CACHE_SALT: &[u8] = b"yulang/source-set-cache/v2";
const SOURCE_FILE_HASH_SALT: &[u8] = b"yulang/source-file/v1";
const COMPILED_SYNTAX_HASH_SALT: &[u8] = b"yulang/compiled-syntax-surface/v1";
const COMPILED_NAMESPACE_HASH_SALT: &[u8] = b"yulang/compiled-namespace-surface/v1";
const COMPILED_LOWERING_HASH_SALT: &[u8] = b"yulang/compiled-lowering-surface/v3";
const COMPILED_TYPED_HASH_SALT: &[u8] = b"yulang/compiled-typed-surface/v1";
const COMPILED_RUNTIME_HASH_SALT: &[u8] = b"yulang/compiled-runtime-surface/v2";
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
            lowering: envelope.lowering,
            typed: envelope.typed,
            runtime: envelope.runtime,
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
            lowering: &artifact.lowering,
            typed: &artifact.typed,
            runtime: &artifact.runtime,
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

#[derive(Clone)]
pub struct CachedCompiledUnitArtifact {
    pub manifest: CompiledUnitManifest,
    pub syntax: sources::CompiledSyntaxSurface,
    pub namespace: infer::CompiledNamespaceSurface,
    pub lowering: infer::CompiledLoweringSurface,
    pub typed: infer::CompiledTypedSurface,
    pub runtime: infer::CompiledRuntimeSurface,
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
    let lowering = infer::lowering::lower_loaded_files(loaded)?;
    let namespace = infer::CompiledNamespaceSurface::from_module_table(&lowering.modules);
    let lowering_surface =
        infer::CompiledLoweringSurface::from_module_table(&lowering.modules, &namespace);
    let typed = infer::CompiledTypedSurface::from_lowering(&lowering, &namespace);
    let runtime =
        infer::CompiledRuntimeSurface::from_lowering_with_namespace(&lowering, &namespace);
    let manifest = compiled_unit_manifest(
        files,
        &syntax,
        &namespace,
        &lowering_surface,
        &typed,
        &runtime,
    );
    Ok(CachedCompiledUnitArtifact {
        manifest,
        syntax,
        namespace,
        lowering: lowering_surface,
        typed,
        runtime,
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
    lowering: &infer::CompiledLoweringSurface,
    typed: &infer::CompiledTypedSurface,
    runtime: &infer::CompiledRuntimeSurface,
) -> CompiledUnitManifest {
    CompiledUnitManifest {
        cache_schema_version: CACHE_SCHEMA_VERSION,
        compiled_unit_format: COMPILED_UNIT_CACHE_FORMAT,
        source_hash: source_cache_key(files).hash,
        syntax_hash: compiled_syntax_hash(syntax),
        namespace_hash: compiled_namespace_hash(namespace),
        lowering_hash: compiled_lowering_hash(lowering),
        typed_hash: compiled_typed_hash(typed),
        runtime_hash: compiled_runtime_hash(runtime),
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

    hasher.usize(lowering.constructor_payloads.len());
    for entry in &lowering.constructor_payloads {
        hasher.u32(entry.value_symbol);
        hash_string_path(&mut hasher, &entry.value_path);
        hasher.u32(entry.owner_type_symbol);
        hash_string_path(&mut hasher, &entry.owner_type_path);
        hash_compiled_constructor_payload(&mut hasher, &entry.payload);
    }

    hasher.usize(lowering.act_operations.len());
    for entry in &lowering.act_operations {
        hasher.u32(entry.type_symbol);
        hash_string_path(&mut hasher, &entry.type_path);
        hash_optional_u32(&mut hasher, entry.value_symbol);
        hash_optional_string_path(&mut hasher, entry.value_path.as_deref());
        hasher.string(&entry.name);
        hash_optional_compiled_signature_type(&mut hasher, &entry.signature);
    }

    hasher.usize(lowering.role_methods.len());
    for entry in &lowering.role_methods {
        hasher.u32(entry.type_symbol);
        hash_string_path(&mut hasher, &entry.type_path);
        hash_optional_u32(&mut hasher, entry.value_symbol);
        hash_optional_string_path(&mut hasher, entry.value_path.as_deref());
        hasher.string(&entry.name);
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
    hasher.usize(runtime.values.len());
    for value in &runtime.values {
        hasher.u32(value.symbol);
        hash_def_id(&mut hasher, value.def);
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
    L = infer::CompiledLoweringSurface,
    T = infer::CompiledTypedSurface,
    R = infer::CompiledRuntimeSurface,
> {
    format: u32,
    manifest: M,
    syntax: S,
    namespace: N,
    lowering: L,
    typed: T,
    runtime: R,
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

impl<M, S, N, L, T, R> CacheEnvelope for CompiledUnitCacheEnvelope<M, S, N, L, T, R> {
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
        assert_eq!(restored.syntax, artifact.syntax);
        assert_eq!(restored.namespace, artifact.namespace);
        assert_eq!(restored.lowering, artifact.lowering);
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
                .constructor_payloads
                .iter()
                .any(|entry| entry.value_path == vec!["ops", "Box"]
                    && entry.owner_type_path == vec!["ops", "Box"]
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
                .role_methods
                .iter()
                .any(|entry| entry.type_path == vec!["ops", "Display"]
                    && entry.value_symbol.is_some()
                    && entry.value_path.is_some()
                    && entry.name == "display"
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
        assert_eq!(restored.typed.values.len(), artifact.typed.values.len());
        assert_eq!(
            restored.runtime.arena.defs.len(),
            artifact.runtime.arena.defs.len()
        );
        assert_eq!(restored.runtime.labels, artifact.runtime.labels);
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
