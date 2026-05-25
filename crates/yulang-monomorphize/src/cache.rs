use std::{
    collections::{HashMap, hash_map::DefaultHasher},
    fs,
    hash::{Hash, Hasher},
    io,
    path::{Path, PathBuf},
};

use serde::{Deserialize, Serialize};
use yulang_runtime_ir::{
    FinalizedBinding as Binding, FinalizedExpr as Expr, FinalizedExprKind as ExprKind,
    FinalizedType as RuntimeType,
};
use yulang_sources::{CompiledUnitManifest, YulangCachePaths};
use yulang_typed_ir as typed_ir;

pub const MONOMORPHIZE_INSTANCE_CACHE_FORMAT_VERSION: u32 = 2;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MonomorphizeInstanceArtifactCache {
    root: PathBuf,
}

impl MonomorphizeInstanceArtifactCache {
    pub fn new(root: impl Into<PathBuf>) -> Self {
        Self { root: root.into() }
    }

    pub fn from_paths(paths: &YulangCachePaths) -> Self {
        Self::new(paths.compiled_units.clone())
    }

    pub fn read_for_manifests(
        &self,
        manifests: &[CompiledUnitManifest],
    ) -> Result<MonomorphizeInstanceCacheSurface, MonomorphizeInstanceArtifactCacheError> {
        let key = MonomorphizeInstanceArtifactCacheKey::from_manifests(manifests)?;
        let path = self.artifact_path(&key);
        let bytes = fs::read(&path).map_err(|error| MonomorphizeInstanceArtifactCacheError::Io {
            path: path.clone(),
            error: io_error_string(error),
        })?;
        let surface =
            postcard::from_bytes::<MonomorphizeInstanceCacheSurface>(&bytes).map_err(|error| {
                MonomorphizeInstanceArtifactCacheError::Deserialize {
                    path: path.clone(),
                    error: error.to_string(),
                }
            })?;
        if surface.format_version != MONOMORPHIZE_INSTANCE_CACHE_FORMAT_VERSION {
            return Err(
                MonomorphizeInstanceArtifactCacheError::UnsupportedFinalizeFormat {
                    format_version: surface.format_version,
                },
            );
        }
        Ok(surface)
    }

    pub fn read_cache_for_manifests(
        &self,
        manifests: &[CompiledUnitManifest],
    ) -> MonomorphizeInstanceCache {
        self.read_for_manifests(manifests)
            .map(MonomorphizeInstanceCache::from_surface)
            .unwrap_or_default()
    }

    pub fn write_cache_for_manifests(
        &self,
        manifests: &[CompiledUnitManifest],
        cache: &MonomorphizeInstanceCache,
    ) -> Result<PathBuf, MonomorphizeInstanceArtifactCacheError> {
        self.write_for_manifests(manifests, &cache.to_surface())
    }

    pub fn write_for_manifests(
        &self,
        manifests: &[CompiledUnitManifest],
        surface: &MonomorphizeInstanceCacheSurface,
    ) -> Result<PathBuf, MonomorphizeInstanceArtifactCacheError> {
        let key = MonomorphizeInstanceArtifactCacheKey::from_manifests(manifests)?;
        let path = self.artifact_path(&key);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).map_err(|error| MonomorphizeInstanceArtifactCacheError::Io {
                path: parent.to_path_buf(),
                error: io_error_string(error),
            })?;
        }
        let bytes = postcard::to_allocvec(surface).map_err(|error| {
            MonomorphizeInstanceArtifactCacheError::Serialize {
                error: error.to_string(),
            }
        })?;
        fs::write(&path, bytes).map_err(|error| MonomorphizeInstanceArtifactCacheError::Io {
            path: path.clone(),
            error: io_error_string(error),
        })?;
        Ok(path)
    }

    fn artifact_path(&self, key: &MonomorphizeInstanceArtifactCacheKey) -> PathBuf {
        key.directory(&self.root).join(key.file_name())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MonomorphizeInstanceArtifactCacheKey {
    pub compiled_artifact_format_version: u32,
    pub parser_format_version: u32,
    pub finalize_format_version: u32,
    pub unit_count: usize,
    pub manifest_hash: u64,
}

impl MonomorphizeInstanceArtifactCacheKey {
    pub fn from_manifests(
        manifests: &[CompiledUnitManifest],
    ) -> Result<Self, MonomorphizeInstanceArtifactCacheError> {
        let Some(first) = manifests.first() else {
            return Err(MonomorphizeInstanceArtifactCacheError::EmptyManifestSet);
        };
        for manifest in manifests {
            if manifest.artifact_format_version != first.artifact_format_version
                || manifest.parser_format_version != first.parser_format_version
            {
                return Err(MonomorphizeInstanceArtifactCacheError::MixedCompiledFormats);
            }
        }
        Ok(Self {
            compiled_artifact_format_version: first.artifact_format_version,
            parser_format_version: first.parser_format_version,
            finalize_format_version: MONOMORPHIZE_INSTANCE_CACHE_FORMAT_VERSION,
            unit_count: manifests.len(),
            manifest_hash: hash_compiled_unit_manifests(manifests),
        })
    }

    fn directory(&self, root: &Path) -> PathBuf {
        root.join(format!("v{}", self.compiled_artifact_format_version))
            .join(format!("parser-v{}", self.parser_format_version))
            .join(format!(
                "runtime-finalize-v{}",
                self.finalize_format_version
            ))
    }

    fn file_name(&self) -> String {
        format!(
            "instances-{}-{:016x}.bin",
            self.unit_count, self.manifest_hash
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MonomorphizeInstanceArtifactCacheError {
    EmptyManifestSet,
    MixedCompiledFormats,
    UnsupportedFinalizeFormat { format_version: u32 },
    Io { path: PathBuf, error: String },
    Serialize { error: String },
    Deserialize { path: PathBuf, error: String },
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct MonomorphizeInstanceCache {
    entries: HashMap<MonomorphizeInstanceKey, CachedMonomorphizeInstance>,
    policy: MonomorphizeInstanceCachePolicy,
    profile: MonomorphizeInstanceCacheProfile,
}

impl MonomorphizeInstanceCache {
    pub fn new(policy: MonomorphizeInstanceCachePolicy) -> Self {
        Self {
            policy,
            ..Self::default()
        }
    }

    pub fn from_surface(surface: MonomorphizeInstanceCacheSurface) -> Self {
        if surface.format_version != MONOMORPHIZE_INSTANCE_CACHE_FORMAT_VERSION {
            return Self::default();
        }
        let entries = surface
            .instances
            .into_iter()
            .map(|instance| (instance.key.clone(), instance))
            .collect();
        Self {
            entries,
            policy: MonomorphizeInstanceCachePolicy::default(),
            profile: MonomorphizeInstanceCacheProfile::default(),
        }
    }

    pub fn to_surface(&self) -> MonomorphizeInstanceCacheSurface {
        MonomorphizeInstanceCacheSurface {
            format_version: MONOMORPHIZE_INSTANCE_CACHE_FORMAT_VERSION,
            instances: self.entries.values().cloned().collect(),
        }
    }

    pub fn profile(&self) -> MonomorphizeInstanceCacheProfile {
        self.profile
    }

    pub fn get(&mut self, key: &MonomorphizeInstanceKey) -> Option<&CachedMonomorphizeInstance> {
        let instance = self.entries.get(key);
        if instance.is_some() {
            self.profile.hits += 1;
        } else {
            self.profile.misses += 1;
        }
        instance
    }

    pub fn insert(&mut self, instance: CachedMonomorphizeInstance) {
        if self.entries.contains_key(&instance.key) {
            return;
        }
        if self
            .policy
            .max_entries
            .is_some_and(|max_entries| self.entries.len() >= max_entries)
        {
            self.profile.skipped_full += 1;
            return;
        }
        let nodes = expr_node_count(&instance.body);
        if self
            .policy
            .max_body_nodes
            .is_some_and(|max_nodes| nodes > max_nodes)
        {
            self.profile.skipped_large_body += 1;
            return;
        }
        self.profile.inserts += 1;
        self.entries.insert(instance.key.clone(), instance);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MonomorphizeInstanceCachePolicy {
    pub max_entries: Option<usize>,
    pub max_body_nodes: Option<usize>,
}

impl Default for MonomorphizeInstanceCachePolicy {
    fn default() -> Self {
        Self {
            max_entries: Some(4096),
            max_body_nodes: Some(2048),
        }
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct MonomorphizeInstanceCacheProfile {
    pub hits: usize,
    pub misses: usize,
    pub inserts: usize,
    pub skipped_full: usize,
    pub skipped_large_body: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MonomorphizeInstanceCacheSurface {
    pub format_version: u32,
    pub instances: Vec<CachedMonomorphizeInstance>,
}

impl Default for MonomorphizeInstanceCacheSurface {
    fn default() -> Self {
        Self {
            format_version: MONOMORPHIZE_INSTANCE_CACHE_FORMAT_VERSION,
            instances: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct MonomorphizeInstanceKey {
    pub binding: typed_ir::Path,
    pub substitutions: Vec<typed_ir::TypeSubstitution>,
    pub callee_type: RuntimeType,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CachedMonomorphizeInstance {
    pub key: MonomorphizeInstanceKey,
    pub scheme: typed_ir::Scheme,
    pub body: Expr,
    pub callee_type: RuntimeType,
    pub result_type: RuntimeType,
}

impl CachedMonomorphizeInstance {
    pub fn binding_with_alias(&self, alias: typed_ir::Path) -> Binding {
        Binding {
            name: alias,
            type_params: Vec::new(),
            scheme: self.scheme.clone(),
            body: self.body.clone(),
        }
    }
}

fn expr_node_count(expr: &Expr) -> usize {
    1 + match &expr.kind {
        ExprKind::Lambda { body, .. }
        | ExprKind::BindHere { expr: body }
        | ExprKind::Thunk { expr: body, .. }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::AddId { thunk: body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. }
        | ExprKind::Select { base: body, .. } => expr_node_count(body),
        ExprKind::Apply { callee, arg, .. } => expr_node_count(callee) + expr_node_count(arg),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => expr_node_count(cond) + expr_node_count(then_branch) + expr_node_count(else_branch),
        ExprKind::Tuple(items) => items.iter().map(expr_node_count).sum(),
        ExprKind::Record { fields, spread } => {
            fields
                .iter()
                .map(|field| expr_node_count(&field.value))
                .sum::<usize>()
                + spread.as_ref().map_or(0, record_spread_expr_node_count)
        }
        ExprKind::Variant { value, .. } => value.as_deref().map_or(0, expr_node_count),
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            expr_node_count(scrutinee)
                + arms
                    .iter()
                    .map(|arm| {
                        arm.guard.as_ref().map_or(0, expr_node_count) + expr_node_count(&arm.body)
                    })
                    .sum::<usize>()
        }
        ExprKind::Block { stmts, tail } => {
            stmts.iter().map(stmt_node_count).sum::<usize>()
                + tail.as_deref().map_or(0, expr_node_count)
        }
        ExprKind::Handle { body, arms, .. } => {
            expr_node_count(body)
                + arms
                    .iter()
                    .map(|arm| {
                        arm.guard.as_ref().map_or(0, expr_node_count) + expr_node_count(&arm.body)
                    })
                    .sum::<usize>()
        }
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => 0,
    }
}

fn record_spread_expr_node_count(spread: &yulang_runtime_ir::FinalizedRecordSpreadExpr) -> usize {
    match spread {
        yulang_runtime_ir::FinalizedRecordSpreadExpr::Head(expr)
        | yulang_runtime_ir::FinalizedRecordSpreadExpr::Tail(expr) => expr_node_count(expr),
    }
}

fn stmt_node_count(stmt: &yulang_runtime_ir::FinalizedStmt) -> usize {
    match stmt {
        yulang_runtime_ir::FinalizedStmt::Let { value, .. } => expr_node_count(value),
        yulang_runtime_ir::FinalizedStmt::Expr(expr)
        | yulang_runtime_ir::FinalizedStmt::Module { body: expr, .. } => expr_node_count(expr),
    }
}

fn hash_compiled_unit_manifests(manifests: &[CompiledUnitManifest]) -> u64 {
    let mut hasher = DefaultHasher::new();
    for manifest in manifests {
        manifest.artifact_format_version.hash(&mut hasher);
        manifest.parser_format_version.hash(&mut hasher);
        manifest.unit_index.hash(&mut hasher);
        source_compilation_unit_origin_key(manifest.origin).hash(&mut hasher);
        for realm in &manifest.realms {
            realm.identity.hash(&mut hasher);
            realm.version.hash(&mut hasher);
        }
        for band in &manifest.bands {
            band.realm.identity.hash(&mut hasher);
            band.realm.version.hash(&mut hasher);
            band.band.segments.hash(&mut hasher);
        }
        manifest.source_hash.hash(&mut hasher);
        manifest.syntax_hash.hash(&mut hasher);
        manifest.interface_hash.hash(&mut hasher);
        for file in &manifest.files {
            file.path.hash(&mut hasher);
            file.module_path.segments.hash(&mut hasher);
            file.origin.hash(&mut hasher);
            file.source_len.hash(&mut hasher);
            file.source_hash.hash(&mut hasher);
        }
        for dependency in &manifest.dependencies {
            dependency.unit_index.hash(&mut hasher);
            dependency.source_hash.hash(&mut hasher);
            dependency.interface_hash.hash(&mut hasher);
        }
    }
    hasher.finish()
}

fn source_compilation_unit_origin_key(origin: yulang_sources::SourceCompilationUnitOrigin) -> u8 {
    match origin {
        yulang_sources::SourceCompilationUnitOrigin::Entry => 0,
        yulang_sources::SourceCompilationUnitOrigin::Std => 1,
        yulang_sources::SourceCompilationUnitOrigin::User => 2,
        yulang_sources::SourceCompilationUnitOrigin::Mixed => 3,
    }
}

fn io_error_string(error: io::Error) -> String {
    match error.kind() {
        io::ErrorKind::NotFound => "not found".to_string(),
        _ => error.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use yulang_sources::{
        CompiledSourceFileIdentity, CompiledUnitDependency, SourceCompilationUnitOrigin,
        SourceOrigin,
    };

    #[test]
    fn artifact_cache_uses_compiled_unit_manifest_key() {
        let root =
            std::env::temp_dir().join(format!("yulang-finalize-cache-test-{}", std::process::id()));
        let _ = fs::remove_dir_all(&root);
        let cache = MonomorphizeInstanceArtifactCache::new(&root);
        let manifests = vec![manifest(0, 11), manifest(1, 29)];
        let surface = MonomorphizeInstanceCacheSurface {
            format_version: MONOMORPHIZE_INSTANCE_CACHE_FORMAT_VERSION,
            instances: vec![cached_instance()],
        };

        let path = cache
            .write_for_manifests(&manifests, &surface)
            .expect("write finalize instance cache");
        assert!(
            path.components()
                .any(|component| component.as_os_str() == "runtime-finalize-v2")
        );

        let restored = cache
            .read_for_manifests(&manifests)
            .expect("read finalize instance cache");
        let restored_cache = cache.read_cache_for_manifests(&manifests);
        let _ = fs::remove_dir_all(&root);

        assert_eq!(restored, surface);
        assert_eq!(restored_cache.to_surface(), surface);
    }

    #[test]
    fn artifact_cache_rejects_mixed_compiled_formats() {
        let mut manifests = vec![manifest(0, 11), manifest(1, 29)];
        manifests[1].artifact_format_version += 1;

        assert_eq!(
            MonomorphizeInstanceArtifactCacheKey::from_manifests(&manifests),
            Err(MonomorphizeInstanceArtifactCacheError::MixedCompiledFormats)
        );
    }

    fn cached_instance() -> CachedMonomorphizeInstance {
        let int = typed_ir::Type::Named {
            path: typed_ir::Path::from_name(typed_ir::Name("int".into())),
            args: Vec::new(),
        };
        CachedMonomorphizeInstance {
            key: MonomorphizeInstanceKey {
                binding: typed_ir::Path::from_name(typed_ir::Name("id".into())),
                substitutions: vec![typed_ir::TypeSubstitution {
                    var: typed_ir::TypeVar("a".into()),
                    ty: int.clone(),
                }],
                callee_type: RuntimeType::Value(int.clone()),
            },
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: int.clone(),
            },
            body: Expr::typed(
                ExprKind::Lit(typed_ir::Lit::Int("1".into())),
                RuntimeType::Value(int.clone()),
            ),
            callee_type: RuntimeType::Value(int.clone()),
            result_type: RuntimeType::Value(int),
        }
    }

    fn manifest(unit_index: usize, hash: u64) -> CompiledUnitManifest {
        CompiledUnitManifest {
            artifact_format_version: 17,
            parser_format_version: 1,
            unit_index,
            origin: SourceCompilationUnitOrigin::Std,
            realms: Vec::new(),
            bands: Vec::new(),
            files: vec![CompiledSourceFileIdentity {
                path: format!("std/{unit_index}.yu"),
                module_path: typed_ir::Path::from_name(typed_ir::Name(format!("m{unit_index}"))),
                origin: SourceOrigin::Std,
                source_len: 10,
                source_hash: hash,
            }],
            dependencies: (unit_index > 0)
                .then(|| CompiledUnitDependency {
                    unit_index: unit_index - 1,
                    source_hash: hash - 1,
                    interface_hash: hash + 1,
                })
                .into_iter()
                .collect(),
            source_hash: hash,
            syntax_hash: hash + 10,
            interface_hash: hash + 20,
        }
    }
}
