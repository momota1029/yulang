//! Source-level runtime compilation glue.
//!
//! Native codegen was archived with `archive/yulang-native`; this crate now
//! only owns source-to-runtime adapters that are shared by frontends.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::path::PathBuf;

pub use yulang_sources::{SourceLoadError, SourceOptions, YulangCachePaths};

pub type SourceRuntimeResult<T> = Result<T, SourceRuntimeError>;

#[derive(Debug)]
pub enum SourceRuntimeError {
    SourceLoad(SourceLoadError),
    SurfaceDiagnostics(Vec<String>),
    RuntimeLower(yulang_runtime::RuntimeError),
    RuntimeMerge(yulang_infer::CompiledRuntimeMergeError),
    DependencyCacheMiss,
    DependencyCacheRead(yulang_infer::CompiledUnitArtifactCacheError),
}

impl fmt::Display for SourceRuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SourceRuntimeError::SourceLoad(error) => write!(f, "{error}"),
            SourceRuntimeError::SurfaceDiagnostics(messages) => {
                write!(f, "{}", messages.join("\n"))
            }
            SourceRuntimeError::RuntimeLower(error) => write!(f, "{error}"),
            SourceRuntimeError::RuntimeMerge(error) => {
                write!(
                    f,
                    "failed to merge compiled runtime dependencies: {error:?}"
                )
            }
            SourceRuntimeError::DependencyCacheMiss => {
                write!(f, "compiled dependency cache is empty")
            }
            SourceRuntimeError::DependencyCacheRead(error) => {
                write!(f, "failed to read compiled dependency cache: {error:?}")
            }
        }
    }
}

impl std::error::Error for SourceRuntimeError {}

impl From<SourceLoadError> for SourceRuntimeError {
    fn from(error: SourceLoadError) -> Self {
        SourceRuntimeError::SourceLoad(error)
    }
}

impl From<yulang_runtime::RuntimeError> for SourceRuntimeError {
    fn from(error: yulang_runtime::RuntimeError) -> Self {
        SourceRuntimeError::RuntimeLower(error)
    }
}

impl From<yulang_infer::CompiledRuntimeMergeError> for SourceRuntimeError {
    fn from(error: yulang_infer::CompiledRuntimeMergeError) -> Self {
        SourceRuntimeError::RuntimeMerge(error)
    }
}

#[derive(Debug)]
pub struct CachedRuntimeIrModule {
    pub module: yulang_runtime::Module,
    pub dependency_cache_hit: bool,
    pub dependency_manifests: Vec<yulang_sources::CompiledUnitManifest>,
}

pub fn runtime_module_from_virtual_source_with_options(
    source: &str,
    base_dir: Option<PathBuf>,
    options: SourceOptions,
) -> SourceRuntimeResult<yulang_runtime::Module> {
    let mut lowered = yulang_infer::lower_virtual_source_with_options(source, base_dir, options)?;
    runtime_module_from_lowered_sources(&mut lowered)
}

pub fn runtime_module_from_lowered_sources(
    lowered: &mut yulang_infer::LoweredSources,
) -> SourceRuntimeResult<yulang_runtime::Module> {
    let diagnostics = yulang_infer::collect_surface_diagnostics(&lowered.state);
    if !diagnostics.is_empty() {
        return Err(SourceRuntimeError::SurfaceDiagnostics(
            diagnostics
                .into_iter()
                .map(|diagnostic| diagnostic.message)
                .collect(),
        ));
    }
    let program = yulang_infer::export_core_program(&mut lowered.state);
    yulang_runtime::lower_core_program(program)
        .and_then(yulang_runtime::monomorphize_module)
        .map_err(SourceRuntimeError::from)
}

pub fn runtime_ir_module_from_virtual_source_with_dependency_cache(
    source: &str,
    base_dir: Option<PathBuf>,
    options: SourceOptions,
    cache_paths: &YulangCachePaths,
) -> SourceRuntimeResult<CachedRuntimeIrModule> {
    let source_set = yulang_sources::collect_virtual_source_files_for_cache_key_with_options(
        source,
        base_dir.clone(),
        options.clone(),
    )?;
    let cache = yulang_infer::CompiledUnitArtifactCache::from_paths(cache_paths);
    let manifests = cacheable_dependency_manifests(&source_set);
    let cached_bundle = read_dependency_bundle_from_cache(&cache, &manifests).ok();

    if let Some(bundle) = cached_bundle {
        return runtime_ir_module_from_cached_dependency_bundle(source_set, manifests, bundle);
    }

    let source_set =
        yulang_sources::collect_virtual_source_files_with_options(source, base_dir, options)?;
    let manifests = cacheable_dependency_manifests(&source_set);
    let mut lowered = yulang_infer::lower_source_set(&source_set);
    lowered.state.finalize_compact_results_profiled();
    write_dependency_unit_artifact_bundle(&source_set, &lowered.state, &cache);
    let module =
        runtime_ir_module_from_lowered_sources_with_runtime_dependencies(&mut lowered, None)?;
    Ok(CachedRuntimeIrModule {
        module,
        dependency_cache_hit: false,
        dependency_manifests: manifests,
    })
}

pub fn runtime_ir_module_from_virtual_source_with_dependency_cache_read_only(
    source: &str,
    base_dir: Option<PathBuf>,
    options: SourceOptions,
    cache_paths: &YulangCachePaths,
) -> SourceRuntimeResult<CachedRuntimeIrModule> {
    let source_set = yulang_sources::collect_virtual_source_files_for_cache_key_with_options(
        source, base_dir, options,
    )?;
    let manifests = cacheable_dependency_manifests(&source_set);
    if manifests.is_empty() {
        return Err(SourceRuntimeError::DependencyCacheMiss);
    }
    let cache = yulang_infer::CompiledUnitArtifactCache::from_paths(cache_paths);
    let bundle = read_dependency_bundle_from_cache(&cache, &manifests)?;
    runtime_ir_module_from_cached_dependency_bundle(source_set, manifests, bundle)
}

pub fn runtime_ir_module_from_lowered_sources(
    lowered: &mut yulang_infer::LoweredSources,
) -> SourceRuntimeResult<yulang_runtime::Module> {
    runtime_ir_module_from_lowered_sources_with_runtime_dependencies(lowered, None)
}

fn runtime_ir_module_from_cached_dependency_bundle(
    mut source_set: yulang_sources::SourceSet,
    manifests: Vec<yulang_sources::CompiledUnitManifest>,
    bundle: yulang_infer::CompiledUnitArtifactBundle,
) -> SourceRuntimeResult<CachedRuntimeIrModule> {
    source_set.build_syntax_tables();
    let mut lowered =
        yulang_infer::lower_source_set_with_trusted_compiled_unit_artifact_bundle_profiled(
            &source_set,
            &bundle,
        );
    lowered
        .lowered
        .lowered
        .state
        .finalize_compact_results_profiled();
    let module = runtime_ir_module_from_lowered_sources_with_runtime_dependencies(
        &mut lowered.lowered.lowered,
        Some(&lowered.runtime),
    )?;
    Ok(CachedRuntimeIrModule {
        module,
        dependency_cache_hit: true,
        dependency_manifests: manifests,
    })
}

fn runtime_ir_module_from_lowered_sources_with_runtime_dependencies(
    lowered: &mut yulang_infer::LoweredSources,
    runtime_dependencies: Option<&yulang_infer::CompiledRuntimeBundle>,
) -> SourceRuntimeResult<yulang_runtime::Module> {
    let diagnostics = yulang_infer::collect_surface_diagnostics(&lowered.state);
    if !diagnostics.is_empty() {
        return Err(SourceRuntimeError::SurfaceDiagnostics(
            diagnostics
                .into_iter()
                .map(|diagnostic| diagnostic.message)
                .collect(),
        ));
    }
    let mut program = yulang_infer::export_core_program(&mut lowered.state);
    if let Some(runtime_dependencies) = runtime_dependencies {
        program = runtime_dependencies.merge_with_user_program(program)?;
    }
    yulang_runtime::lower_core_program(program).map_err(SourceRuntimeError::from)
}

fn cacheable_dependency_manifests(
    source_set: &yulang_sources::SourceSet,
) -> Vec<yulang_sources::CompiledUnitManifest> {
    source_set
        .compiled_unit_syntax_artifacts()
        .into_iter()
        .map(|artifact| artifact.manifest)
        .filter(is_cacheable_dependency_manifest)
        .collect()
}

fn read_dependency_bundle_from_cache(
    cache: &yulang_infer::CompiledUnitArtifactCache,
    manifests: &[yulang_sources::CompiledUnitManifest],
) -> SourceRuntimeResult<yulang_infer::CompiledUnitArtifactBundle> {
    if manifests.is_empty() {
        return Err(SourceRuntimeError::DependencyCacheMiss);
    }
    if let Ok(bundle) = cache.read_bundle_for_manifests(manifests) {
        return Ok(bundle);
    }

    let mut artifacts_by_unit = BTreeMap::new();
    for manifest in manifests {
        if let Ok(artifact) = cache.read_for_manifest(manifest) {
            artifacts_by_unit.insert(manifest.unit_index, artifact);
        }
    }
    let selected_units = dependency_closed_cached_units(manifests, artifacts_by_unit.keys());
    if selected_units.is_empty() {
        return Err(SourceRuntimeError::DependencyCacheMiss);
    }
    let artifacts = artifacts_by_unit
        .into_iter()
        .filter_map(|(unit_idx, artifact)| selected_units.contains(&unit_idx).then_some(artifact))
        .collect::<Vec<_>>();
    let bundle = yulang_infer::build_compiled_unit_artifact_bundle(&artifacts)?;
    let _ = cache.write_bundle(&bundle);
    Ok(bundle)
}

fn dependency_closed_cached_units<'a>(
    manifests: &'a [yulang_sources::CompiledUnitManifest],
    cached_units: impl Iterator<Item = &'a usize>,
) -> BTreeSet<usize> {
    let manifests_by_unit = manifests
        .iter()
        .map(|manifest| (manifest.unit_index, manifest))
        .collect::<BTreeMap<_, _>>();
    let mut selected = cached_units.copied().collect::<BTreeSet<_>>();
    loop {
        let before = selected.len();
        let previous = selected.clone();
        selected.retain(|unit_idx| {
            let Some(manifest) = manifests_by_unit.get(unit_idx) else {
                return false;
            };
            manifest
                .dependencies
                .iter()
                .all(|dependency| previous.contains(&dependency.unit_index))
        });
        if selected.len() == before {
            return selected;
        }
    }
}

fn is_cacheable_dependency_manifest(manifest: &yulang_sources::CompiledUnitManifest) -> bool {
    manifest.origin != yulang_sources::SourceCompilationUnitOrigin::Entry
        && manifest
            .files
            .iter()
            .all(|file| file.origin != yulang_sources::SourceOrigin::Entry)
}

fn write_dependency_unit_artifact_bundle(
    source_set: &yulang_sources::SourceSet,
    state: &yulang_infer::LowerState,
    cache: &yulang_infer::CompiledUnitArtifactCache,
) {
    let artifacts = yulang_infer::build_compiled_unit_artifacts(source_set, state)
        .into_iter()
        .filter(|artifact| is_cacheable_dependency_manifest(&artifact.manifest))
        .collect::<Vec<_>>();
    if artifacts.is_empty() {
        return;
    }
    for artifact in &artifacts {
        let _ = cache.write(artifact);
    }
    if let Ok(bundle) = yulang_infer::build_compiled_unit_artifact_bundle(&artifacts) {
        let _ = cache.write_bundle(&bundle);
        let semantic_bundle = yulang_infer::CompiledUnitSemanticArtifactBundle::from(&bundle);
        let _ = cache.write_semantic_bundle(&semantic_bundle);
    } else {
        let semantic_bundle =
            yulang_infer::build_compiled_unit_semantic_artifact_bundle(&artifacts);
        let _ = cache.write_semantic_bundle(&semantic_bundle);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lowers_literal_source_to_runtime_module() {
        let module = runtime_module_from_virtual_source_with_options(
            "41",
            None,
            SourceOptions {
                implicit_prelude: false,
                std_root: None,
                search_paths: Vec::new(),
            },
        )
        .expect("runtime module");

        assert_eq!(module.root_exprs.len(), 1);
    }

    #[test]
    fn virtual_source_runtime_ir_uses_compiled_dependency_cache_on_second_run() {
        let repo_root = temp_cache_root("compiled-dependency-cache-root");
        let std_root = repo_root.join("std");
        std::fs::create_dir_all(&std_root).unwrap();
        std::fs::write(std_root.join("prelude.yu"), "pub id x = x\n").unwrap();
        let cache_root = repo_root.join("cache");
        let cache_paths = YulangCachePaths::with_user_cache_root(&repo_root, cache_root);
        let options = SourceOptions {
            std_root: Some(std_root),
            implicit_prelude: true,
            search_paths: Vec::new(),
        };

        let first = runtime_ir_module_from_virtual_source_with_dependency_cache(
            "id 1\n",
            Some(repo_root.clone()),
            options.clone(),
            &cache_paths,
        )
        .expect("first runtime ir lower");
        let second = runtime_ir_module_from_virtual_source_with_dependency_cache(
            "id 1\n",
            Some(repo_root.clone()),
            options,
            &cache_paths,
        )
        .expect("second runtime ir lower");
        let _ = std::fs::remove_dir_all(repo_root);

        assert!(!first.dependency_cache_hit);
        assert!(second.dependency_cache_hit);
        assert!(!second.dependency_manifests.is_empty());
        assert_eq!(second.module.root_exprs.len(), 1);
    }

    #[test]
    fn virtual_source_runtime_ir_read_only_cache_uses_warmed_dependency_bundle() {
        let repo_root = temp_cache_root("read-only-compiled-dependency-cache-root");
        let std_root = repo_root.join("std");
        std::fs::create_dir_all(&std_root).unwrap();
        std::fs::write(std_root.join("prelude.yu"), "pub id x = x\n").unwrap();
        let cache_root = repo_root.join("cache");
        let cache_paths = YulangCachePaths::with_user_cache_root(&repo_root, cache_root);
        let options = SourceOptions {
            std_root: Some(std_root),
            implicit_prelude: true,
            search_paths: Vec::new(),
        };

        let warmed = runtime_ir_module_from_virtual_source_with_dependency_cache(
            "id 1\n",
            Some(repo_root.clone()),
            options.clone(),
            &cache_paths,
        )
        .expect("warm runtime ir cache");
        let cached = runtime_ir_module_from_virtual_source_with_dependency_cache_read_only(
            "id 1\n",
            Some(repo_root.clone()),
            options,
            &cache_paths,
        )
        .expect("read warmed runtime ir cache");
        let _ = std::fs::remove_dir_all(repo_root);

        assert!(!warmed.dependency_cache_hit);
        assert!(cached.dependency_cache_hit);
        assert!(!cached.dependency_manifests.is_empty());
        assert_eq!(cached.module.root_exprs.len(), 1);
    }

    #[test]
    fn virtual_source_runtime_ir_dependency_cache_preserves_nominal_enum_payload_bundle() {
        run_with_large_stack(|| {
            let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
            let std_root = repo_root.join("lib/std");
            let cache_root = temp_cache_root("compiled-dependency-cache-nominal-enum-payload");
            let cache_paths =
                YulangCachePaths::with_user_cache_root(&cache_root, cache_root.clone());
            let options = SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            };

            let source = "println { a: \"a\", b: [\"あ\"] }.debug\n";
            let first = runtime_ir_module_from_virtual_source_with_dependency_cache(
                source,
                Some(repo_root.clone()),
                options.clone(),
                &cache_paths,
            )
            .expect("warm runtime ir dependency cache");
            let second = runtime_ir_module_from_virtual_source_with_dependency_cache(
                source,
                Some(repo_root),
                options,
                &cache_paths,
            )
            .expect("cached runtime ir dependency cache");
            let _ = std::fs::remove_dir_all(cache_root);

            assert!(!first.dependency_cache_hit);
            assert!(second.dependency_cache_hit);
            assert_eq!(second.module.root_exprs.len(), 1);
        });
    }

    fn run_with_large_stack<T>(f: impl FnOnce() -> T + Send + 'static) -> T
    where
        T: Send + 'static,
    {
        std::thread::Builder::new()
            .stack_size(128 * 1024 * 1024)
            .spawn(f)
            .expect("spawn large-stack compile test thread")
            .join()
            .unwrap()
    }

    fn temp_cache_root(name: &str) -> PathBuf {
        let path = std::env::temp_dir().join(format!(
            "yulang-compile-{name}-{}-{}",
            std::process::id(),
            std::thread::current().name().unwrap_or("test")
        ));
        let _ = std::fs::remove_dir_all(&path);
        path
    }
}
