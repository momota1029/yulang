//! Source-to-lowered-runtime pipeline for Yulang.
//!
//! This crate owns the orchestration needed to turn source files into lowered
//! runtime IR: source collection, surface diagnostics, compiled dependency
//! artifacts, typed/core export, and runtime lowering. It deliberately stops
//! before monomorphization/finalization and VM execution, so lower-level
//! transform crates can depend on this crate in tests without depending on the
//! outer user-facing driver.

use std::fmt;
use std::path::PathBuf;

mod dependency_cache;

use dependency_cache::{
    DependencyBundleReadMode, cacheable_dependency_manifests, read_dependency_bundle_from_cache,
    write_dependency_unit_artifact_bundle,
};

pub use yulang_sources::{SourceLoadError, SourceOptions, YulangCachePaths};

pub type RuntimePipelineResult<T> = Result<T, RuntimePipelineError>;

#[derive(Debug)]
pub enum RuntimePipelineError {
    SourceLoad(SourceLoadError),
    SurfaceDiagnostics(Vec<String>),
    RuntimeLower(yulang_runtime_types::RuntimeError),
    RuntimeMerge(yulang_infer::CompiledRuntimeMergeError),
    DependencyCacheMiss,
    DependencyCacheRead(yulang_infer::CompiledUnitArtifactCacheError),
}

impl fmt::Display for RuntimePipelineError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RuntimePipelineError::SourceLoad(error) => write!(f, "{error}"),
            RuntimePipelineError::SurfaceDiagnostics(messages) => {
                write!(f, "{}", messages.join("\n"))
            }
            RuntimePipelineError::RuntimeLower(error) => write!(f, "{error}"),
            RuntimePipelineError::RuntimeMerge(error) => {
                write!(
                    f,
                    "failed to merge compiled runtime dependencies: {error:?}"
                )
            }
            RuntimePipelineError::DependencyCacheMiss => {
                write!(f, "compiled dependency cache is empty")
            }
            RuntimePipelineError::DependencyCacheRead(error) => {
                write!(f, "failed to read compiled dependency cache: {error:?}")
            }
        }
    }
}

impl std::error::Error for RuntimePipelineError {}

impl From<SourceLoadError> for RuntimePipelineError {
    fn from(error: SourceLoadError) -> Self {
        RuntimePipelineError::SourceLoad(error)
    }
}

impl From<yulang_runtime_types::RuntimeError> for RuntimePipelineError {
    fn from(error: yulang_runtime_types::RuntimeError) -> Self {
        RuntimePipelineError::RuntimeLower(error)
    }
}

impl From<yulang_infer::CompiledRuntimeMergeError> for RuntimePipelineError {
    fn from(error: yulang_infer::CompiledRuntimeMergeError) -> Self {
        RuntimePipelineError::RuntimeMerge(error)
    }
}

#[derive(Debug)]
pub struct CachedLoweredRuntimeModule {
    pub module: yulang_runtime_ir::LoweredModule,
    pub dependency_cache_hit: bool,
    pub dependency_manifests: Vec<yulang_sources::CompiledUnitManifest>,
}

pub fn lowered_runtime_module_from_virtual_source_with_options(
    source: &str,
    base_dir: Option<PathBuf>,
    options: SourceOptions,
) -> RuntimePipelineResult<yulang_runtime_ir::LoweredModule> {
    let mut lowered = yulang_infer::lower_virtual_source_with_options(source, base_dir, options)?;
    lowered_runtime_module_from_lowered_sources(&mut lowered)
}

pub fn lowered_runtime_module_from_lowered_sources(
    lowered: &mut yulang_infer::LoweredSources,
) -> RuntimePipelineResult<yulang_runtime_ir::LoweredModule> {
    lowered_runtime_module_from_lowered_sources_with_runtime_dependencies(lowered, None)
}

pub fn lowered_runtime_module_from_virtual_source_with_dependency_cache(
    source: &str,
    base_dir: Option<PathBuf>,
    options: SourceOptions,
    cache_paths: &YulangCachePaths,
) -> RuntimePipelineResult<CachedLoweredRuntimeModule> {
    let source_set = yulang_sources::collect_virtual_source_files_for_cache_key_with_options(
        source,
        base_dir.clone(),
        options.clone(),
    )?;
    let cache = yulang_infer::CompiledUnitArtifactCache::from_paths(cache_paths);
    let manifests = cacheable_dependency_manifests(&source_set);
    let cached_bundle =
        read_dependency_bundle_from_cache(&cache, &manifests, DependencyBundleReadMode::Persist)
            .ok();

    if let Some(bundle) = cached_bundle {
        return lowered_runtime_module_from_cached_dependency_bundle(source_set, manifests, bundle);
    }

    let source_set =
        yulang_sources::collect_virtual_source_files_with_options(source, base_dir, options)?;
    let manifests = cacheable_dependency_manifests(&source_set);
    let mut lowered = yulang_infer::lower_source_set(&source_set);
    lowered.state.finalize_compact_results_profiled();
    write_dependency_unit_artifact_bundle(&source_set, &lowered.state, &cache);
    let module =
        lowered_runtime_module_from_lowered_sources_with_runtime_dependencies(&mut lowered, None)?;
    Ok(CachedLoweredRuntimeModule {
        module,
        dependency_cache_hit: false,
        dependency_manifests: manifests,
    })
}

pub fn lowered_runtime_module_from_virtual_source_with_dependency_cache_read_only(
    source: &str,
    base_dir: Option<PathBuf>,
    options: SourceOptions,
    cache_paths: &YulangCachePaths,
) -> RuntimePipelineResult<CachedLoweredRuntimeModule> {
    let source_set = yulang_sources::collect_virtual_source_files_for_cache_key_with_options(
        source, base_dir, options,
    )?;
    let manifests = cacheable_dependency_manifests(&source_set);
    if manifests.is_empty() {
        return Err(RuntimePipelineError::DependencyCacheMiss);
    }
    let cache = yulang_infer::CompiledUnitArtifactCache::from_paths(cache_paths);
    let bundle =
        read_dependency_bundle_from_cache(&cache, &manifests, DependencyBundleReadMode::ReadOnly)?;
    lowered_runtime_module_from_cached_dependency_bundle(source_set, manifests, bundle)
}

fn lowered_runtime_module_from_cached_dependency_bundle(
    mut source_set: yulang_sources::SourceSet,
    manifests: Vec<yulang_sources::CompiledUnitManifest>,
    bundle: yulang_infer::CompiledUnitArtifactBundle,
) -> RuntimePipelineResult<CachedLoweredRuntimeModule> {
    source_set.build_syntax_tables();
    let imported =
        yulang_infer::lower_source_set_with_trusted_compiled_unit_artifact_bundle_profiled(
            &source_set,
            &bundle,
        );
    let yulang_infer::CompiledUnitProfiledLoweredSources { lowered, runtime } = imported;
    let mut lowered = lowered.lowered;
    lowered.state.finalize_compact_results_profiled();
    let module = lowered_runtime_module_from_lowered_sources_with_runtime_dependencies(
        &mut lowered,
        Some(&runtime),
    )?;
    Ok(CachedLoweredRuntimeModule {
        module,
        dependency_cache_hit: true,
        dependency_manifests: manifests,
    })
}

fn lowered_runtime_module_from_lowered_sources_with_runtime_dependencies(
    lowered: &mut yulang_infer::LoweredSources,
    runtime_dependencies: Option<&yulang_infer::CompiledRuntimeBundle>,
) -> RuntimePipelineResult<yulang_runtime_ir::LoweredModule> {
    let diagnostics = yulang_infer::collect_surface_diagnostics(&lowered.state);
    if !diagnostics.is_empty() {
        return Err(RuntimePipelineError::SurfaceDiagnostics(
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
    yulang_runtime_lower::lower_core_program(program).map_err(RuntimePipelineError::from)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lowers_literal_source_to_lowered_runtime_module() {
        let module = lowered_runtime_module_from_virtual_source_with_options(
            "41",
            None,
            SourceOptions {
                implicit_prelude: false,
                std_root: None,
                search_paths: Vec::new(),
            },
        )
        .expect("lowered runtime module");

        assert_eq!(module.root_exprs.len(), 1);
    }

    #[test]
    fn virtual_source_lowered_runtime_uses_compiled_dependency_cache_on_second_run() {
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

        let first = lowered_runtime_module_from_virtual_source_with_dependency_cache(
            "id 1\n",
            Some(repo_root.clone()),
            options.clone(),
            &cache_paths,
        )
        .expect("first runtime lower");
        let second = lowered_runtime_module_from_virtual_source_with_dependency_cache(
            "id 1\n",
            Some(repo_root.clone()),
            options,
            &cache_paths,
        )
        .expect("second runtime lower");
        let _ = std::fs::remove_dir_all(repo_root);

        assert!(!first.dependency_cache_hit);
        assert!(second.dependency_cache_hit);
        assert!(!second.dependency_manifests.is_empty());
        assert_eq!(second.module.root_exprs.len(), 1);
    }

    #[test]
    fn virtual_source_lowered_runtime_read_only_cache_uses_warmed_dependency_bundle() {
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

        let warmed = lowered_runtime_module_from_virtual_source_with_dependency_cache(
            "id 1\n",
            Some(repo_root.clone()),
            options.clone(),
            &cache_paths,
        )
        .expect("warm runtime cache");
        let cached = lowered_runtime_module_from_virtual_source_with_dependency_cache_read_only(
            "id 1\n",
            Some(repo_root.clone()),
            options,
            &cache_paths,
        )
        .expect("read warmed runtime cache");
        let _ = std::fs::remove_dir_all(repo_root);

        assert!(!warmed.dependency_cache_hit);
        assert!(cached.dependency_cache_hit);
        assert!(!cached.dependency_manifests.is_empty());
        assert_eq!(cached.module.root_exprs.len(), 1);
    }

    #[test]
    fn virtual_source_lowered_runtime_read_only_cache_does_not_persist_rebuilt_bundle() {
        let repo_root = temp_cache_root("read-only-compiled-dependency-no-write");
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

        let warmed = lowered_runtime_module_from_virtual_source_with_dependency_cache(
            "id 1\n",
            Some(repo_root.clone()),
            options.clone(),
            &cache_paths,
        )
        .expect("warm runtime cache");
        let source_set = yulang_sources::collect_virtual_source_files_for_cache_key_with_options(
            "id 1\n",
            Some(repo_root.clone()),
            options.clone(),
        )
        .expect("collect source set for cache key");
        let manifests = cacheable_dependency_manifests(&source_set);
        let cache = yulang_infer::CompiledUnitArtifactCache::from_paths(&cache_paths);
        let bundle_key =
            yulang_infer::artifact_cache::CompiledUnitArtifactBundleCacheKey::from_manifests(
                &manifests,
            )
            .expect("bundle key");
        let bundle_path = cache.bundle_artifact_path(&bundle_key);
        std::fs::remove_file(&bundle_path).expect("remove warmed bundle artifact");

        let cached = lowered_runtime_module_from_virtual_source_with_dependency_cache_read_only(
            "id 1\n",
            Some(repo_root.clone()),
            options,
            &cache_paths,
        )
        .expect("read warmed runtime cache from unit artifacts");
        let bundle_was_rewritten = bundle_path.exists();
        let _ = std::fs::remove_dir_all(repo_root);

        assert!(!warmed.dependency_cache_hit);
        assert!(cached.dependency_cache_hit);
        assert!(!bundle_was_rewritten);
    }

    #[test]
    fn virtual_source_lowered_runtime_dependency_cache_preserves_nominal_enum_payload_bundle() {
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
            let first = lowered_runtime_module_from_virtual_source_with_dependency_cache(
                source,
                Some(repo_root.clone()),
                options.clone(),
                &cache_paths,
            )
            .expect("warm runtime dependency cache");
            let second = lowered_runtime_module_from_virtual_source_with_dependency_cache(
                source,
                Some(repo_root),
                options,
                &cache_paths,
            )
            .expect("cached runtime dependency cache");
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
            .expect("spawn large-stack runtime pipeline test thread")
            .join()
            .unwrap()
    }

    fn temp_cache_root(name: &str) -> PathBuf {
        let path = std::env::temp_dir().join(format!(
            "yulang-runtime-pipeline-{name}-{}-{}",
            std::process::id(),
            std::thread::current().name().unwrap_or("test")
        ));
        let _ = std::fs::remove_dir_all(&path);
        path
    }
}
