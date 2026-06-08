//! Source-to-finalized-runtime pipeline for Yulang frontends.
//!
//! This crate is the outer driver for source-facing frontends. Its default
//! path exports erased inference output, elaborates concrete runtime demands,
//! and lowers that elaborated IR to finalized runtime IR. Lower-level transform
//! crates should depend on the concrete IR/pass crates instead of depending on
//! this orchestration crate.

use std::fmt;
use std::path::PathBuf;

pub use yulang_runtime_pipeline::{SourceLoadError, SourceOptions, YulangCachePaths};

pub type SourceRuntimeResult<T> = Result<T, SourceRuntimeError>;

#[derive(Debug)]
pub enum SourceRuntimeError {
    RuntimePipeline(yulang_runtime_pipeline::RuntimePipelineError),
    RuntimeElaborate(yulang_elaborate::ElaborateProgramError),
    RuntimeFinalize(yulang_monomorphize::MonomorphizeError),
}

impl fmt::Display for SourceRuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SourceRuntimeError::RuntimePipeline(error) => write!(f, "{error}"),
            SourceRuntimeError::RuntimeElaborate(error) => write!(f, "{error:?}"),
            SourceRuntimeError::RuntimeFinalize(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for SourceRuntimeError {}

impl From<yulang_runtime_pipeline::RuntimePipelineError> for SourceRuntimeError {
    fn from(error: yulang_runtime_pipeline::RuntimePipelineError) -> Self {
        SourceRuntimeError::RuntimePipeline(error)
    }
}

impl From<yulang_monomorphize::MonomorphizeError> for SourceRuntimeError {
    fn from(error: yulang_monomorphize::MonomorphizeError) -> Self {
        SourceRuntimeError::RuntimeFinalize(error)
    }
}

impl From<yulang_elaborate::ElaborateProgramError> for SourceRuntimeError {
    fn from(error: yulang_elaborate::ElaborateProgramError) -> Self {
        SourceRuntimeError::RuntimeElaborate(error)
    }
}

#[derive(Debug)]
pub struct CachedRuntimeIrModule {
    pub module: yulang_runtime_ir::FinalizedModule,
    pub dependency_cache_hit: bool,
    pub dependency_manifests: Vec<yulang_sources::CompiledUnitManifest>,
}

pub fn runtime_module_from_virtual_source_with_options(
    source: &str,
    base_dir: Option<PathBuf>,
    options: SourceOptions,
) -> SourceRuntimeResult<yulang_runtime_ir::FinalizedModule> {
    elaborated_runtime_module_from_virtual_source_with_options(source, base_dir, options)
}

pub fn runtime_module_from_lowered_sources(
    lowered: &mut yulang_infer::LoweredSources,
) -> SourceRuntimeResult<yulang_runtime_ir::FinalizedModule> {
    elaborated_runtime_module_from_lowered_sources(lowered)
}

pub fn elaborated_runtime_module_from_virtual_source_with_options(
    source: &str,
    base_dir: Option<PathBuf>,
    options: SourceOptions,
) -> SourceRuntimeResult<yulang_runtime_ir::FinalizedModule> {
    let mut lowered = yulang_infer::lower_virtual_source_with_options(source, base_dir, options)
        .map_err(yulang_runtime_pipeline::RuntimePipelineError::from)?;
    elaborated_runtime_module_from_lowered_sources(&mut lowered)
}

pub fn elaborated_runtime_module_from_lowered_sources(
    lowered: &mut yulang_infer::LoweredSources,
) -> SourceRuntimeResult<yulang_runtime_ir::FinalizedModule> {
    lowered.state.finalize_compact_results_profiled();
    let diagnostics = yulang_infer::collect_surface_diagnostics(&lowered.state);
    if !diagnostics.is_empty() {
        return Err(SourceRuntimeError::RuntimePipeline(
            yulang_runtime_pipeline::RuntimePipelineError::SurfaceDiagnostics(
                diagnostics
                    .into_iter()
                    .map(|diagnostic| diagnostic.message)
                    .collect(),
            ),
        ));
    }
    let export = yulang_infer::export_erased_program(&mut lowered.state);
    let elaborated = yulang_elaborate::Elaborator::new(&export).build_program()?;
    yulang_runtime_lower::lower_elaborated_program(elaborated)
        .map_err(yulang_runtime_pipeline::RuntimePipelineError::from)
        .map_err(SourceRuntimeError::from)
}

// Compiled dependency cache APIs still expose lowered-runtime artifacts. They
// stay on the legacy finalization path until compiled erased exports exist.
pub fn runtime_ir_module_from_virtual_source_with_dependency_cache(
    source: &str,
    base_dir: Option<PathBuf>,
    options: SourceOptions,
    cache_paths: &YulangCachePaths,
) -> SourceRuntimeResult<CachedRuntimeIrModule> {
    let cached =
        yulang_runtime_pipeline::lowered_runtime_module_from_virtual_source_with_dependency_cache(
            source,
            base_dir,
            options,
            cache_paths,
        )?;
    finalize_cached_runtime_module(cached)
}

pub fn runtime_ir_module_from_virtual_source_with_dependency_cache_read_only(
    source: &str,
    base_dir: Option<PathBuf>,
    options: SourceOptions,
    cache_paths: &YulangCachePaths,
) -> SourceRuntimeResult<CachedRuntimeIrModule> {
    let cached = yulang_runtime_pipeline::lowered_runtime_module_from_virtual_source_with_dependency_cache_read_only(
        source,
        base_dir,
        options,
        cache_paths,
    )?;
    finalize_cached_runtime_module(cached)
}

fn finalize_cached_runtime_module(
    cached: yulang_runtime_pipeline::CachedLoweredRuntimeModule,
) -> SourceRuntimeResult<CachedRuntimeIrModule> {
    Ok(CachedRuntimeIrModule {
        module: yulang_monomorphize::monomorphize_module(cached.module)?,
        dependency_cache_hit: cached.dependency_cache_hit,
        dependency_manifests: cached.dependency_manifests,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn finalizes_literal_source_to_runtime_module() {
        let module = runtime_module_from_virtual_source_with_options(
            "41",
            None,
            SourceOptions {
                implicit_prelude: false,
                std_root: None,
                search_paths: Vec::new(),
            },
        )
        .expect("finalized runtime module");

        assert_eq!(module.root_exprs.len(), 1);
    }

    #[test]
    fn default_runtime_module_uses_elaborated_instance_paths() {
        let module = runtime_module_from_virtual_source_with_options(
            "my id x = x\nid 1\n",
            None,
            SourceOptions {
                implicit_prelude: false,
                std_root: None,
                search_paths: Vec::new(),
            },
        )
        .expect("elaborated runtime module");

        assert_eq!(module.root_exprs.len(), 1);
        assert!(module.bindings.iter().any(|binding| {
            binding
                .name
                .segments
                .last()
                .is_some_and(|name| name.0.starts_with("mono"))
        }));
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

    fn temp_cache_root(name: &str) -> PathBuf {
        let path = std::env::temp_dir().join(format!(
            "yulang-pipeline-{name}-{}-{}",
            std::process::id(),
            std::thread::current().name().unwrap_or("test")
        ));
        let _ = std::fs::remove_dir_all(&path);
        path
    }
}
