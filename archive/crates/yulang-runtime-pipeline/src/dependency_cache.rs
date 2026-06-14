//! Compiled dependency artifact cache support.
//!
//! The runtime pipeline only treats compiled dependency artifacts as an input
//! surface. Source collection and runtime lowering stay in `lib.rs`; this
//! module owns the cache-selection policy and cache writes.

use crate::{RuntimePipelineError, RuntimePipelineResult};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DependencyBundleReadMode {
    Persist,
    ReadOnly,
}

pub(crate) fn cacheable_dependency_manifests(
    source_set: &yulang_sources::SourceSet,
) -> Vec<yulang_sources::CompiledUnitManifest> {
    source_set
        .compiled_unit_syntax_artifacts()
        .into_iter()
        .map(|artifact| artifact.manifest)
        .filter(is_cacheable_dependency_manifest)
        .collect()
}

pub(crate) fn read_dependency_bundle_from_cache(
    cache: &yulang_infer::CompiledUnitArtifactCache,
    manifests: &[yulang_sources::CompiledUnitManifest],
    mode: DependencyBundleReadMode,
) -> RuntimePipelineResult<yulang_infer::CompiledUnitArtifactBundle> {
    if manifests.is_empty() {
        return Err(RuntimePipelineError::DependencyCacheMiss);
    }
    if let Ok(bundle) = cache.read_bundle_for_manifests(manifests) {
        return Ok(bundle);
    }

    let mut artifacts = Vec::with_capacity(manifests.len());
    for manifest in manifests {
        artifacts.push(
            cache
                .read_for_manifest(manifest)
                .map_err(|_| RuntimePipelineError::DependencyCacheMiss)?,
        );
    }
    let bundle = yulang_infer::build_compiled_unit_artifact_bundle(&artifacts)?;
    if matches!(mode, DependencyBundleReadMode::Persist) {
        let _ = cache.write_bundle(&bundle);
    }
    Ok(bundle)
}

pub(crate) fn write_dependency_unit_artifact_bundle(
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

fn is_cacheable_dependency_manifest(manifest: &yulang_sources::CompiledUnitManifest) -> bool {
    manifest.origin != yulang_sources::SourceCompilationUnitOrigin::Entry
        && manifest
            .files
            .iter()
            .all(|file| file.origin != yulang_sources::SourceOrigin::Entry)
}
