//! Compiled dependency artifact cache support.
//!
//! The runtime pipeline only treats compiled dependency artifacts as an input
//! surface. Source collection and runtime lowering stay in `lib.rs`; this
//! module owns the cache-selection policy and cache writes.

use std::collections::{BTreeMap, BTreeSet};

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

    let mut artifacts_by_unit = BTreeMap::new();
    for manifest in manifests {
        if let Ok(artifact) = cache.read_for_manifest(manifest) {
            artifacts_by_unit.insert(manifest.unit_index, artifact);
        }
    }
    let selected_units = dependency_closed_cached_units(manifests, artifacts_by_unit.keys());
    if selected_units.is_empty() {
        return Err(RuntimePipelineError::DependencyCacheMiss);
    }
    let artifacts = artifacts_by_unit
        .into_iter()
        .filter_map(|(unit_idx, artifact)| selected_units.contains(&unit_idx).then_some(artifact))
        .collect::<Vec<_>>();
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
