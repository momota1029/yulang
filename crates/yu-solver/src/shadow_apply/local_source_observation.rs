//! Structural, source-keyed readback for one local-callee Apply.
//! This deliberately reports gaps instead of authorizing inference behavior.
use super::*;
use crate::candidate_context::Dependency;
use yu_hir::shadow::{LocalSourceForm, LocalSourceResolution};

/// One exact local route plus the already-retained rows associated with it.
pub struct CandidateLocalProviderRoute<'a> {
    pub graph_index: usize,
    pub route: usize,
    pub source_relation: Option<usize>,
    pub source_drain_complete: bool,
    pub context_use: usize,
    pub captures: Vec<CandidateProviderCaptureRow<'a>>,
    pub replay_dependencies: Vec<CandidateLocalReplayDependency>,
    pub capture_coverage_complete: bool,
}

/// One retained Replay edge touching the direct source relation, with the
/// actual Origin index that authenticated that relation as a source seed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CandidateLocalReplayDependency {
    pub graph_index: usize,
    pub source_relation: usize,
    pub source_origin_index: usize,
    pub ordinal: usize,
    pub child: u32,
    pub lower: u32,
    pub upper: u32,
    pub lower_input: CandidateSourceBoundKey,
    pub upper_input: CandidateSourceBoundKey,
}

/// Read-only structural evidence for a direct local-name Apply.
/// `preservation_complete` is always false: this view does not authenticate a
/// Replay-child completion receipt or prove coverage of all native fibers.
pub struct CandidateLocalSourceProviderObservation<'a> {
    pub apply: &'a HirOccurrenceId,
    pub callee: &'a HirOccurrenceId,
    pub target: &'a yu_hir::HirLocalId,
    pub native_callee: Term,
    pub native_demand: Term,
    pub source: CandidateSourceOccurrenceObservation<'a>,
    pub routes: Vec<CandidateLocalProviderRoute<'a>>,
    pub facts_complete: bool,
    pub origins_complete: bool,
    pub captures_truncated: bool,
    pub replay_child_completion_receipt_available: bool,
    pub preservation_complete: bool,
}

impl CandidateInference {
    /// Join one source Apply to an exact local-callee FreshUse route.
    ///
    /// This returns retained construction records, not a typing, admission,
    /// soundness or preservation certificate. The method intentionally leaves
    /// `preservation_complete` false even when all returned rows are present.
    pub fn local_source_provider_observation<'a>(
        &'a self,
        forwarding_apply: &'a HirOccurrenceId,
        max_rows: usize,
    ) -> Result<CandidateLocalSourceProviderObservation<'a>, ArtifactMismatch> {
        if !self.solved.data.errors.is_empty()
            || !self.solved.data.hir.owns_occurrence(forwarding_apply)
        {
            return Err(ArtifactMismatch);
        }
        let call_index = self.solved.data.candidate_calls.calls.iter()
            .position(|call| call.checking.occurrence() == forwarding_apply)
            .ok_or(ArtifactMismatch)?;
        let call = self.source_call(call_index)?;
        let callee = call.callee_source();
        let LocalSourceForm::Name {
            resolution: LocalSourceResolution::Local(target), ..
        } = &callee.form else {
            return Err(ArtifactMismatch);
        };
        let source = self.source_occurrence_observation(forwarding_apply, max_rows)?;
        let facts_complete = source.facts_complete;
        let origins_complete = source.origins_complete;
        let mut source_relations = Vec::new();
        source_relations.try_reserve(self.solved.data.candidate_graph.len()).map_err(|_| ArtifactMismatch)?;
        for (graph_index, graph) in self.solved.data.candidate_graph.iter().enumerate() {
            let context = &graph.intrusion.effect_algebra.context;
            let receipts = source_drain_receipts(context)?;
            for (origin_index, origin) in context.origins.iter().enumerate() {
                if origin.occurrence.occurrence() != forwarding_apply
                    || origin.occurrence.local_slot() != 0
                    || !self.solved.data.store.provenance().iter()
                        .any(|edge| edge.cause().occurrence() == &origin.occurrence)
                {
                    continue;
                }
                let attribution = source_origin_attribution(&origin.occurrence, origin_index, origin, &receipts);
                if is_direct_source_attribution(&attribution) {
                    source_relations.push((graph_index, origin.relation.0 as usize, origin_index));
                }
            }
        }

        let ordinary = self.ordinary_provider_observation(max_rows)?;
        let captures_truncated = ordinary.truncated;
        let mut routes = Vec::new();
        for (graph_index, graph) in self.solved.data.candidate_graph.iter().enumerate() {
            let Some(route) = graph.local_route_by_occurrence.get(&callee.occurrence).copied() else {
                continue;
            };
            let local_route = graph.local_routes.get(route).ok_or(ArtifactMismatch)?;
            if local_route.occurrence != callee.occurrence || &local_route.local != target {
                return Err(ArtifactMismatch);
            }

            let source_origin = source_relations.iter()
                .find(|(source_graph, _, _)| *source_graph == graph_index);
            if source_relations.iter().filter(|(source_graph, _, _)| *source_graph == graph_index).count() > 1 {
                return Err(ArtifactMismatch);
            }
            let source_relation = source_origin.map(|(_, relation, _)| *relation);
            let context_use = local_route.use_instance;
            let mut route_captures = Vec::new();
            for capture in &ordinary.capture_rows {
                if capture.graph_index == graph_index
                    && capture.route_owner == CandidateReplayRouteOwner::Local
                    && capture.route == route
                {
                    route_captures.push(CandidateProviderCaptureRow {
                        graph_index: capture.graph_index,
                        route_owner: capture.route_owner,
                        route: capture.route,
                        route_occurrence: capture.route_occurrence,
                        context_use: capture.context_use,
                        relation: capture.relation,
                        ordinal: capture.ordinal,
                        kind: capture.kind,
                        map_name: capture.map_name,
                        map_entry: capture.map_entry,
                        structure: capture.structure,
                        record: capture.record,
                    });
                }
            }

            let mut replay_dependencies = Vec::new();
            if let Some(source_relation) = source_relation {
                let context = &graph.intrusion.effect_algebra.context;
                for (ordinal, dependency) in context.observed_dependencies().enumerate() {
                    let Dependency::Replay { child, lower, upper, lower_input, upper_input } = *dependency else {
                        continue;
                    };
                    if lower.0 as usize != source_relation && upper.0 as usize != source_relation {
                        continue;
                    }
                    replay_dependencies.push(CandidateLocalReplayDependency {
                        graph_index,
                        source_relation,
                        source_origin_index: source_origin.map(|(_, _, index)| *index).ok_or(ArtifactMismatch)?,
                        ordinal,
                        child: child.0,
                        lower: lower.0,
                        upper: upper.0,
                        lower_input: source_bound_key(lower_input),
                        upper_input: source_bound_key(upper_input),
                    });
                }
            }
            let capture_coverage_complete = !captures_truncated
                && route_captures.iter().any(|capture| capture.kind == CandidateProviderCaptureKind::CaptureGraph)
                && route_captures.iter().any(|capture| capture.kind == CandidateProviderCaptureKind::FreshUseMap)
                && route_captures.iter().any(|capture| capture.kind == CandidateProviderCaptureKind::CaptureSnapshot)
                && route_captures.iter().all(|capture| match capture.structure {
                    Some(CandidateProviderCaptureStructure::Snapshot { coverage_bits, .. }) => coverage_bits == 0,
                    _ => true,
                });
            routes.push(CandidateLocalProviderRoute {
                graph_index,
                route,
                source_relation,
                source_drain_complete: source_relation.is_some(),
                context_use,
                captures: route_captures,
                replay_dependencies,
                capture_coverage_complete,
            });
        }

        if routes.len() != 1 { return Err(ArtifactMismatch); }

        Ok(CandidateLocalSourceProviderObservation {
            apply: forwarding_apply,
            callee: &callee.occurrence,
            target,
            native_callee: call.native_callee(),
            native_demand: call.native_demand(),
            source,
            routes,
            facts_complete,
            origins_complete,
            captures_truncated,
            replay_child_completion_receipt_available: false,
            preservation_complete: false,
        })
    }
}
