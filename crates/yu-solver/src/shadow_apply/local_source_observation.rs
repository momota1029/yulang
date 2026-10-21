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
        source_relations.try_reserve(1).map_err(|_| ArtifactMismatch)?;
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

#[cfg(all(test, feature = "shadow-apply-candidate"))]
mod r202_capture_lineage_tests {
    use super::*;
    use std::sync::Arc;
    use yu_hir::shadow::lower_module_with_local_source;
    use yu_hir::{FileId, FileKey, HirBinding, HirModule, ModuleIdentity, SemanticImports};
    use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

    const SOURCE: &str = r#"act signal:
    our ping: () -> int
my finish (x:[signal] int) = x
my outer (t:[signal] int) = {
    my bridge (x:[signal] int) = outer x;
    my relay (u:[signal] int) = bridge u;
    catch t { signal::ping(), _ -> relay t, v -> finish t }
}"#;

    fn binding<'a>(hir: &'a HirModule, name: &str) -> &'a HirBinding {
        hir.items().iter().find_map(|item| match item {
            yu_hir::HirItem::Binding(binding) if binding.name().spelling() == name => Some(binding),
            _ => None,
        }).unwrap_or_else(|| panic!("missing binding {name}"))
    }

    #[test]
    fn relay_capture_snapshots_join_existing_bound_emissions_and_source_sets() {
        let source: Arc<SourceText> = Arc::from(SOURCE);
        let parsed = parse_file(source.clone(), Arc::new(scan_header(source)), Arc::new(SyntaxEnvironment::empty()));
        assert!(parsed.structural_recoveries().is_empty());
        let hir = Arc::new(lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new("r202-capture-lineage", "relay.yu"))),
            &parsed, SemanticImports::empty(),
        ).unwrap());
        let outer = binding(&hir, "outer");
        let local = hir.local_source(outer.definition_root()).unwrap().unwrap();
        let apply = local.expressions().iter().find(|expr| expr.occurrence.ordinal() == 18).unwrap();
        assert!(matches!(&apply.form, yu_hir::shadow::LocalSourceForm::Apply { .. }));
        let occurrence_15 = local.expressions().iter()
            .find(|expr| expr.occurrence.ordinal() == 15).map(|expr| &expr.form);
        println!("R206 source_occurrence_15={occurrence_15:?}");

        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        let observed = candidate.local_source_provider_observation(&apply.occurrence, 256).unwrap();
        assert!(observed.facts_complete && observed.origins_complete);
        assert!(!observed.captures_truncated);
        assert_eq!(observed.routes.len(), 1);

        let graph = candidate.solved.data.candidate_graph.as_ref().unwrap();
        let context = &graph.intrusion.effect_algebra.context;
        let references = &candidate.solved.data.candidate_references;
        let target_relations = [53usize, 56, 57, 62];
        let mut seen = std::collections::HashSet::new();
        for capture in &observed.routes[0].captures {
            let Some(CandidateProviderCaptureStructure::Snapshot {
                source_bound, relation: Some(relation), coverage_bits,
            }) = capture.structure else { continue; };
            if !target_relations.contains(&relation) { continue; }
            seen.insert(relation);
            let relation_id = crate::candidate_context::RelationId(relation as u32);
            let events = context.test_source_events_for_relation(relation_id).unwrap_or(&[]);
            let checking = events.iter().filter_map(|&event| references.observed_checking(event))
                .collect::<Vec<_>>();
            let admissions = context.observed_bound_admissions().filter(|(_, admission)| {
                admission.relation == Some(relation_id)
                    && source_bound_key(admission.bound) == source_bound
            }).collect::<Vec<_>>();
            let admission_ids = admissions.iter().map(|(index, _)| *index).collect::<Vec<_>>();
            let emissions = context.observed_bound_emissions_for_relation(relation_id)
                .filter(|(_, emission)| admission_ids.contains(&emission.admission.0)
                    && source_bound_key(emission.bound) == source_bound)
                .collect::<Vec<_>>();
            println!("R202 relation={relation} key={source_bound:?} coverage={coverage_bits} events={events:?} checking={checking:?}");
            for (origin_index, origin) in context.origins.iter().enumerate()
                .filter(|(_, origin)| origin.relation == relation_id)
            {
                let drain_completed = origin.source_drain_receipt.as_ref()
                    .map(|receipt| context.source_drain_completed(receipt));
                println!("  origin={origin_index} occurrence={:?} entry={:?} formal={:?} drain={:?} drain_completed={drain_completed:?}",
                    origin.occurrence, origin.inferred_entry, origin.formal, origin.source_drain_receipt);
            }
            for (index, admission) in &admissions {
                println!("  admission={index} cause={:?} coverage={:?} bound={:?}", admission.cause, admission.coverage, admission.bound);
                if let crate::candidate_context::BoundAdmissionCause::OwnerEmission { processing: Some(processing) } = admission.cause {
                    let process_events = context.test_source_events_for_relation(processing).unwrap_or(&[]);
                    let process_checking = process_events.iter()
                        .filter_map(|&event| references.observed_checking(event)).collect::<Vec<_>>();
                    println!("    processing={processing:?} source_events={process_events:?} checking={process_checking:?}");
                    for (origin_index, origin) in context.origins.iter().enumerate()
                        .filter(|(_, origin)| origin.relation == processing)
                    {
                        let drain_completed = origin.source_drain_receipt.as_ref()
                            .map(|receipt| context.source_drain_completed(receipt));
                        println!("    processing_origin={origin_index} occurrence={:?} entry={:?} formal={:?} drain={:?} drain_completed={drain_completed:?}",
                            origin.occurrence, origin.inferred_entry, origin.formal, origin.source_drain_receipt);
                    }
                }
            }
            for (index, emission) in &emissions {
                println!("  emission={index} admission={} physical={:?} readback={:?}", emission.admission.0, emission.physical, emission.readback);
            }
            assert!(!admissions.is_empty(), "captured relation {relation} has no matching retained admission");
            assert!(!emissions.is_empty(), "captured relation {relation} has no matching physical emission");
        }
        for capture in &observed.routes[0].captures {
            let Some(CandidateProviderCaptureStructure::Snapshot { source_bound, relation: Some(relation), .. }) = capture.structure else { continue; };
            let relation_id = crate::candidate_context::RelationId(relation as u32);
            for (origin_index, origin) in context.origins.iter().enumerate()
                .filter(|(_, origin)| origin.relation == relation_id && [1, 2, 4].contains(&origin.occurrence.local_slot())
            ) {
                let ordinal = origin.occurrence.occurrence().ordinal();
                let form = local.expressions().iter()
                    .find(|expr| expr.occurrence.ordinal() == ordinal).map(|expr| &expr.form);
                let drain_completed = origin.source_drain_receipt.as_ref()
                    .map(|receipt| context.source_drain_completed(receipt));
                println!("R207 captured_relation={relation} bound={source_bound:?} origin={origin_index} occurrence={ordinal} slot={} form={form:?} drain_completed={drain_completed:?}",
                    origin.occurrence.local_slot());
            }
        }
        let captured_relations = observed.routes[0].captures.iter().filter_map(|capture| match capture.structure {
            Some(CandidateProviderCaptureStructure::Snapshot { relation: Some(relation), .. }) => Some(relation),
            _ => None,
        }).collect::<std::collections::HashSet<_>>();
        for (origin_index, origin) in context.origins.iter().enumerate().filter(|(_, origin)| {
            origin.occurrence.occurrence().ordinal() == 12 && origin.occurrence.local_slot() == 4
        }) {
            let relation = origin.relation;
            let drain_completed = origin.source_drain_receipt.as_ref()
                .map(|receipt| context.source_drain_completed(receipt));
            println!("R208 lambda_slot4 origin={origin_index} relation={relation:?} captured={} occurrence={:?} drain={:?} drain_completed={drain_completed:?}",
                captured_relations.contains(&(relation.0 as usize)), origin.occurrence, origin.source_drain_receipt);
            for (admission, record, emissions) in context.test_admission_emissions_for_relation(relation) {
                println!("  lambda_slot4 admission={admission:?} record={record:?} emissions={emissions:?}");
            }
        }
        let candidate_graph = candidate.solved.data.candidate_graph.as_ref().unwrap();
        let provider_route = &candidate_graph.local_routes[observed.routes[0].route];
        assert_eq!(&provider_route.local, observed.target);
        let source_owner_rep = candidate_graph.intrusion.rep(crate::candidate_scheme::RowKey::Effect(10));
        let source_result_rep = candidate_graph.intrusion.rep(crate::candidate_scheme::RowKey::Effect(31));
        println!("R211 source_owner=Effect(10) rep={source_owner_rep:?} source_result=Effect(31) rep={source_result_rep:?}");
        let provider_binding = local.bindings().iter().find(|binding| &binding.id == observed.target).unwrap();
        let provider_initializer = local.expression(&provider_binding.initializer).unwrap();
        let provider_lambda_ordinal = provider_initializer.occurrence.ordinal();
        println!("R209 provider_binding={} local_id={:?} initializer={} form={:?}",
            provider_binding.spelling, provider_binding.id, provider_lambda_ordinal, provider_initializer.form);
        let provider_capture_relations = observed.routes[0].captures.iter().filter_map(|capture| match capture.structure {
            Some(CandidateProviderCaptureStructure::Snapshot { relation: Some(relation), .. }) => Some(relation),
            _ => None,
        }).collect::<std::collections::HashSet<_>>();
        println!("R210 provider_route={} occurrence={:?} graph_root={} live_root={} boundary={} source_frontier={:?} rows={:?}",
            observed.routes[0].route, provider_route.occurrence, provider_route.graph.root,
            provider_route.graph.live_root, provider_route.graph.boundary, provider_route.graph.source_frontier,
            provider_route.graph.rows);
        for row in &provider_route.graph.capture_rows {
            println!("R210 captured_row={row:?} image={:?}", provider_route.rows.get(row.graph_row));
        }
        for (node_index, node) in provider_route.graph.nodes.iter().enumerate() {
            if let crate::candidate_scheme::Node::Function { polarity, children } = node {
                println!("R210 function_node={node_index} polarity={polarity:?} children={children:?}");
                for (port, &child) in children.iter().enumerate() {
                    if let Some(crate::candidate_scheme::Node::Row { row, polarity }) = provider_route.graph.nodes.get(child) {
                        println!("  function_port={port} child={child} row={:?} polarity={polarity:?} capture={:?} image={:?}",
                            provider_route.graph.rows.get(*row), provider_route.graph.capture_rows.get(*row),
                            provider_route.rows.get(*row));
                    }
                }
            }
        }
        for (bound_index, bound) in provider_route.graph.bounds.iter().enumerate()
            .filter(|(_, bound)| bound.kind == yu_types::ComponentKind::Effect)
        {
            let lower = match provider_route.graph.nodes.get(bound.lower) {
                Some(crate::candidate_scheme::Node::Row { row, polarity }) => provider_route.graph.rows.get(*row).map(|row| (row.key, *polarity)),
                _ => None,
            };
            let upper = match provider_route.graph.nodes.get(bound.upper) {
                Some(crate::candidate_scheme::Node::Row { row, polarity }) => provider_route.graph.rows.get(*row).map(|row| (row.key, *polarity)),
                _ => None,
            };
            println!("R211 captured_effect_bound={bound_index} source={:?} relation={:?} lower={lower:?} upper={upper:?}",
                bound.source_bound, bound.relation);
        }
        for (snapshot_index, snapshot) in provider_route.graph.bound_evidence.iter().enumerate() {
            let key = source_bound_key(snapshot.source_bound);
            if format!("{key:?}").contains("EffectRow(10)") || format!("{key:?}").contains("EffectRow(31)") {
                println!("R211 captured_effect_snapshot={snapshot_index} key={key:?} relation={:?} coverage={:?}",
                    snapshot.relation, snapshot.coverage);
            }
        }
        println!("R210 replay_dependencies={:?}", observed.routes[0].replay_dependencies);
        for (origin_index, origin) in context.origins.iter().enumerate().filter(|(_, origin)| {
            origin.occurrence.occurrence().ordinal() == provider_lambda_ordinal
                && origin.occurrence.local_slot() == 4
        }) {
            let task = origin.source_drain_receipt.as_ref().map(|receipt| receipt.task);
            let completed = origin.source_drain_receipt.as_ref()
                .map(|receipt| context.source_drain_completed(receipt));
            println!("R209 provider_lambda_slot4 origin={origin_index} relation={:?} captured={} occurrence={:?} task={task:?} completed={completed:?}",
                origin.relation, provider_capture_relations.contains(&(origin.relation.0 as usize)), origin.occurrence);
            println!("  provider_slot4_lineage={:?}", context.test_relation_lineage(origin.relation));
        }
        for row in &provider_route.graph.capture_rows {
            if [10, 31].iter().any(|&id| row.requested == crate::candidate_scheme::RowKey::Effect(id)
                || row.representative == crate::candidate_scheme::RowKey::Effect(id))
            {
                println!("R209 capture_row={row:?}");
            }
        }
        assert_eq!(seen.into_iter().collect::<std::collections::HashSet<_>>(), target_relations.into_iter().collect());
    }
}
