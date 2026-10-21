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
            || !self.solved.data.owns_occurrence(forwarding_apply)
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
        let effect_bound = |lower, polarity, upper| CandidateSourceBoundKey {
            lower: CandidateSourceBoundEndpoint::Effect(CandidateSourceEffectEndpoint::EffectRow(lower)),
            polarity,
            upper: CandidateSourceBoundEndpoint::Effect(CandidateSourceEffectEndpoint::EffectRow(upper)),
        };
        let target_bounds = [
            effect_bound(29, Polarity::Negative, 9),
            effect_bound(23, Polarity::Negative, 12),
            effect_bound(12, Polarity::Negative, 23),
            effect_bound(12, Polarity::Negative, 29),
        ];
        let mut seen = Vec::new();
        for capture in &observed.routes[0].captures {
            let Some(CandidateProviderCaptureStructure::Snapshot {
                source_bound, relation: Some(relation), coverage_bits,
            }) = capture.structure else { continue; };
            if !target_bounds.contains(&source_bound) { continue; }
            if !seen.contains(&source_bound) { seen.push(source_bound); }
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
        let result_frontier = provider_route.graph.capture_effect_frontiers.iter()
            .find(|frontier| frontier.representative == crate::candidate_scheme::RowKey::Effect(31))
            .expect("Capture recorded canonical Effect(31) effect-row predecessors");
        assert_eq!(result_frontier.requested, crate::candidate_scheme::RowKey::Effect(31));
        assert_eq!(result_frontier.representative, crate::candidate_scheme::RowKey::Effect(31));
        assert!(!result_frontier.truncated, "Effect(31) predecessor snapshot is complete");
        let has_source_owner = result_frontier.direct_lower_rows.contains(&10);
        println!("R215 effect31_capture_frontier={result_frontier:?} contains_effect10={has_source_owner}");
        let source_relation = context.origins.iter().find(|origin|
            origin.occurrence.occurrence().ordinal() == 12
                && origin.occurrence.local_slot() == 4)
            .expect("Lambda slot-4 source owner is retained").relation;
        let captured_source_bound = provider_route.graph.bounds.iter()
            .find(|bound| bound.source_bound == crate::candidate_effect::BoundKey(
                crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(10)),
                Polarity::Negative,
                crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(31)),
            ))
            .expect("Capture retains the Lambda slot-4 source bound through its reverse owner");
        let captured_relation = captured_source_bound.relation
            .expect("reverse-owner bound retains a context relation");
        let lineage = context.test_relation_lineage(captured_relation);
        assert!(lineage.iter().any(|edge| edge.contains(&format!("upper: {source_relation:?}"))),
            "captured bound lineage retains the Lambda slot-4 owner");
        assert_eq!(captured_source_bound.source_bound, crate::candidate_effect::BoundKey(
            crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(10)),
            Polarity::Negative,
            crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(31)),
        ));
        let captured_owner = provider_route.graph.rows.iter()
            .position(|row| row.key == crate::candidate_scheme::RowKey::Effect(10))
            .expect("reverse-owner capture includes Effect(10)");
        assert!(provider_route.graph.capture_rows[captured_owner].local);
        assert!(provider_route.rows.get(captured_owner).is_some(), "local owner has a FreshUse image");
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
        assert_eq!(seen.len(), target_bounds.len());
        for target in target_bounds {
            assert!(seen.contains(&target), "source-bound capture is independent of relation allocation order: {target:?}");
        }
    }

    #[test]
    fn r218_exact_r72_source_ordinary_local_routes() {
        const R72_SOURCE: &str = r#"act io:
    our tick: int -> int

my outer (q:[io] int) = {
    my loop (x:[io] int) = {
        my direct = loop x
        my helper (y:[io] int) = loop y
        helper x
    }
    loop q
}"#;
        let source: Arc<SourceText> = Arc::from(R72_SOURCE);
        let parsed = parse_file(source.clone(), Arc::new(scan_header(source)), Arc::new(SyntaxEnvironment::empty()));
        assert!(parsed.structural_recoveries().is_empty());
        let hir = Arc::new(lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new("r218-r72-source", "source.yu"))),
            &parsed, SemanticImports::empty(),
        ).unwrap());
        let outer = binding(&hir, "outer");
        let local = hir.local_source(outer.definition_root()).unwrap().unwrap();
        let binding_id = |name: &str| local.bindings().iter()
            .find(|binding| binding.spelling.as_ref() == name).unwrap().id.clone();
        let loop_id = binding_id("loop");
        let helper_id = binding_id("helper");
        let source_name = |index: &yu_hir::shadow::LocalSourceIndex| {
            let expression = local.expression(index).unwrap();
            match &expression.form {
                yu_hir::shadow::LocalSourceForm::Name { spelling, resolution, .. } => Some((
                    spelling.as_ref().to_owned(),
                    match resolution {
                        yu_hir::shadow::LocalSourceResolution::Local(id) => Some(id.clone()),
                        _ => None,
                    },
                )),
                _ => None,
            }
        };
        let applies = local.expressions().iter().filter_map(|expression| {
            let yu_hir::shadow::LocalSourceForm::Apply { callee, argument, .. } = &expression.form else { return None; };
            let (callee_spelling, callee_id) = source_name(callee)?;
            let argument_name = source_name(argument).map(|(name, _)| name);
            Some((expression, callee_spelling, callee_id, argument_name))
        }).collect::<Vec<_>>();
        let target_calls = applies.iter().filter(|(_, _, callee, _)| callee.as_ref() == Some(&loop_id) || callee.as_ref() == Some(&helper_id)).collect::<Vec<_>>();
        assert_eq!(target_calls.len(), 4, "the unchanged source has direct loop x, helper loop y, helper x, and loop q");
        println!("R218 source_actions={:?}", target_calls.iter().map(|(expr, callee, _, argument)|
            (expr.occurrence.ordinal(), callee.as_str(), argument.as_deref())).collect::<Vec<_>>());

        crate::candidate_context::r148_trace_begin();
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        let execution_trace = crate::candidate_context::r148_trace_finish();
        println!("R218 candidate_solver_errors={:?}", candidate.solved.data.errors);
        let work_bounds = execution_trace.iter().filter(|event| event.starts_with("work-bound ")).collect::<Vec<_>>();
        let row_merges = execution_trace.iter().filter(|event| event.starts_with("row-merge ")).collect::<Vec<_>>();
        let transports = execution_trace.iter().filter(|event| event.starts_with("bound-transport ")).collect::<Vec<_>>();
        let extrusion_starts = execution_trace.iter().filter(|event| event.starts_with("extrusion-start ")).count();
        let extrusion_finishes = execution_trace.iter().filter(|event| event.starts_with("extrusion-finish ")).count();
        let work_pops = execution_trace.iter().filter(|event| event.starts_with("work-pop ")).count();
        println!("R218 execution_trace events={} work_bounds={} row_merges={} transports={}",
            execution_trace.len(), work_bounds.len(), row_merges.len(), transports.len());
        assert!(extrusion_starts > 0 && extrusion_starts == extrusion_finishes,
            "the successful fixed-source execution has a completed record for every started extrusion");
        assert!(work_pops >= work_bounds.len());
        let expected_work_sources = applies.iter().filter_map(|(expression, _, callee, argument)|
            (callee.as_ref() == Some(&loop_id) && matches!(argument.as_deref(), Some("x" | "y")))
                .then_some(expression.occurrence.ordinal())).collect::<std::collections::HashSet<_>>();
        let mut observed_work_sources = std::collections::HashSet::new();
        let work_occurrences = work_bounds.iter().filter_map(|event| event.split_whitespace()
            .find_map(|part| part.strip_prefix("occurrence=").and_then(|value| value.parse::<usize>().ok())))
            .collect::<std::collections::HashSet<_>>();
        let trace_occurrence = |event: &str| event.split_whitespace().find_map(|part|
            part.strip_prefix("occurrence=").and_then(|value| value.parse::<usize>().ok()));
        for (index, event) in execution_trace.iter().enumerate().filter(|(_, event)| {
            event.starts_with("row-merge ") || event.starts_with("bound-transport ")
                || ((event.starts_with("extrusion-start ") || event.starts_with("extrusion-finish "))
                    && trace_occurrence(event).is_some_and(|occurrence| work_occurrences.contains(&occurrence)))
                || (event.starts_with("work-pop ")
                    && trace_occurrence(event).is_some_and(|occurrence| work_occurrences.contains(&occurrence)))
                || (event.starts_with("work-bound ")
                    && trace_occurrence(event).is_some_and(|occurrence| work_occurrences.contains(&occurrence)))
        }) {
            println!("R218 execution_event index={index} event={event}");
        }
        let solved = candidate.solved.data.candidate_graph.as_ref().unwrap();
        let context = &solved.intrusion.effect_algebra.context;
        let references = &candidate.solved.data.candidate_references;
        let loop_binding = local.bindings().iter().find(|binding| binding.id == loop_id).unwrap();
        let loop_lambda_ordinal = local.expression(&loop_binding.initializer).unwrap().occurrence.ordinal();
        let loop_slot4 = context.origins.iter().find(|origin|
            origin.occurrence.occurrence().ordinal() == loop_lambda_ordinal
                && origin.occurrence.local_slot() == 4)
            .expect("fixed source loop Lambda has its own slot-4 Origin");
        let slot4_source_bound = context.test_admission_emissions_for_relation(loop_slot4.relation).iter()
            .find_map(|(_, admission, _)| match admission.bound {
                crate::candidate_effect::BoundKey(
                    crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(_)),
                    Polarity::Negative,
                    crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(_)),
                ) => Some(admission.bound),
                _ => None,
            }).expect("slot-4 origin has its exact source effect bound");
        let crate::candidate_effect::BoundKey(
            crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(owner)),
            Polarity::Negative,
            crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(item)),
        ) = slot4_source_bound else { unreachable!() };
        let mut loop_q_route_seen = false;
        for event in &work_bounds {
            let occurrence = event.split_whitespace().find_map(|part|
                part.strip_prefix("occurrence=").and_then(|value| value.parse::<usize>().ok()));
            let Some(occurrence) = occurrence else { panic!("Work::Bound trace has no extrusion occurrence: {event}"); };
            let event_index = execution_trace.iter().position(|candidate| std::ptr::eq(candidate, *event)).unwrap();
            assert!(event_index > 0 && execution_trace[event_index - 1].starts_with(&format!("work-pop occurrence={occurrence} task=Bound(")),
                "every Work::Bound record follows the exact popped bound work item");
            for (group, group_occurrence, start, end, active) in solved.intrusion.observed_groups()
                .filter(|(_, group_occurrence, _, _, _)| *group_occurrence == occurrence)
            {
                let parents = solved.intrusion.parents[start..end].iter().enumerate()
                    .map(|(offset, parent)| (start + offset, parent.copy, parent.parent, parent.polarity,
                        parent.target, parent.comparison, parent.occurrence, parent.sources,
                        parent.sources.map(|sources| context.source_events(sources).iter()
                            .filter_map(|&event| references.observed_checking(event).cloned()).collect::<Vec<_>>())))
                    .collect::<Vec<_>>();
                for parent in &solved.intrusion.parents[start..end] {
                    if let Some(sources) = parent.sources {
                        observed_work_sources.extend(context.source_events(sources).iter()
                            .filter_map(|&event| references.observed_checking(event))
                            .map(|checking| checking.source_ordinal()));
                    }
                }
                println!("R218 work_bound_group occurrence={occurrence} group={group} active={active} parents={parents:?}");
            }
        }
        assert_eq!(observed_work_sources, expected_work_sources,
            "each selected Work::Bound family maps to the fixed source's direct or helper-body loop Apply");
        assert_eq!(work_bounds.len(), 2, "the full exact-source extrusion trace has only the two recorded Work::Bound events");
        let source_item_marker = format!("EffectRow({item})");
        assert!(work_bounds.iter().all(|event| !event.contains(&source_item_marker)),
            "neither production Work::Bound lookup selects the fixed source slot-4 item {source_item_marker}: {work_bounds:?}");
        assert!(solved.intrusion.forest_event_log_complete(), "the alias/merge history did not truncate");
        let forest_events = solved.intrusion.forest_events();
        assert!(forest_events.iter().all(|event| !matches!(event,
            crate::candidate_intrusion::ForestEvent::Birth(crate::candidate_scheme::RowKey::Effect(row))
                if *row == item)
            && !matches!(event,
                crate::candidate_intrusion::ForestEvent::ParentWrite { key: crate::candidate_scheme::RowKey::Effect(row), .. }
                    if *row == item)),
            "the exact source slot-4 item has no birth or parent-write in the complete intrusion forest: Effect({item})");
        let mut value_forest = Vec::<u32>::new();
        let mut effect_forest = Vec::<u32>::new();
        let mut source_alias_history = Vec::new();
        let apply_parent_write = |forest: &mut Vec<u32>, key: u32, before: u32, after: u32| {
            let slot = forest.get_mut(key as usize).expect("parent write follows row birth");
            assert_eq!(*slot, before, "forest event starts from its recorded previous parent");
            *slot = after;
        };
        let forest_root = |forest: &[u32], mut row: u32| {
            while forest[row as usize] != row { row = forest[row as usize]; }
            row
        };
        for (cursor, event) in forest_events.iter().enumerate() {
            match *event {
                crate::candidate_intrusion::ForestEvent::Birth(crate::candidate_scheme::RowKey::Value(row)) => {
                    assert_eq!(row as usize, value_forest.len()); value_forest.push(row);
                }
                crate::candidate_intrusion::ForestEvent::Birth(crate::candidate_scheme::RowKey::Effect(row)) => {
                    assert_eq!(row as usize, effect_forest.len()); effect_forest.push(row);
                }
                crate::candidate_intrusion::ForestEvent::ParentWrite { key: crate::candidate_scheme::RowKey::Value(row), before, after, .. } =>
                    apply_parent_write(&mut value_forest, row, before, after),
                crate::candidate_intrusion::ForestEvent::ParentWrite { key: crate::candidate_scheme::RowKey::Effect(row), before, after, .. } =>
                    apply_parent_write(&mut effect_forest, row, before, after),
                crate::candidate_intrusion::ForestEvent::Truncate { values_len, effects_len } => {
                    value_forest.truncate(values_len); effect_forest.truncate(effects_len);
                }
            }
            if effect_forest.len() > owner as usize && effect_forest.len() > item as usize {
                source_alias_history.push((cursor, forest_root(&effect_forest, owner), forest_root(&effect_forest, item)));
            }
        }
        let final_forest = solved.intrusion.forest_snapshot().unwrap();
        assert_eq!(value_forest, final_forest.values, "complete Value forest event replay matches final state");
        assert_eq!(effect_forest, final_forest.effects, "complete Effect forest event replay matches final state");
        let source_owner_rep = solved.intrusion.effect_rep(owner);
        let source_item_rep = solved.intrusion.effect_rep(item);
        assert_ne!(source_owner_rep, source_item_rep, "slot-4 owner and item remain separate at the final source boundary");
        assert!(source_alias_history.iter().all(|(_, owner_rep, item_rep)| owner_rep != item_rep),
            "where both rows enter the complete intrusion forest, they never merge: {source_alias_history:?}");
        println!("R218 forest_replay complete=true effect_rows={} source_owner=Effect({owner}) rep={source_owner_rep} source_item=Effect({item}) rep={source_item_rep} joint_alias_history={source_alias_history:?}", effect_forest.len());
        let mut complete_observations = 0usize;
        for (expression, callee, _, argument) in target_calls {
            let observed = match candidate.local_source_provider_observation(&expression.occurrence, 512) {
                Ok(observed) => observed,
                Err(error) => {
                    println!("R218 observation_unavailable occurrence={} callee={callee} argument={argument:?} error={error:?}", expression.occurrence.ordinal());
                    continue;
                }
            };
            println!("R218 call_observation occurrence={} callee={callee} argument={argument:?} complete=({}, {}) truncated={} routes={}",
                expression.occurrence.ordinal(), observed.facts_complete, observed.origins_complete,
                observed.captures_truncated, observed.routes.len());
            assert!(observed.facts_complete && observed.origins_complete);
            assert!(!observed.captures_truncated);
            complete_observations += 1;
            for route_observation in &observed.routes {
                let route = &solved.local_routes[route_observation.route];
                println!("R218 route occurrence={:?} local={:?} boundary={} root={} live_root={} rows={:?}",
                    route.occurrence, route.local, route.graph.boundary, route.graph.root,
                    route.graph.live_root, route.graph.rows);
                if callee == "loop" && argument.as_deref() == Some("q") {
                    loop_q_route_seen = true;
                    assert_eq!(route.local, loop_id, "the top-level loop q call uses the retained loop scheme");
                    let source_bound = route.graph.bounds.iter()
                        .find(|bound| bound.relation == Some(loop_slot4.relation))
                        .expect("loop q Local Capture contains the loop Lambda slot-4 bound").source_bound;
                    let crate::candidate_effect::BoundKey(
                        crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(owner)),
                        Polarity::Negative,
                        crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(item)),
                    ) = source_bound else { panic!("loop slot-4 bound is the expected negative owner-to-item edge: {source_bound:?}"); };
                    assert_eq!(source_bound, slot4_source_bound);
                    let owner_capture = route.graph.rows.iter().position(|row| row.key == crate::candidate_scheme::RowKey::Effect(owner)).unwrap();
                    let item_capture = route.graph.rows.iter().position(|row| row.key == crate::candidate_scheme::RowKey::Effect(item)).unwrap();
                    assert!(route.graph.capture_rows[owner_capture].local && route.graph.capture_rows[item_capture].local);
                    let mapped_effect = |index: usize| match route.rows[index] {
                        crate::candidate_scheme::RowKey::Effect(mapped) => mapped,
                        other => panic!("effect Capture row maps to an effect row, got {other:?}"),
                    };
                    let mapped_bound = crate::candidate_effect::BoundKey(
                        crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(mapped_effect(owner_capture))),
                        Polarity::Negative,
                        crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(mapped_effect(item_capture))),
                    );
                    let lineage = context.test_relation_lineage(loop_slot4.relation);
                    assert!(lineage.iter().any(|edge| edge.contains(&format!("from: {source_bound:?}"))
                        && edge.contains(&format!("to: {mapped_bound:?}"))
                        && edge.contains("reason: FreshUse")),
                        "loop slot-4 relation has the exact Local FreshUse image {mapped_bound:?}");
                    let physical = context.test_admission_emissions_for_relation(loop_slot4.relation);
                    assert!(physical.iter().any(|(_, admission, emissions)| admission.bound == source_bound
                        && emissions.iter().any(|(_, emission)| emission.physical.owner == crate::candidate_scheme::RowKey::Effect(owner)
                            && emission.physical.lane == crate::candidate_context::BoundLane::EffectUpperRow)),
                        "slot-4 source relation reads back from its owner row's upper lane");
                    println!("R218 loop_slot4 source={source_bound:?} owner=Effect({owner}) item=Effect({item}) local_fresh_use={mapped_bound:?} lineage_edges={}", lineage.len());
                }
                for bound in &route.graph.bounds {
                    if bound.kind == yu_types::ComponentKind::Effect {
                        println!("R218 effect_bound occurrence={} source={:?} relation={:?}",
                            expression.occurrence.ordinal(), bound.source_bound, bound.relation);
                        if let Some(relation) = bound.relation {
                            if context.origins.iter().any(|origin| origin.relation == relation && origin.occurrence.local_slot() == 4) {
                                println!("R218 lambda_slot4_lineage occurrence={} relation={relation:?} lineage={:?}",
                                    expression.occurrence.ordinal(), context.test_relation_lineage(relation));
                            }
                        }
                    }
                }
            }
        }
        assert!(complete_observations > 0, "at least one exact local source route has complete observation");
        assert!(loop_q_route_seen, "the exact outer loop q call has a complete source route");
        println!("R218 complete_observations={complete_observations} total_calls=4");
    }

    #[test]
    fn r219_repeated_loop_q_source_reachability() {
        const SOURCE: &str = r#"act io:
    our tick: int -> int

my outer (q:[io] int) = {
    my loop (x:[io] int) = {
        my direct = loop x
        my helper (y:[io] int) = loop y
        helper x
    }
    my repeated (z:[io] int) = {
        my first = loop z
        loop z
    }
    repeated q
}"#;
        let source: Arc<SourceText> = Arc::from(SOURCE);
        let parsed = parse_file(source.clone(), Arc::new(scan_header(source)), Arc::new(SyntaxEnvironment::empty()));
        assert!(parsed.structural_recoveries().is_empty());
        let hir = Arc::new(lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new("r219-repeat-loop-q", "source.yu"))),
            &parsed, SemanticImports::empty(),
        ).unwrap());
        let outer = binding(&hir, "outer");
        let local = hir.local_source(outer.definition_root()).unwrap().unwrap();
        let local_id = |name: &str| local.bindings().iter()
            .find(|binding| binding.spelling.as_ref() == name).unwrap().id.clone();
        let loop_id = local_id("loop");
        let repeated_loop_occurrences = local.expressions().iter().filter_map(|expression| {
            let LocalSourceForm::Apply { callee, argument, .. } = &expression.form else { return None; };
            let (LocalSourceForm::Name { resolution: LocalSourceResolution::Local(callee), .. },
                 LocalSourceForm::Name { spelling, .. }) =
                (&local.expression(callee).unwrap().form, &local.expression(argument).unwrap().form) else { return None; };
            (*callee == loop_id && spelling.as_ref() == "z").then_some(expression.occurrence.ordinal())
        }).collect::<Vec<_>>();
        assert_eq!(repeated_loop_occurrences.len(), 2, "the exact repeated function body has two loop z applications");

        crate::candidate_context::r148_trace_begin();
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        let trace = crate::candidate_context::r148_trace_finish();
        assert!(candidate.solved.data.errors.is_empty(), "the exact ordinary source is admitted");
        let starts = trace.iter().filter(|event| event.starts_with("extrusion-start ")).count();
        let finishes = trace.iter().filter(|event| event.starts_with("extrusion-finish ")).count();
        assert!(starts > 0 && starts == finishes);
        let work_bounds = trace.iter().filter(|event| event.starts_with("work-bound ")).collect::<Vec<_>>();
        let work_occurrences = work_bounds.iter().filter_map(|event| event.split_whitespace()
            .find_map(|part| part.strip_prefix("occurrence=").and_then(|value| value.parse::<usize>().ok())))
            .collect::<std::collections::HashSet<_>>();
        for event in &work_bounds {
            let occurrence = event.split_whitespace().find_map(|part|
                part.strip_prefix("occurrence=").and_then(|value| value.parse::<usize>().ok())).unwrap();
            let index = trace.iter().position(|candidate| std::ptr::eq(candidate, *event)).unwrap();
            assert!(index > 0 && trace[index - 1].starts_with(&format!("work-pop occurrence={occurrence} task=Bound(")));
        }
        let solved = candidate.solved.data.candidate_graph.as_ref().unwrap();
        let context = &solved.intrusion.effect_algebra.context;
        let references = &candidate.solved.data.candidate_references;
        for source_occurrence in &repeated_loop_occurrences {
            let expression = local.expressions().iter().find(|expression|
                expression.occurrence.ordinal() == *source_occurrence).unwrap();
            match candidate.local_source_provider_observation(&expression.occurrence, 4096) {
                Ok(observation) => println!("R219 local_observation occurrence={source_occurrence} complete=({}, {}) truncated={} routes={}",
                    observation.facts_complete, observation.origins_complete,
                    observation.captures_truncated, observation.routes.len()),
                Err(error) => println!("R219 local_observation_unavailable occurrence={source_occurrence} error={error:?}"),
            }
        }
        let loop_initializer = local.bindings().iter().find(|binding| binding.id == loop_id).unwrap().initializer.clone();
        let loop_ordinal = local.expression(&loop_initializer).unwrap().occurrence.ordinal();
        let slot4 = context.origins.iter().find(|origin|
            origin.occurrence.occurrence().ordinal() == loop_ordinal && origin.occurrence.local_slot() == 4)
            .expect("loop Lambda slot-4 source origin");
        let slot4_bound = context.test_admission_emissions_for_relation(slot4.relation).iter()
            .find_map(|(_, admission, emissions)| matches!(admission.bound,
                crate::candidate_effect::BoundKey(
                    crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(_)),
                    Polarity::Negative,
                    crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(_))))
                .then_some((admission.bound, emissions.to_vec())))
            .expect("slot-4 physical source bound");
        let (source_bound, emissions) = slot4_bound;
        let crate::candidate_effect::BoundKey(
            crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(owner)),
            Polarity::Negative,
            crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(item)),
        ) = source_bound else { unreachable!() };
        assert!(emissions.iter().any(|(_, emission)|
            emission.physical.owner == crate::candidate_scheme::RowKey::Effect(owner)
                && emission.physical.lane == crate::candidate_context::BoundLane::EffectUpperRow));

        let intrusion = &solved.intrusion;
        assert!(intrusion.forest_event_log_complete());
        let mut values = Vec::<u32>::new();
        let mut effects = Vec::<u32>::new();
        let mut item_events = Vec::new();
        for (index, event) in intrusion.forest_events().iter().enumerate() {
            match *event {
                crate::candidate_intrusion::ForestEvent::Birth(crate::candidate_scheme::RowKey::Value(row)) => {
                    assert_eq!(row as usize, values.len()); values.push(row);
                }
                crate::candidate_intrusion::ForestEvent::Birth(crate::candidate_scheme::RowKey::Effect(row)) => {
                    assert_eq!(row as usize, effects.len()); effects.push(row);
                    if row == item { item_events.push((index, "birth", row)); }
                }
                crate::candidate_intrusion::ForestEvent::ParentWrite { key: crate::candidate_scheme::RowKey::Value(row), before, after, .. } => {
                    let slot = &mut values[row as usize]; assert_eq!(*slot, before); *slot = after;
                }
                crate::candidate_intrusion::ForestEvent::ParentWrite { key: crate::candidate_scheme::RowKey::Effect(row), before, after, .. } => {
                    let slot = &mut effects[row as usize]; assert_eq!(*slot, before); *slot = after;
                    if row == item { item_events.push((index, "parent-write", row)); }
                }
                crate::candidate_intrusion::ForestEvent::Truncate { values_len, effects_len } => {
                    values.truncate(values_len); effects.truncate(effects_len);
                }
            }
        }
        let final_forest = intrusion.forest_snapshot().unwrap();
        assert_eq!(values, final_forest.values);
        assert_eq!(effects, final_forest.effects);
        let bound_mentions = work_bounds.iter().filter(|event| event.contains(&format!("EffectRow({item})"))).count();
        let source_checking = solved.intrusion.observed_groups().flat_map(|(_, occurrence, start, end, _)| {
            if !work_occurrences.contains(&occurrence) { return Vec::new(); }
            solved.intrusion.parents[start..end].iter().filter_map(|parent| parent.sources)
                .flat_map(|sources| context.source_events(sources).iter()
                    .filter_map(|&event| references.observed_checking(event))
                    .map(|checking| checking.source_ordinal()).collect::<Vec<_>>()).collect::<Vec<_>>()
        }).collect::<std::collections::HashSet<_>>();
        assert_eq!(work_bounds.len(), 2, "the complete source trace has only the two Work::Bound events");
        let repeated_checks = repeated_loop_occurrences.iter().copied().collect::<std::collections::HashSet<_>>();
        assert!(source_checking.is_disjoint(&repeated_checks),
            "neither repeated loop z Apply owns a Work::Bound group: source checks={source_checking:?}, calls={repeated_loop_occurrences:?}");
        assert!(item_events.is_empty(), "the slot-4 item has no birth or parent write in the complete forest: {item_events:?}");
        assert_eq!(bound_mentions, 0, "no later Work::Bound selects the slot-4 item");
        println!("R219 source repeated_loop={repeated_loop_occurrences:?} work_bounds={work_bounds:?} source_checks={source_checking:?} slot4={source_bound:?} physical=Effect({owner})/EffectUpperRow[0] item=Effect({item}) item_forest_events={item_events:?} item_work_bound_mentions={bound_mentions} forest_effect_rows={}", effects.len());
    }

    #[test]
    fn r220_repeated_loop_local_fresh_use_bound_lineage() {
        const SOURCE: &str = r#"act io:
    our tick: int -> int

my outer (q:[io] int) = {
    my loop (x:[io] int) = {
        my direct = loop x
        my helper (y:[io] int) = loop y
        helper x
    }
    my repeated (z:[io] int) = {
        my first = loop z
        loop z
    }
    repeated q
}"#;
        let source: Arc<SourceText> = Arc::from(SOURCE);
        let parsed = parse_file(source.clone(), Arc::new(scan_header(source)), Arc::new(SyntaxEnvironment::empty()));
        assert!(parsed.structural_recoveries().is_empty());
        let hir = Arc::new(lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new("r220-repeat-loop-fresh-use", "source.yu"))),
            &parsed, SemanticImports::empty(),
        ).unwrap());
        let outer = binding(&hir, "outer");
        let local = hir.local_source(outer.definition_root()).unwrap().unwrap();
        let loop_id = local.bindings().iter().find(|binding| binding.spelling.as_ref() == "loop").unwrap().id.clone();
        let applies = local.expressions().iter().filter(|expression| {
            let LocalSourceForm::Apply { callee, argument, .. } = &expression.form else { return false; };
            matches!((&local.expression(callee).unwrap().form, &local.expression(argument).unwrap().form),
                (LocalSourceForm::Name { resolution: LocalSourceResolution::Local(id), .. },
                 LocalSourceForm::Name { spelling, .. }) if *id == loop_id && spelling.as_ref() == "z")
        }).collect::<Vec<_>>();
        assert_eq!(applies.len(), 2);

        crate::candidate_context::r148_trace_begin();
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        let trace = crate::candidate_context::r148_trace_finish();
        assert!(candidate.solved.data.errors.is_empty());
        let solved = candidate.solved.data.candidate_graph.as_ref().unwrap();
        let context = &solved.intrusion.effect_algebra.context;
        let loop_initializer = local.bindings().iter().find(|binding| binding.id == loop_id).unwrap().initializer.clone();
        let loop_ordinal = local.expression(&loop_initializer).unwrap().occurrence.ordinal();
        let slot4 = context.origins.iter().find(|origin|
            origin.occurrence.occurrence().ordinal() == loop_ordinal && origin.occurrence.local_slot() == 4)
            .expect("loop Lambda slot-4 origin");
        let source_bound = context.test_admission_emissions_for_relation(slot4.relation).iter()
            .find_map(|(_, admission, _)| matches!(admission.bound,
                crate::candidate_effect::BoundKey(
                    crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(_)),
                    Polarity::Negative,
                    crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(_))))
                .then_some(admission.bound)).unwrap();
        let crate::candidate_effect::BoundKey(
            crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(owner)), Polarity::Negative,
            crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(item)),
        ) = source_bound else { unreachable!() };
        let mut mapped_bounds = Vec::new();
        for expression in &applies {
            let observation = candidate.local_source_provider_observation(&expression.occurrence, 4096).unwrap();
            assert!(observation.facts_complete && observation.origins_complete);
            assert!(observation.captures_truncated, "the source capture observer's row list is truncated");
            assert_eq!(observation.routes.len(), 1);
            let route_observation = &observation.routes[0];
            let route = &solved.local_routes[route_observation.route];
            let bound = route.graph.bounds.iter().find(|bound| bound.relation == Some(slot4.relation))
                .expect("the repeated-loop Local route contains the exact slot-4 source relation");
            assert_eq!(bound.source_bound, source_bound);
            let owner_capture = route.graph.rows.iter().position(|row| row.key == crate::candidate_scheme::RowKey::Effect(owner)).unwrap();
            let item_capture = route.graph.rows.iter().position(|row| row.key == crate::candidate_scheme::RowKey::Effect(item)).unwrap();
            let mapped_effect = |index: usize| match route.rows[index] {
                crate::candidate_scheme::RowKey::Effect(mapped) => mapped,
                other => panic!("effect Capture row maps to an effect row, got {other:?}"),
            };
            let mapped = crate::candidate_effect::BoundKey(
                crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(mapped_effect(owner_capture))),
                Polarity::Negative,
                crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(mapped_effect(item_capture))),
            );
            let lineage = context.test_relation_lineage(slot4.relation);
            assert!(lineage.iter().any(|edge| edge.contains(&format!("from: {source_bound:?}"))
                && edge.contains(&format!("to: {mapped:?}")) && edge.contains("reason: FreshUse")));
            mapped_bounds.push((expression.occurrence.ordinal(), mapped, lineage.len()));
        }
        let work_bounds = trace.iter().filter(|event| event.starts_with("work-bound ")).collect::<Vec<_>>();
        assert_eq!(work_bounds.len(), 2);
        assert!(work_bounds.iter().all(|event| !event.contains(&format!("EffectRow({item})"))));
        assert!(solved.intrusion.forest_event_log_complete());
        let mapped_items = mapped_bounds.iter().map(|(_, bound, _)| match bound {
            crate::candidate_effect::BoundKey(_, _, crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(item))) => *item,
            other => panic!("mapped FreshUse image has an effect item: {other:?}"),
        }).collect::<Vec<_>>();
        for mapped_item in &mapped_items {
            assert!(work_bounds.iter().all(|event| !event.contains(&format!("EffectRow({mapped_item})"))),
                "no later Work::Bound selects this Local FreshUse image item: Effect({mapped_item})");
        }
        assert!(!solved.intrusion.forest_events().iter().any(|event| matches!(event,
            crate::candidate_intrusion::ForestEvent::Birth(crate::candidate_scheme::RowKey::Effect(row)) if *row == item)
            || matches!(event,
                crate::candidate_intrusion::ForestEvent::ParentWrite { key: crate::candidate_scheme::RowKey::Effect(row), .. } if *row == item)));
        assert!(mapped_items.iter().all(|mapped_item| !solved.intrusion.forest_events().iter().any(|event| matches!(event,
            crate::candidate_intrusion::ForestEvent::Birth(crate::candidate_scheme::RowKey::Effect(row)) if row == mapped_item)
            || matches!(event,
                crate::candidate_intrusion::ForestEvent::ParentWrite { key: crate::candidate_scheme::RowKey::Effect(row), .. } if row == mapped_item))));
        println!("R220 source_bound={source_bound:?} physical_owner=Effect({owner}) item=Effect({item}) repeated_local_fresh_uses={mapped_bounds:?} work_bounds={work_bounds:?} forest_complete=true item_in_forest=false");
    }

    #[test]
    fn r222_higher_order_provider_formal_bridge() {
        const SOURCE: &str = r#"act io:
    our tick: int -> int

my outer (q:[io] int) = {
    my loop (x:[io] int) = {
        my direct = loop x
        my helper (y:[io] int) = loop y
        helper x
    }
    my repeat (f:[io] int -> int) (z:[io] int) = {
        my first = f z
        f z
    }
    repeat loop q
}"#;
        let source: Arc<SourceText> = Arc::from(SOURCE);
        let parsed = parse_file(source.clone(), Arc::new(scan_header(source)), Arc::new(SyntaxEnvironment::empty()));
        assert!(parsed.structural_recoveries().is_empty());
        let hir = Arc::new(lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new("r222-provider-formal", "source.yu"))),
            &parsed, SemanticImports::empty(),
        ).unwrap());
        let candidate = CandidateInference::solve(hir).unwrap();
        assert!(candidate.solved.data.errors.is_empty());
        assert!(candidate.candidate_conflicts().is_empty());
        let callback_call = (0..candidate.source_call_count()).map(|index| candidate.source_call(index).unwrap())
            .find(|call| call.checking_occurrence().occurrence().ordinal() == 19).unwrap();
        let provider_call = (0..candidate.source_call_count()).map(|index| candidate.source_call(index).unwrap())
            .find(|call| call.checking_occurrence().occurrence().ordinal() == 26).unwrap();
        assert_eq!(callback_call.formal_registration().unwrap().spelling.as_ref(), "f");
        assert!(provider_call.formal_registration().is_none());
        assert_eq!(callback_call.native_registered_root().unwrap(), callback_call.native_callee());
        let callback_formal_use = candidate.fresh_use(&callback_call.callee_source().occurrence);
        let actual_loop_use = candidate.fresh_use(&provider_call.argument_source().occurrence);
        let repeat_callee_use = candidate.fresh_use(&provider_call.callee_source().occurrence);
        assert!(callback_formal_use.is_none());
        assert_eq!(actual_loop_use.as_ref().unwrap().rows().count(), 20);
        assert_eq!(repeat_callee_use.as_ref().unwrap().rows().count(), 16);

        let provider_term = provider_call.native_argument();
        let formal_term = callback_call.native_callee();
        let mut edges = std::collections::HashMap::<Term, Vec<Term>>::new();
        let mut pending = Vec::new();
        for fact in candidate.solved.data.store.facts() {
            edges.entry(fact.lower()).or_default().push(fact.upper());
            edges.entry(fact.upper()).or_default().push(fact.lower());
            pending.extend([fact.lower(), fact.upper()]);
        }
        pending.extend([provider_term, formal_term]);
        let mut seen = std::collections::HashSet::new();
        while let Some(term) = pending.pop() {
            if !seen.insert(term) { continue; }
            let children = match candidate.solved.data.store.term_view(term).unwrap() {
                crate::TermView::PositiveFunction { argument, argument_effect, result_effect, result }
                | crate::TermView::NegativeFunction { argument, argument_effect, result_effect, result } =>
                    [argument, argument_effect, result_effect, result],
                _ => continue,
            };
            for child in children {
                edges.entry(term).or_default().push(child);
                edges.entry(child).or_default().push(term);
                pending.push(child);
            }
        }
        let mut search = std::collections::VecDeque::from([provider_term]);
        let mut reachable = std::collections::HashSet::from([provider_term]);
        while let Some(term) = search.pop_front() {
            for &next in edges.get(&term).into_iter().flatten() {
                if reachable.insert(next) { search.push_back(next); }
            }
        }
        assert!(!reachable.contains(&formal_term));
        println!("R222 provider_occurrence=26 callback_apply=19 formal_use_available=false provider_formal_registration=false provider_native={:?} callback_native={:?} fact_and_function_path=false",
            candidate.solved.data.store.term_view(provider_term), candidate.solved.data.store.term_view(formal_term));
    }

    #[test]
    fn r223_local_apply_provider_route_rows() {
        const SOURCE: &str = r#"act io:
    our tick: int -> int

my outer (q:[io] int) = {
    my loop (x:[io] int) = {
        my direct = loop x
        my helper (y:[io] int) = loop y
        helper x
    }
    my repeat (f:[io] int -> int) (z:[io] int) = {
        my first = f z
        f z
    }
    repeat loop q
}"#;
        let source: Arc<SourceText> = Arc::from(SOURCE);
        let parsed = parse_file(source.clone(), Arc::new(scan_header(source)), Arc::new(SyntaxEnvironment::empty()));
        let hir = Arc::new(lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new("r223-provider-route", "source.yu"))),
            &parsed, SemanticImports::empty(),
        ).unwrap());
        let outer = binding(&hir, "outer");
        let local = hir.local_source(outer.definition_root()).unwrap().unwrap();
        let loop_id = local.bindings().iter().find(|binding| binding.spelling.as_ref() == "loop").unwrap().id.clone();
        let repeat_id = local.bindings().iter().find(|binding| binding.spelling.as_ref() == "repeat").unwrap().id.clone();
        let candidate = CandidateInference::solve(hir).unwrap();
        assert!(candidate.solved.data.errors.is_empty());
        assert!(candidate.candidate_conflicts().is_empty());
        let solved = candidate.solved.data.candidate_graph.as_ref().unwrap();
        let actual_loop = solved.local_routes.iter().find(|route|
            route.occurrence.ordinal() == 28 && route.local == loop_id).expect("actual loop Name LocalFreshRoute");
        let repeat = solved.local_routes.iter().find(|route|
            route.occurrence.ordinal() == 27 && route.local == repeat_id).expect("repeat callee Name LocalFreshRoute");
        assert!(actual_loop.authentic_use_instance());
        assert!(repeat.authentic_use_instance());
        let describe = |route: &crate::candidate_scheme::LocalFreshRoute| {
            route.graph.rows.iter().zip(&route.rows).map(|(source, image)| (source.key, *image)).collect::<Vec<_>>()
        };
        let actual_rows = describe(actual_loop);
        let repeat_rows = describe(repeat);
        let actual_slot4 = actual_loop.graph.rows.iter().position(|row| row.key == crate::candidate_scheme::RowKey::Effect(41))
            .map(|index| actual_loop.rows[index]);
        let repeat_formal_item = repeat.graph.rows.iter().position(|row| row.key == crate::candidate_scheme::RowKey::Effect(31))
            .map(|index| repeat.rows[index]);
        assert_eq!(actual_slot4, Some(crate::candidate_scheme::RowKey::Effect(69)));
        assert_eq!(repeat_formal_item, Some(crate::candidate_scheme::RowKey::Effect(57)));
        let actual_bounds = actual_loop.graph.bounds.iter().filter(|bound| {
            matches!(bound.source_bound,
                crate::candidate_effect::BoundKey(
                    crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(41)), _, _)
                | crate::candidate_effect::BoundKey(
                    crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(_)), _,
                    crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(41))))
        }).map(|bound| (bound.source_bound, bound.relation)).collect::<Vec<_>>();
        let repeat_bounds = repeat.graph.bounds.iter().filter(|bound| {
            matches!(bound.source_bound,
                crate::candidate_effect::BoundKey(
                    crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(31)), _, _)
                | crate::candidate_effect::BoundKey(
                    crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(_)), _,
                    crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(31))))
        }).map(|bound| (bound.source_bound, bound.relation)).collect::<Vec<_>>();
        println!("R223 actual_loop_occurrence=28 rows={actual_rows:?} slot4_item_image={actual_slot4:?} bounds={actual_bounds:?}");
        println!("R223 repeat_callee_occurrence=27 rows={repeat_rows:?} callback_item_image={repeat_formal_item:?} bounds={repeat_bounds:?}");
        println!("R223 roots actual_loop={:?} repeat={:?} node_counts=({}, {})",
            actual_loop.graph.nodes[actual_loop.graph.root], repeat.graph.nodes[repeat.graph.root],
            actual_loop.graph.nodes.len(), repeat.graph.nodes.len());
        println!("R223 graph_intrusion_effect_rows={}", solved.intrusion.forest_snapshot().unwrap().effects.len());
        println!("R223 mapped_route_effect_representatives actual_slot4={} repeat_formal={}",
            solved.intrusion.effect_rep(69), solved.intrusion.effect_rep(57));
        let actual_use = candidate.fresh_use(&actual_loop.occurrence).unwrap();
        let slot4_source_row = actual_loop.graph.rows.iter().find(|row| row.key == crate::candidate_scheme::RowKey::Effect(41)).unwrap();
        let slot4_fresh_row = actual_use.rows().find(|row| row.source_row().same_identity(crate::shadow_apply::CandidateGraphRow {
            state: solved, graph: &actual_loop.graph, index: actual_loop.graph.rows.iter().position(|candidate_row|
                std::ptr::eq(candidate_row, slot4_source_row)).unwrap(),
        })).unwrap();
        let mapped_identity_self_check = std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
            slot4_fresh_row.same_identity(&slot4_fresh_row)));
        println!("R223 mapped_fresh_row_identity_self_check={:?}", mapped_identity_self_check);
        let function_ports = |route: &crate::candidate_scheme::LocalFreshRoute| {
            route.graph.nodes.iter().enumerate().filter_map(|(index, node)| {
                let crate::candidate_scheme::Node::Function { polarity, children } = node else { return None; };
                let ports = children.map(|child| match route.graph.nodes[child] {
                    crate::candidate_scheme::Node::Row { row, polarity } => Some((route.graph.rows[row].key, polarity)),
                    _ => None,
                });
                Some((index, *polarity, ports))
            }).collect::<Vec<_>>()
        };
        let provider_apply = candidate.solved.data.candidate_calls.calls.iter().find(|call|
            call.checking.occurrence().ordinal() == 26).unwrap();
        let provider_apply_index = candidate.solved.data.candidate_calls.calls.iter().position(|call|
            call.checking.occurrence().ordinal() == 26).unwrap();
        println!("R223 apply_constructor local_callee={:?} formal_name={:?} argument_endpoint={:?} native={:?}",
            provider_apply.local_callee, provider_apply.formal_name, provider_apply.argument_value, provider_apply.native);
        assert!(provider_apply.local_callee.is_none());
        assert!(provider_apply.formal_name.is_none());
        println!("R223 actual_loop_function_ports={:?}", function_ports(actual_loop));
        println!("R223 repeat_function_ports={:?}", function_ports(repeat));
        let context = &solved.intrusion.effect_algebra.context;
        let provider_replay_rows = context.replay_demand_rows().filter(|row| row.call == provider_apply_index).collect::<Vec<_>>();
        println!("R223 provider_replay_rows={provider_replay_rows:?}");
        assert!(provider_replay_rows.is_empty());
        for replay in provider_replay_rows {
            println!("R223 replay_lineage lower={:?} child={:?} upper={:?}",
                context.test_relation_lineage(replay.lower), context.test_relation_lineage(replay.child),
                context.test_relation_lineage(replay.upper));
            let port_edges = context.observed_dependencies().filter_map(|dependency| {
                let crate::candidate_context::Dependency::FunctionPort { child, parent, field, operation } = *dependency else { return None; };
                (parent == replay.child).then_some((child, parent, field, operation,
                    context.relation_pair(child), context.test_relation_lineage(child)))
            }).collect::<Vec<_>>();
            println!("R223 replay_function_port_edges={port_edges:?}");
        }
    }

    #[test]
    fn r221_higher_order_loop_callback_reachability() {
        const SOURCE: &str = r#"act io:
    our tick: int -> int

my outer (q:[io] int) = {
    my loop (x:[io] int) = {
        my direct = loop x
        my helper (y:[io] int) = loop y
        helper x
    }
    my repeat (f:[io] int -> int) (z:[io] int) = {
        my first = f z
        f z
    }
    repeat loop q
}"#;
        let source: Arc<SourceText> = Arc::from(SOURCE);
        let parsed = parse_file(source.clone(), Arc::new(scan_header(source)), Arc::new(SyntaxEnvironment::empty()));
        assert!(parsed.structural_recoveries().is_empty());
        let hir = Arc::new(lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new("r221-higher-order-loop", "source.yu"))),
            &parsed, SemanticImports::empty(),
        ).unwrap());
        let outer = binding(&hir, "outer");
        let local = hir.local_source(outer.definition_root()).unwrap().unwrap();
        let loop_id = local.bindings().iter().find(|binding| binding.spelling.as_ref() == "loop").unwrap().id.clone();
        let callback_applies = local.expressions().iter().filter(|expression| {
            let LocalSourceForm::Apply { callee, argument, .. } = &expression.form else { return false; };
            matches!((&local.expression(callee).unwrap().form, &local.expression(argument).unwrap().form),
                (LocalSourceForm::Name { spelling, .. }, LocalSourceForm::Name { spelling: argument, .. })
                    if spelling.as_ref() == "f" && argument.as_ref() == "z")
        }).map(|expression| expression.occurrence.ordinal()).collect::<Vec<_>>();
        assert_eq!(callback_applies.len(), 2, "the fixed callback body has exactly two f z calls");

        crate::candidate_context::r148_trace_begin();
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        let trace = crate::candidate_context::r148_trace_finish();
        assert!(candidate.solved.data.errors.is_empty(), "the exact ordinary source is admitted");
        assert!(candidate.candidate_conflicts().is_empty(), "the exact higher-order source has no ordinary candidate conflicts");
        let callback_apply = callback_applies.iter().copied().min().unwrap();
        let callback_call_index = (0..candidate.source_call_count()).find(|&index| {
            candidate.source_call(index).unwrap().checking_occurrence().occurrence().ordinal() == callback_apply
        }).expect("source Call for the first callback f z Apply");
        let callback_call = candidate.source_call(callback_call_index).unwrap();
        assert!(matches!(&callback_call.callee_source().form,
            LocalSourceForm::Name { spelling, .. } if spelling.as_ref() == "f"));
        assert_eq!(callback_call.formal_registration().unwrap().spelling.as_ref(), "f");
        assert!(matches!(&callback_call.argument_source().form,
            LocalSourceForm::Name { spelling, .. } if spelling.as_ref() == "z"));
        let provider_call_index = (0..candidate.source_call_count()).find(|&index| {
            let call = candidate.source_call(index).unwrap();
            matches!((&call.callee_source().form, &call.argument_source().form),
                (LocalSourceForm::Name { spelling: callee, .. }, LocalSourceForm::Name { spelling: argument, .. })
                    if callee.as_ref() == "repeat" && argument.as_ref() == "loop")
        }).expect("source Call passing the retained loop as repeat's callback argument");
        let provider_call = candidate.source_call(provider_call_index).unwrap();
        println!("R221 provider_call occurrence={} callee=repeat actual=loop formal_registration={:?}",
            provider_call.checking_occurrence().occurrence().ordinal(),
            provider_call.formal_registration().map(|formal| formal.spelling.as_ref()));
        let starts = trace.iter().filter(|event| event.starts_with("extrusion-start ")).count();
        let finishes = trace.iter().filter(|event| event.starts_with("extrusion-finish ")).count();
        assert!(starts > 0 && starts == finishes);
        let work_bounds = trace.iter().filter(|event| event.starts_with("work-bound ")).collect::<Vec<_>>();
        for (index, event) in trace.iter().enumerate().filter(|(_, event)|
            event.starts_with("work-bound ") || event.starts_with("row-merge ")
                || (event.starts_with("bound-transport ") && (event.contains("EffectRow(31)") || event.contains("EffectRow(41)")))) {
            println!("R221 alias_consumer_event index={index} {event}");
        }
        for event in &work_bounds {
            let occurrence = event.split_whitespace().find_map(|part|
                part.strip_prefix("occurrence=").and_then(|value| value.parse::<usize>().ok())).unwrap();
            let index = trace.iter().position(|candidate| std::ptr::eq(candidate, *event)).unwrap();
            assert!(index > 0 && trace[index - 1].starts_with(&format!("work-pop occurrence={occurrence} task=Bound(")));
        }
        let solved = candidate.solved.data.candidate_graph.as_ref().unwrap();
        let context = &solved.intrusion.effect_algebra.context;
        let references = &candidate.solved.data.candidate_references;
        let callback_work_event = work_bounds.iter().find(|event|
            event.contains("raw=BoundKey(Effect(EffectRow(21)), Positive, Effect(EffectRow(31)))"))
            .expect("callback formal Work::Bound lookup");
        let callback_work_occurrence = callback_work_event.split_whitespace().find_map(|part|
            part.strip_prefix("occurrence=").and_then(|value| value.parse::<usize>().ok())).unwrap();
        let callback_start = trace.iter().find(|event| event.starts_with(&format!("extrusion-start occurrence={callback_work_occurrence} ")))
            .expect("callback Work::Bound extrusion start");
        let processing_relation = callback_start.split("processing=Some(RelationId(").nth(1)
            .and_then(|rest| rest.split(')').next()).and_then(|id| id.parse::<u32>().ok()).unwrap();
        let callback_lineage = context.test_relation_lineage(crate::candidate_context::RelationId(processing_relation));
        println!("R221 callback_consumer occurrence={callback_work_occurrence} source_apply={} processing_relation=RelationId({processing_relation}) lineage={callback_lineage:?}", callback_applies.iter().copied().min().unwrap());
        let loop_initializer = local.bindings().iter().find(|binding| binding.id == loop_id).unwrap().initializer.clone();
        let loop_ordinal = local.expression(&loop_initializer).unwrap().occurrence.ordinal();
        let slot4 = context.origins.iter().find(|origin|
            origin.occurrence.occurrence().ordinal() == loop_ordinal && origin.occurrence.local_slot() == 4)
            .expect("loop Lambda slot-4 origin");
        let source_bound = context.test_admission_emissions_for_relation(slot4.relation).iter()
            .find_map(|(_, admission, _)| matches!(admission.bound,
                crate::candidate_effect::BoundKey(
                    crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(_)), Polarity::Negative,
                    crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(_))))
                .then_some(admission.bound)).unwrap();
        let crate::candidate_effect::BoundKey(
            crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(owner)), Polarity::Negative,
            crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(item)),
        ) = source_bound else { unreachable!() };
        let repeat_id = local.bindings().iter().find(|binding| binding.spelling.as_ref() == "repeat").unwrap().id.clone();
        let repeat_route = solved.local_routes.iter().find(|route|
            route.occurrence.ordinal() == 27 && route.local == repeat_id).expect("repeat loop Local route");
        let repeat_item_index = repeat_route.graph.rows.iter().position(|row|
            row.key == crate::candidate_scheme::RowKey::Effect(31)).expect("callback formal's retained item row");
        let repeat_item_image = match repeat_route.rows[repeat_item_index] {
            crate::candidate_scheme::RowKey::Effect(row) => row,
            other => panic!("callback item route maps to an effect row: {other:?}"),
        };
        let loop_route = solved.local_routes.iter().find(|route|
            route.graph.bounds.iter().any(|bound| bound.relation == Some(slot4.relation)))
            .expect("loop slot-4 Local route");
        let slot4_route_bound = loop_route.graph.bounds.iter().find(|bound| bound.relation == Some(slot4.relation)).unwrap();
        assert_eq!(slot4_route_bound.source_bound, source_bound);
        let route_effect_image = |source_row: u32| {
            let index = loop_route.graph.rows.iter().position(|row|
                row.key == crate::candidate_scheme::RowKey::Effect(source_row)).unwrap();
            match loop_route.rows[index] {
                crate::candidate_scheme::RowKey::Effect(row) => row,
                other => panic!("slot-4 Local row maps to an effect row: {other:?}"),
            }
        };
        let loop_owner_image = route_effect_image(owner);
        let loop_item_image = route_effect_image(item);
        let slot4_image = crate::candidate_effect::BoundKey(
            crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(loop_owner_image)), Polarity::Negative,
            crate::ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(loop_item_image)),
        );
        let slot4_lineage = context.test_relation_lineage(slot4.relation);
        assert!(slot4_lineage.iter().any(|edge| edge.contains(&format!("from: {source_bound:?}"))
            && edge.contains(&format!("to: {slot4_image:?}")) && edge.contains("reason: FreshUse")));
        assert!(work_bounds.iter().any(|event| event.contains("raw=BoundKey(Effect(EffectRow(21)), Positive, Effect(EffectRow(31)))")),
            "the callback's production lookup selects its own formal item Effect(31)");
        assert_ne!(repeat_item_image, loop_item_image,
            "the callback formal's Local image and loop slot-4 item have distinct source-qualified rows");
        let slot4_lineage = context.test_relation_lineage(slot4.relation);
        assert!(slot4_lineage.iter().any(|edge| edge.contains(&format!("from: {source_bound:?}"))
            && edge.contains(&format!("to: {slot4_image:?}")) && edge.contains("reason: FreshUse")));
        let mut source_checks = std::collections::HashSet::new();
        let mut work_occurrences = std::collections::HashSet::new();
        for event in &work_bounds {
            if let Some(occurrence) = event.split_whitespace().find_map(|part|
                part.strip_prefix("occurrence=").and_then(|value| value.parse::<usize>().ok())) {
                work_occurrences.insert(occurrence);
                for (_, group_occurrence, start, end, _) in solved.intrusion.observed_groups()
                    .filter(|(_, group_occurrence, _, _, _)| *group_occurrence == occurrence)
                {
                    for parent in &solved.intrusion.parents[start..end] {
                        if let Some(sources) = parent.sources {
                            source_checks.extend(context.source_events(sources).iter()
                                .filter_map(|&event| references.observed_checking(event))
                                .map(|checking| checking.source_ordinal()));
                        }
                    }
                }
            }
        }
        let callback_apply = callback_applies.iter().copied().min().unwrap();
        let callback_work_bound = work_bounds.iter().find(|event|
            event.contains("raw=BoundKey(Effect(EffectRow(21)), Positive, Effect(EffectRow(31)))"))
            .expect("callback formal Work::Bound consumer");
        let callback_work_occurrence = callback_work_bound.split_whitespace().find_map(|part|
            part.strip_prefix("occurrence=").and_then(|value| value.parse::<usize>().ok())).unwrap();
        let callback_group_sources = solved.intrusion.observed_groups()
            .filter(|(_, occurrence, _, _, _)| *occurrence == callback_work_occurrence)
            .flat_map(|(_, _, start, end, _)| solved.intrusion.parents[start..end].iter()
                .filter_map(|parent| parent.sources)
                .flat_map(|sources| context.source_events(sources).iter()
                    .filter_map(|&event| references.observed_checking(event))
                    .map(|checking| checking.source_ordinal()).collect::<Vec<_>>()))
            .collect::<std::collections::HashSet<_>>();
        assert!(callback_group_sources.contains(&callback_apply),
            "the callback Work::Bound consumer maps to the exact first f z source Apply");

        // R229: join this same source Call, source Lambda, annotation, provider
        // argument port, and Work::Bound consumer without relying on the
        // separately branded candidate_scheme audit.
        let data = &candidate.solved.data;
        let callback_occurrence = callback_call.checking_occurrence().occurrence();
        let registration_index = data.candidate_calls.formal_use_registration(&data.hir, callback_occurrence)
            .expect("the exact callback Apply resolves to a formal registration");
        let registration = &data.candidate_calls.formals[registration_index];
        let formal_source = data.hir.local_source_for(&registration.owner).unwrap().unwrap();
        let lambda = formal_source.expressions().get(registration.lambda).unwrap();
        let LocalSourceForm::Lambda { parameter, .. } = &lambda.form else { panic!("formal registration owns its Lambda") };
        assert_eq!(parameter.id, registration.parameter);
        assert_eq!(callback_call.formal_registration().unwrap().id, registration.parameter);
        assert_eq!(callback_call.formal_parameter_recipe_position(), Some(registration.recipe_position));
        let formal_root = registration.native_root.unwrap();
        assert!(matches!(data.store.term_view(formal_root),
            Ok(crate::TermView::LiveVariable(view)) if view.kind() == ComponentKind::Value
                && view.polarity() == Polarity::Positive));
        let algebra = &solved.intrusion.effect_algebra;
        let formal_domain = *algebra.formal_domains.get(&registration.recipe_position)
            .expect("the source annotation's function domain is retained at the exact formal recipe");
        let fact_at = |occurrence: &HirOccurrenceId, slot: u8| {
            let edge = data.store.provenance().iter().find(|edge| {
                edge.cause().occurrence().occurrence() == occurrence
                    && edge.cause().occurrence().local_slot() == u32::from(slot)
            }).unwrap_or_else(|| panic!("source occurrence {} slot {slot} has provenance", occurrence.ordinal()));
            data.store.facts().iter().find(|fact| fact.id() == edge.fact()).unwrap()
        };
        let formal_annotation_upper = fact_at(&lambda.occurrence, 44);
        assert_eq!(formal_annotation_upper.lower(), formal_root);
        assert_eq!(formal_annotation_upper.upper(), formal_domain,
            "the registered native formal root is linked to its source annotation's negative function domain");
        let lambda_fact = fact_at(&lambda.occurrence, 2);
        let crate::TermView::PositiveFunction { argument: lambda_argument, .. } = data.store.term_view(lambda_fact.lower()).unwrap()
            else { panic!("the exact Lambda constructor emits its positive function") };
        assert_eq!(lambda_argument, formal_domain,
            "the registered formal domain is the argument port of the owning Lambda constructor");
        assert!(matches!(data.store.term_view(lambda_fact.upper()),
            Ok(crate::TermView::Component(component)) if component.kind() == ComponentKind::Value
                && component.occurrence() == Some(&lambda.occurrence)),
            "Lambda slot 2 is owned by the exact source Lambda's value root");
        let provider_origin = solved.intrusion.effect_algebra.context.origins.iter()
            .find(|origin| origin.occurrence == *provider_call.checking_occurrence()).unwrap();
        assert_eq!(provider_origin.occurrence.occurrence().ordinal(), provider_call.checking_occurrence().occurrence().ordinal());
        let provider_replay = crate::candidate_context::RelationId(363);
        let TypedPairKey::Value(provider_pair) = solved.intrusion.effect_algebra.context.relation_pair(provider_replay).unwrap()
            else { panic!("provider callback replay is a value relation") };
        let provider_expected = match provider_pair.upper {
            ValueEndpointKey::NegativeFunction(term) => term,
            other => panic!("provider expected callback function: {other:?}"),
        };
        assert_ne!(provider_expected, formal_domain,
            "the local FreshUse creates a distinct term identity, so identity alone cannot join source annotation to provider expected port");
        let repeat_binding = local.bindings().iter().find(|binding| binding.spelling.as_ref() == "repeat").unwrap();
        let LocalSourceForm::Lambda { parameter: repeat_parameter, .. } = &local.expression(&repeat_binding.initializer).unwrap().form
            else { panic!("repeat's authentic initializer is the registered Lambda") };
        assert_eq!(local.expression(&repeat_binding.initializer).unwrap().occurrence,
            formal_source.expressions()[registration.lambda].occurrence);
        assert_eq!(repeat_parameter.id, registration.parameter);
        let LocalSourceForm::Name { resolution: LocalSourceResolution::Local(provider_local), .. } = &provider_call.callee_source().form
            else { panic!("the provider Apply uses the exact repeat local") };
        assert_eq!(provider_local, &repeat_binding.id);
        let repeat_route = solved.local_routes.iter().find(|route| route.occurrence.ordinal() == 27)
            .expect("the exact repeat Name has a retained LocalFreshRoute");
        assert_eq!(repeat_route.local, repeat_binding.id);
        let mut mapped_terms = Vec::<Option<Term>>::new();
        repeat_route.retained.observe_map_entries(|name, entry| {
            if name == "terms" {
                if let Some(crate::shadow_apply::CandidateFreshUseMapEntry::Term { index, value }) = entry {
                    if mapped_terms.len() <= index { mapped_terms.resize(index + 1, None); }
                    mapped_terms[index] = value;
                }
            }
        });
        let repeat_use_fact = fact_at(&provider_call.callee_source().occurrence, 0);
        assert_eq!(repeat_use_fact.lower(), mapped_terms[repeat_route.graph.root].unwrap(),
            "the exact repeat Name's slot-zero restoration is rooted at this route's mapped graph root");
        assert!(matches!(data.store.term_view(repeat_use_fact.upper()),
            Ok(crate::TermView::Component(component)) if component.kind() == ComponentKind::Value
                && component.occurrence() == Some(&provider_call.callee_source().occurrence)),
            "the route root is restored to the exact source repeat Name component");
        let argument_ports = repeat_route.graph.nodes.iter().enumerate().filter_map(|(index, node)| {
            let crate::candidate_scheme::Node::Function { polarity: Polarity::Positive, children } = node else { return None; };
            (mapped_terms.get(children[0]).copied().flatten() == Some(provider_expected)).then_some((index, children[0]))
        }).collect::<Vec<_>>();
        assert_eq!(argument_ports.len(), 1, "one retained positive repeat function exposes this exact provider expected port");
        let (repeat_function_node, repeat_argument_node) = argument_ports[0];
        assert!(matches!(repeat_route.graph.nodes[repeat_argument_node],
            crate::candidate_scheme::Node::Function { polarity: Polarity::Negative, .. }),
            "the exact Lambda argument port is a negative function node in the captured route");
        assert_eq!(mapped_terms[repeat_argument_node], Some(provider_expected),
            "the same route argument-port node's retained FreshUse image is the provider's expected callback function");
        let callback_demand = callback_call.native_demand();
        let demand_fact = fact_at(callback_occurrence, 0);
        assert_eq!(demand_fact.lower(), formal_root);
        assert_eq!(demand_fact.upper(), callback_demand,
            "the same registered formal root owns the callback body's source Apply demand");
        let callback_work = work_bounds.iter().find(|event|
            event.contains("raw=BoundKey(Effect(EffectRow(21)), Positive, Effect(EffectRow(31)))"))
            .expect("the exact callback formal's production Work::Bound selection");
        assert!(callback_work.contains(&format!("operation=Value(NegativeFunction({callback_demand:?}))")),
            "the exact body demand term is the operation selected by its source-owned Work::Bound");
        assert!(callback_group_sources.contains(&callback_apply));
        println!("R229 formal-registration={registration_index} parameter={:?} lambda={} annotation-domain={formal_domain:?} repeat-function-node={repeat_function_node} mapped-argument-node={repeat_argument_node} provider-expected={provider_expected:?} body-demand={callback_demand:?} demand-view={:?} work-bound={callback_work}",
            registration.parameter, lambda.occurrence.ordinal(), data.store.term_view(callback_demand));
        assert!(solved.intrusion.forest_event_log_complete());
        let (mut values, mut effects) = (Vec::<u32>::new(), Vec::<u32>::new());
        for event in solved.intrusion.forest_events() {
            match *event {
                crate::candidate_intrusion::ForestEvent::Birth(crate::candidate_scheme::RowKey::Value(row)) => { assert_eq!(row as usize, values.len()); values.push(row); }
                crate::candidate_intrusion::ForestEvent::Birth(crate::candidate_scheme::RowKey::Effect(row)) => { assert_eq!(row as usize, effects.len()); effects.push(row); }
                crate::candidate_intrusion::ForestEvent::ParentWrite { key: crate::candidate_scheme::RowKey::Value(row), before, after, .. } => { let slot=&mut values[row as usize]; assert_eq!(*slot,before); *slot=after; }
                crate::candidate_intrusion::ForestEvent::ParentWrite { key: crate::candidate_scheme::RowKey::Effect(row), before, after, .. } => { let slot=&mut effects[row as usize]; assert_eq!(*slot,before); *slot=after; }
                crate::candidate_intrusion::ForestEvent::Truncate { values_len, effects_len } => { values.truncate(values_len); effects.truncate(effects_len); }
            }
        }
        let final_forest = solved.intrusion.forest_snapshot().unwrap();
        assert_eq!(values, final_forest.values);
        assert_eq!(effects, final_forest.effects);
        let relevant_alias_writes = solved.intrusion.forest_events().iter().filter(|event| matches!(event,
            crate::candidate_intrusion::ForestEvent::ParentWrite { key: crate::candidate_scheme::RowKey::Effect(row), after, .. }
                if *row == item || *after == item || *row == 31 || *after == 31)).collect::<Vec<_>>();
        assert!(relevant_alias_writes.is_empty(),
            "complete alias history never attaches either the slot-4 item or callback formal item: {relevant_alias_writes:?}");
        let forest_root = |forest: &[u32], mut row: u32| {
            while forest[row as usize] != row { row = forest[row as usize]; }
            row
        };
        let mut callback_slot_alias_history = Vec::new();
        let (mut value_prefix, mut effect_prefix) = (Vec::<u32>::new(), Vec::<u32>::new());
        for (cursor, event) in solved.intrusion.forest_events().iter().enumerate() {
            match *event {
                crate::candidate_intrusion::ForestEvent::Birth(crate::candidate_scheme::RowKey::Value(row)) => { assert_eq!(row as usize, value_prefix.len()); value_prefix.push(row); }
                crate::candidate_intrusion::ForestEvent::Birth(crate::candidate_scheme::RowKey::Effect(row)) => { assert_eq!(row as usize, effect_prefix.len()); effect_prefix.push(row); }
                crate::candidate_intrusion::ForestEvent::ParentWrite { key: crate::candidate_scheme::RowKey::Value(row), before, after, .. } => { let slot=&mut value_prefix[row as usize]; assert_eq!(*slot,before); *slot=after; }
                crate::candidate_intrusion::ForestEvent::ParentWrite { key: crate::candidate_scheme::RowKey::Effect(row), before, after, .. } => { let slot=&mut effect_prefix[row as usize]; assert_eq!(*slot,before); *slot=after; }
                crate::candidate_intrusion::ForestEvent::Truncate { values_len, effects_len } => { value_prefix.truncate(values_len); effect_prefix.truncate(effects_len); }
            }
            if effect_prefix.len() > 31 && effect_prefix.len() > item as usize {
                callback_slot_alias_history.push((cursor, forest_root(&effect_prefix, 31), forest_root(&effect_prefix, item)));
            }
        }
        assert!(callback_slot_alias_history.iter().all(|(_, callback_rep, slot_rep)| callback_rep != slot_rep),
            "the callback formal item and slot-4 source item never alias in this complete history: {callback_slot_alias_history:?}");
        println!("R221 callback_applies={callback_applies:?} slot4_source={source_bound:?} slot4_local_image={slot4_image:?} callback_formal_item_image=Effect({repeat_item_image}) slot4_lineage_edges={} callback_slot_alias_history_end={:?} work_bounds={work_bounds:?} work_occurrences={work_occurrences:?} source_checks={source_checks:?} source_item_bound_mentions={} local_item_bound_mentions={} forest_effect_rows={} forest_complete=true replay=true",
            slot4_lineage.len(),
            callback_slot_alias_history.last(),
            work_bounds.iter().filter(|event| event.contains(&format!("EffectRow({item})"))).count(),
            work_bounds.iter().filter(|event| event.contains(&format!("EffectRow({loop_item_image})"))).count(),
            effects.len());
    }

    #[test]
    fn r231_cross_owner_source_schedule_variants() {
        const BASE: &str = r#"act io:
    our tick: int -> int

my outer (q:[io] int) = {
    my loop (x:[io] int) = {
        my direct = loop x
        my helper (y:[io] int) = loop y
        helper x
    }
    my repeat (f:[io] int -> int) (z:[io] int) = {
        my first = f z
        f z
    }
    repeat loop q
}"#;
        let variants = [
            ("callback-direct-loop", BASE.replace("        my first = f z", "        my side = loop z\n        my first = f z")),
            ("outer-direct-loop", BASE.replace("    repeat loop q", "    my side = loop q\n    repeat loop q")),
            ("repeat-provider-twice", BASE.replace("    repeat loop q", "    my first_call = repeat loop q\n    repeat loop q")),
            ("callback-extra-formal-call", BASE.replace("        f z\n    }", "        my second = f z\n        f z\n    }")),
            ("forward-provider-formal", BASE.replace("    repeat loop q", "    my relay (g:[io] int -> int) (w:[io] int) = repeat g w\n    relay loop q")),
            ("wrapped-provider-local", BASE.replace("    my repeat (f:[io] int -> int)", "    my wrapped (w:[io] int) = loop w\n    my repeat (f:[io] int -> int)").replace("    repeat loop q", "    repeat wrapped q")),
        ];

        for (case, source_text) in variants {
            let source: Arc<SourceText> = Arc::from(source_text.as_str());
            let parsed = parse_file(source.clone(), Arc::new(scan_header(source)), Arc::new(SyntaxEnvironment::empty()));
            assert!(parsed.structural_recoveries().is_empty(), "{case}: structural recovery");
            let hir = Arc::new(lower_module_with_local_source(
                ModuleIdentity::source_root(FileId::new(FileKey::new(case, "source.yu"))),
                &parsed, SemanticImports::empty(),
            ).unwrap());
            crate::candidate_context::r148_trace_begin();
            let candidate = CandidateInference::solve(hir).unwrap();
            let trace = crate::candidate_context::r148_trace_finish();
            let work_bounds = trace.iter().filter(|event| event.starts_with("work-bound ")).collect::<Vec<_>>();
            let merges = trace.iter().filter(|event| event.starts_with("row-merge ")).collect::<Vec<_>>();
            assert!(candidate.solved.data.errors.is_empty(), "{case}: candidate solve errors");
            let solved = candidate.solved.data.candidate_graph.as_ref().unwrap();
            assert!(solved.intrusion.forest_event_log_complete(), "{case}: complete alias history");
            let writes = solved.intrusion.forest_events().iter().filter(|event| matches!(event,
                crate::candidate_intrusion::ForestEvent::ParentWrite { key: crate::candidate_scheme::RowKey::Effect(_), .. }
            )).collect::<Vec<_>>();
            assert_eq!(writes.len(), merges.iter().filter(|event| event.contains("copy=Effect(")).count(),
                "{case}: every effect-row forest merge has its ordered trace record");
            let row_number = |event: &str, prefix: &str| event.strip_prefix(prefix)
                .and_then(|rest| rest.split(|ch: char| !ch.is_ascii_digit()).next())
                .and_then(|number| number.parse::<usize>().ok());
            let raw_effect_bound = |event: &str| {
                let raw = event.split("raw=BoundKey(Effect(EffectRow(").nth(1)?;
                let (owner, rest) = raw.split_once(")), ")?;
                let rest = rest.strip_prefix("Positive, Effect(EffectRow(")
                    .or_else(|| rest.strip_prefix("Negative, Effect(EffectRow("))?;
                let item = rest.split(")))").next()?;
                Some((owner.parse::<usize>().ok()?, item.parse::<usize>().ok()?))
            };
            let mut effect_representatives = (0..4096).collect::<Vec<usize>>();
            let mut cross_owner_hits = Vec::new();
            for event in &trace {
                if event.starts_with("row-merge copy=Effect(") {
                    let copy = row_number(event, "row-merge copy=Effect(").unwrap();
                    let parent = row_number(event.split(" parent=").nth(1).unwrap(), "Effect(").unwrap();
                    effect_representatives[copy] = parent;
                } else if event.starts_with("work-bound ") {
                    if let Some((owner, item)) = raw_effect_bound(event) {
                        let mut owner_root = owner;
                        while effect_representatives[owner_root] != owner_root { owner_root = effect_representatives[owner_root]; }
                        let mut item_root = item;
                        while effect_representatives[item_root] != item_root { item_root = effect_representatives[item_root]; }
                        if item_root != item && owner_root != item_root {
                            cross_owner_hits.push((event.clone(), owner_root, item_root));
                        }
                    }
                }
            }
            assert!(candidate.candidate_conflicts().is_empty(), "{case}: candidate source conflicts");
            println!("R231 case={case} accepted=true work_bounds={work_bounds:?} merges={merges:?} effect_parent_writes={writes:?} cross_owner_hits={cross_owner_hits:?}");
            assert_eq!(trace.iter().filter(|event| event.starts_with("extrusion-start ")).count(),
                trace.iter().filter(|event| event.starts_with("extrusion-finish ")).count(),
                "{case}: every started extrusion completes");
        }
    }

    #[test]
    fn r232_playground_samples_cross_owner_schedule_search() {
        let samples = [
            ("identity-island", include_str!("../../../../web/playground/examples/yulang2-identity-island.yu")),
            ("ordinary-islands", include_str!("../../../../web/playground/examples/yulang2-ordinary-islands.yu")),
            ("repeated-choice", include_str!("../../../../web/playground/examples/repeated-choice.yu")),
            ("polymorphic-escaping-closure", include_str!("../../../../web/playground/examples/polymorphic-escaping-closure.yu")),
        ];
        let mut accepted = 0;
        for (name, sample) in samples {
            let source: Arc<SourceText> = Arc::from(sample);
            let parsed = parse_file(source.clone(), Arc::new(scan_header(source)), Arc::new(SyntaxEnvironment::empty()));
            assert!(parsed.structural_recoveries().is_empty(), "{name}: structural recovery");
            let hir = Arc::new(lower_module_with_local_source(
                ModuleIdentity::source_root(FileId::new(FileKey::new(format!("r232-{name}"), "sample.yu"))),
                &parsed, SemanticImports::empty(),
            ).unwrap());
            crate::candidate_context::r148_trace_begin();
            let candidate = CandidateInference::solve(hir).unwrap();
            let trace = crate::candidate_context::r148_trace_finish();
            if !candidate.solved.data.errors.is_empty() || !candidate.candidate_conflicts().is_empty() {
                println!("R232 sample={name} candidate_accepted=false errors={} conflicts={}",
                    candidate.solved.data.errors.len(), candidate.candidate_conflicts().len());
                continue;
            }
            accepted += 1;
            let solved = candidate.solved.data.candidate_graph.as_ref().unwrap();
            assert!(solved.intrusion.forest_event_log_complete(), "{name}: complete alias history");
            let writes = solved.intrusion.forest_events().iter().filter(|event| matches!(event,
                crate::candidate_intrusion::ForestEvent::ParentWrite { key: crate::candidate_scheme::RowKey::Effect(_), .. }
            )).collect::<Vec<_>>();
            let merges = trace.iter().filter(|event| event.starts_with("row-merge copy=Effect(")).collect::<Vec<_>>();
            assert_eq!(writes.len(), merges.len(), "{name}: ordered trace accounts for every effect merge");
            let row_number = |event: &str, prefix: &str| event.strip_prefix(prefix)
                .and_then(|rest| rest.split(|ch: char| !ch.is_ascii_digit()).next())
                .and_then(|number| number.parse::<usize>().ok());
            let raw_effect_bound = |event: &str| {
                let raw = event.split("raw=BoundKey(Effect(EffectRow(").nth(1)?;
                let (owner, rest) = raw.split_once(")), ")?;
                let rest = rest.strip_prefix("Positive, Effect(EffectRow(")
                    .or_else(|| rest.strip_prefix("Negative, Effect(EffectRow("))?;
                let item = rest.split(")))").next()?;
                Some((owner.parse::<usize>().ok()?, item.parse::<usize>().ok()?))
            };
            let mut representatives = (0..4096).collect::<Vec<usize>>();
            let mut cross_owner_hits = Vec::new();
            for event in &trace {
                if event.starts_with("row-merge copy=Effect(") {
                    let copy = row_number(event, "row-merge copy=Effect(").unwrap();
                    let parent = row_number(event.split(" parent=").nth(1).unwrap(), "Effect(").unwrap();
                    representatives[copy] = parent;
                } else if event.starts_with("work-bound ") {
                    if let Some((owner, item)) = raw_effect_bound(event) {
                        let mut owner_root = owner;
                        while representatives[owner_root] != owner_root { owner_root = representatives[owner_root]; }
                        let mut item_root = item;
                        while representatives[item_root] != item_root { item_root = representatives[item_root]; }
                        if item_root != item && owner_root != item_root {
                            cross_owner_hits.push((event.clone(), owner_root, item_root));
                        }
                    }
                }
            }
            println!("R232 sample={name} candidate_accepted=true effect_merges={merges:?} work_bounds={:?} cross_owner_hits={cross_owner_hits:?}",
                trace.iter().filter(|event| event.starts_with("work-bound ")).collect::<Vec<_>>());
        }
        assert_eq!(accepted, samples.len(), "every executable browser sample enters ordinary candidate inference");
    }

    #[test]
    fn r233_playground_tool_examples_cross_owner_schedule_search() {
        let samples = [
            ("catch-operation", include_str!("../../../../tools/inference-playground/examples/catch-operation.yu")),
            ("catch-value", include_str!("../../../../tools/inference-playground/examples/catch-value.yu")),
            ("compose-scoped-identity", include_str!("../../../../tools/inference-playground/examples/compose-scoped-identity.yu")),
            ("compose-scoped-independent", include_str!("../../../../tools/inference-playground/examples/compose-scoped-independent.yu")),
            ("compose-scoped-two-uses", include_str!("../../../../tools/inference-playground/examples/compose-scoped-two-uses.yu")),
            ("conditional-conflict", include_str!("../../../../tools/inference-playground/examples/conditional-conflict.yu")),
            ("conditional-union", include_str!("../../../../tools/inference-playground/examples/conditional-union.yu")),
            ("effects", include_str!("../../../../tools/inference-playground/examples/effects.yu")),
            ("entry-computation-argument", include_str!("../../../../tools/inference-playground/examples/entry-computation-argument.yu")),
            ("entry-unmatched-request", include_str!("../../../../tools/inference-playground/examples/entry-unmatched-request.yu")),
            ("hygiene-argument", include_str!("../../../../tools/inference-playground/examples/hygiene-argument.yu")),
            ("hygiene-callback-block", include_str!("../../../../tools/inference-playground/examples/hygiene-callback-block.yu")),
            ("hygiene-callback", include_str!("../../../../tools/inference-playground/examples/hygiene-callback.yu")),
            ("hygiene-direct", include_str!("../../../../tools/inference-playground/examples/hygiene-direct.yu")),
            ("hygiene-outside-arm", include_str!("../../../../tools/inference-playground/examples/hygiene-outside-arm.yu")),
            ("identity", include_str!("../../../../tools/inference-playground/examples/identity.yu")),
            ("nested-recursion", include_str!("../../../../tools/inference-playground/examples/nested-recursion.yu")),
            ("original-suffix-outer-receiver", include_str!("../../../../tools/inference-playground/examples/original-suffix-outer-receiver.yu")),
            ("r171-formal-name-forwarding", include_str!("../../../../tools/inference-playground/examples/r171-formal-name-forwarding.yu")),
            ("type-error", include_str!("../../../../tools/inference-playground/examples/type-error.yu")),
        ];
        let mut accepted = 0;
        for (name, sample) in samples {
            let source: Arc<SourceText> = Arc::from(sample);
            let parsed = parse_file(source.clone(), Arc::new(scan_header(source)), Arc::new(SyntaxEnvironment::empty()));
            if !parsed.structural_recoveries().is_empty() {
                println!("R233 sample={name} candidate_accepted=false structural_recoveries={}", parsed.structural_recoveries().len());
                continue;
            }
            let hir = match lower_module_with_local_source(
                ModuleIdentity::source_root(FileId::new(FileKey::new(format!("r233-{name}"), "example.yu"))),
                &parsed, SemanticImports::empty(),
            ) {
                Ok(hir) => Arc::new(hir),
                Err(error) => { println!("R233 sample={name} candidate_accepted=false lowering={error:?}"); continue; }
            };
            crate::candidate_context::r148_trace_begin();
            let result = CandidateInference::solve(hir);
            let trace = crate::candidate_context::r148_trace_finish();
            let candidate = match result {
                Ok(candidate) => candidate,
                Err(error) => { println!("R233 sample={name} candidate_accepted=false solve={error:?}"); continue; }
            };
            if !candidate.solved.data.errors.is_empty() || !candidate.candidate_conflicts().is_empty() {
                println!("R233 sample={name} candidate_accepted=false errors={} conflicts={}",
                    candidate.solved.data.errors.len(), candidate.candidate_conflicts().len());
                continue;
            }
            accepted += 1;
            let solved = candidate.solved.data.candidate_graph.as_ref().unwrap();
            assert!(solved.intrusion.forest_event_log_complete(), "{name}: complete alias history");
            let writes = solved.intrusion.forest_events().iter().filter(|event| matches!(event,
                crate::candidate_intrusion::ForestEvent::ParentWrite { key: crate::candidate_scheme::RowKey::Effect(_), .. }
            )).collect::<Vec<_>>();
            let merges = trace.iter().filter(|event| event.starts_with("row-merge copy=Effect(")).collect::<Vec<_>>();
            assert_eq!(writes.len(), merges.len(), "{name}: every effect merge has an ordered trace record");
            let row_number = |event: &str, prefix: &str| event.strip_prefix(prefix)
                .and_then(|rest| rest.split(|ch: char| !ch.is_ascii_digit()).next())
                .and_then(|number| number.parse::<usize>().ok());
            let raw_effect_bound = |event: &str| {
                let raw = event.split("raw=BoundKey(Effect(EffectRow(").nth(1)?;
                let (owner, rest) = raw.split_once(")), ")?;
                let rest = rest.strip_prefix("Positive, Effect(EffectRow(")
                    .or_else(|| rest.strip_prefix("Negative, Effect(EffectRow("))?;
                let item = rest.split(")))").next()?;
                Some((owner.parse::<usize>().ok()?, item.parse::<usize>().ok()?))
            };
            let mut representatives = (0..4096).collect::<Vec<usize>>();
            let mut cross_owner_hits = Vec::new();
            for event in &trace {
                if event.starts_with("row-merge copy=Effect(") {
                    let copy = row_number(event, "row-merge copy=Effect(").unwrap();
                    let parent = row_number(event.split(" parent=").nth(1).unwrap(), "Effect(").unwrap();
                    representatives[copy] = parent;
                } else if event.starts_with("work-bound ") {
                    if let Some((owner, item)) = raw_effect_bound(event) {
                        let mut owner_root = owner;
                        while representatives[owner_root] != owner_root { owner_root = representatives[owner_root]; }
                        let mut item_root = item;
                        while representatives[item_root] != item_root { item_root = representatives[item_root]; }
                        if item_root != item && owner_root != item_root {
                            cross_owner_hits.push((event.clone(), owner_root, item_root));
                        }
                    }
                }
            }
            println!("R233 sample={name} candidate_accepted=true effect_merges={} work_bounds={} cross_owner_hits={cross_owner_hits:?}",
                merges.len(), trace.iter().filter(|event| event.starts_with("work-bound ")).count());
            if name == "nested-recursion" {
                println!("R233 nested-recursion ordered_merges={merges:?} work_bounds={:?}",
                    trace.iter().filter(|event| event.starts_with("work-bound ")).collect::<Vec<_>>());
            }
        }
        assert!(accepted > 0, "at least one checked-in tool example enters candidate inference");
    }

    #[test]
    fn r234_handler_recursion_source_schedule_variants() {
        const BASE: &str = r#"act io:
    our tick: int -> int

my outer (q:[io] int) = {
    my loop (x:[io] int) = {
        my direct = loop x
        my helper (y:[io] int) = loop y
        helper x
    }
    my repeat (f:[io] int -> int) (z:[io] int) = {
        my first = f z
        f z
    }
    repeat loop q
}"#;
        let recursive_handler = r#"act io:
    our tick: int -> int

my outer (q:[io] int) = {
    my loop (x:[io] int) = catch (loop x) { io::tick(p), _ -> p }
    my repeat (f:[io] int -> int) (z:[io] int) = f z
    repeat loop q
}"#;
        let variants = [
            ("handler-direct", BASE.replace("my direct = loop x", "my direct = catch (loop x) { io::tick(p), _ -> p }")),
            ("handler-helper-call", BASE.replace("        helper x", "        catch (helper x) { io::tick(p), _ -> p }")),
            ("handler-callback-call", BASE.replace("        my first = f z", "        my first = catch (f z) { io::tick(p), _ -> p }")),
            ("handler-provider-call", BASE.replace("    repeat loop q", "    catch (repeat loop q) { io::tick(p), _ -> p }")),
            ("handler-recursive-loop-body", recursive_handler.to_owned()),
        ];
        let mut accepted = 0;
        for (name, sample) in variants {
            let source: Arc<SourceText> = Arc::from(sample.as_str());
            let parsed = parse_file(source.clone(), Arc::new(scan_header(source)), Arc::new(SyntaxEnvironment::empty()));
            if !parsed.structural_recoveries().is_empty() {
                println!("R234 case={name} accepted=false structural_recoveries={}", parsed.structural_recoveries().len());
                continue;
            }
            let hir = match lower_module_with_local_source(
                ModuleIdentity::source_root(FileId::new(FileKey::new(format!("r234-{name}"), "source.yu"))),
                &parsed, SemanticImports::empty(),
            ) {
                Ok(hir) => Arc::new(hir),
                Err(error) => { println!("R234 case={name} accepted=false lowering={error:?}"); continue; }
            };
            crate::candidate_context::r148_trace_begin();
            let result = CandidateInference::solve(hir);
            let trace = crate::candidate_context::r148_trace_finish();
            let candidate = match result {
                Ok(candidate) => candidate,
                Err(error) => { println!("R234 case={name} accepted=false solve={error:?}"); continue; }
            };
            if !candidate.solved.data.errors.is_empty() || !candidate.candidate_conflicts().is_empty() {
                println!("R234 case={name} accepted=false errors={} conflicts={}", candidate.solved.data.errors.len(), candidate.candidate_conflicts().len());
                continue;
            }
            accepted += 1;
            let solved = candidate.solved.data.candidate_graph.as_ref().unwrap();
            assert!(solved.intrusion.forest_event_log_complete(), "{name}: complete alias history");
            let writes = solved.intrusion.forest_events().iter().filter(|event| matches!(event,
                crate::candidate_intrusion::ForestEvent::ParentWrite { key: crate::candidate_scheme::RowKey::Effect(_), .. }
            )).count();
            let merges = trace.iter().filter(|event| event.starts_with("row-merge copy=Effect(")).collect::<Vec<_>>();
            assert_eq!(writes, merges.len(), "{name}: every effect merge is traced");
            let row_number = |event: &str, prefix: &str| event.strip_prefix(prefix)
                .and_then(|rest| rest.split(|ch: char| !ch.is_ascii_digit()).next())
                .and_then(|number| number.parse::<usize>().ok());
            let raw_effect_bound = |event: &str| {
                let raw = event.split("raw=BoundKey(Effect(EffectRow(").nth(1)?;
                let (owner, rest) = raw.split_once(")), ")?;
                let rest = rest.strip_prefix("Positive, Effect(EffectRow(")
                    .or_else(|| rest.strip_prefix("Negative, Effect(EffectRow("))?;
                let item = rest.split(")))").next()?;
                Some((owner.parse::<usize>().ok()?, item.parse::<usize>().ok()?))
            };
            let mut representatives = (0..4096).collect::<Vec<usize>>();
            let mut hits = Vec::new();
            for event in &trace {
                if event.starts_with("row-merge copy=Effect(") {
                    let copy = row_number(event, "row-merge copy=Effect(").unwrap();
                    let parent = row_number(event.split(" parent=").nth(1).unwrap(), "Effect(").unwrap();
                    representatives[copy] = parent;
                } else if event.starts_with("work-bound ") {
                    if let Some((owner, item)) = raw_effect_bound(event) {
                        let mut owner_root = owner;
                        while representatives[owner_root] != owner_root { owner_root = representatives[owner_root]; }
                        let mut item_root = item;
                        while representatives[item_root] != item_root { item_root = representatives[item_root]; }
                        if item_root != item && owner_root != item_root { hits.push((event.clone(), owner_root, item_root)); }
                    }
                }
            }
            println!("R234 case={name} accepted=true effect_merges={merges:?} work_bounds={:?} hits={hits:?}",
                trace.iter().filter(|event| event.starts_with("work-bound ")).collect::<Vec<_>>());
        }
        assert!(accepted > 0, "at least one ordinary handler/recursion source is candidate-accepted");
    }

    #[test]
    fn r235_higher_order_effect_mismatch_source_route() {
        const SOURCE: &str = r#"act io:
    our ping: int -> int
act state:
    our put: int -> int

my bad: int -> [state] int = \x -> state::put x
my accept (f: int -> [io] int) = f 0
my main = accept bad
"#;
        let text: Arc<SourceText> = Arc::from(SOURCE);
        let parsed = parse_file(text.clone(), Arc::new(scan_header(text)), Arc::new(SyntaxEnvironment::empty()));
        assert!(parsed.structural_recoveries().is_empty());
        let hir = Arc::new(lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new("r235-effect-mismatch", "source.yu"))),
            &parsed, SemanticImports::empty(),
        ).unwrap());
        let candidate = CandidateInference::solve(hir).unwrap();
        assert!(candidate.candidate_conflicts().iter().any(|error|
            matches!(error.kind(), SolverErrorKind::IncompatibleEffect { .. })),
            "nested callback effect mismatch reaches the effect conflict consumer");
        let call = (0..candidate.source_call_count()).map(|index| candidate.source_call(index).unwrap())
            .find(|call| call.checking_occurrence().occurrence().ordinal() == 14)
            .expect("outer Apply whose argument is the annotated callback provider");
        assert!(matches!(call.argument_source().form, LocalSourceForm::Name { .. }));
    }
}
