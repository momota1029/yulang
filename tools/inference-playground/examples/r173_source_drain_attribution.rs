use std::sync::Arc;

use yu_hir::shadow::{LocalSourceForm, lower_module_with_local_source};
use yu_hir::{FileId, FileKey, HirBinding, HirModule, HirOccurrenceId, ModuleIdentity, SemanticImports};
use yu_solver::shadow_apply::CandidateInference;
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

const SOURCE: &str = include_str!("r171-formal-name-forwarding.yu");
const MAX_ROWS: usize = 256;

fn binding<'a>(hir: &'a HirModule, name: &str) -> Result<&'a HirBinding, String> {
    hir.items().iter().find_map(|item| match item {
        yu_hir::HirItem::Binding(binding) if binding.name().spelling() == name => Some(binding),
        _ => None,
    }).ok_or_else(|| format!("R171 binding {name} missing"))
}

fn main() -> Result<(), String> {
    let source: Arc<SourceText> = Arc::from(SOURCE);
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    if !parsed.structural_recoveries().is_empty() { return Err("R171 fixture has structural recovery".into()); }
    let hir = Arc::new(lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new("inference-playground-r173", "r171-formal-name-forwarding.yu"))),
        &parsed,
        SemanticImports::empty(),
    ).map_err(|error| format!("R171 fixture lowering unavailable: {error:?}"))?);

    let terminal = binding(&hir, "terminal")?;
    let terminal_source = hir.local_source(terminal.definition_root())
        .map_err(|error| format!("terminal source unavailable: {error:?}"))?
        .ok_or_else(|| "terminal local source missing".to_owned())?;
    let terminal_lambda = terminal_source.expression(terminal_source.body())
        .ok_or_else(|| "terminal body expression missing".to_owned())?;
    let LocalSourceForm::Lambda { body, .. } = &terminal_lambda.form else { return Err("terminal source locator is not Lambda".into()); };
    let terminal_body = terminal_source.expression(body).ok_or_else(|| "terminal body source missing".to_owned())?;
    if !matches!(&terminal_body.form, LocalSourceForm::Name { .. }) { return Err("terminal body source locator is not Name".into()); }

    let relay = binding(&hir, "relay")?;
    let relay_source = hir.local_source(relay.definition_root())
        .map_err(|error| format!("relay source unavailable: {error:?}"))?
        .ok_or_else(|| "relay local source missing".to_owned())?;
    let relay_lambda = relay_source.expression(relay_source.body())
        .ok_or_else(|| "relay definition expression missing".to_owned())?;
    let LocalSourceForm::Lambda { body, .. } = &relay_lambda.form else {
        return Err("relay definition expression is not Lambda".into());
    };
    let forwarding_apply = relay_source.expression(body)
        .ok_or_else(|| "relay lambda body expression missing".to_owned())?;
    if !matches!(&forwarding_apply.form, LocalSourceForm::Apply { .. }) { return Err("forwarding source locator is not Apply".into()); }
    let LocalSourceForm::Apply { callee, argument, .. } = &forwarding_apply.form else { unreachable!() };
    let forwarding_callee = relay_source.expression(callee).ok_or_else(|| "forwarding callee source missing".to_owned())?;
    let forwarding_argument = relay_source.expression(argument).ok_or_else(|| "forwarding argument source missing".to_owned())?;
    if !matches!(&forwarding_argument.form, LocalSourceForm::Name { .. }) { return Err("forwarding argument source locator is not Name".into()); }

    let terminal_occurrence: &HirOccurrenceId = &terminal_lambda.occurrence;
    let terminal_body_occurrence: &HirOccurrenceId = &terminal_body.occurrence;
    let forwarding_occurrence: &HirOccurrenceId = &forwarding_apply.occurrence;
    let forwarding_argument_occurrence: &HirOccurrenceId = &forwarding_argument.occurrence;
    let source_keys = [
        (terminal_occurrence, 2), (terminal_occurrence, 4), (terminal_occurrence, 30),
        (terminal_body_occurrence, 1), (terminal_body_occurrence, 2),
        (forwarding_occurrence, 0), (forwarding_occurrence, 2),
        (forwarding_argument_occurrence, 1), (forwarding_argument_occurrence, 2),
    ];
    let candidate = CandidateInference::solve(hir.clone())
        .map_err(|error| format!("R173 candidate inference unavailable: {error:?}"))?;
    let observation = candidate.source_provider_observation(&source_keys, forwarding_occurrence, MAX_ROWS)
        .map_err(|error| format!("R173 source query unavailable: {error:?}"))?;

    println!("R173 source facts complete={} count={}", observation.facts_complete, observation.facts.len());
    for fact in &observation.facts { println!("  source={:?} cause={:?} fact={:?}", fact.occurrence, fact.cause, fact.fact); }
    println!("R173 Origin candidates complete={} count={}", observation.origins_complete, observation.origins.len());
    for origin in &observation.origins { println!("  graph={} source={:?}/slot{} relation={} attribution={:?}", origin.graph_index, origin.occurrence, origin.local_slot, origin.relation, origin.attribution); }
    println!("R173 dependencies complete={} count={}", observation.dependencies_complete, observation.dependencies.len());
    for dependency in &observation.dependencies { println!("  graph={} origin={} relation={} ordinal={} {:?} replay={:?}", dependency.graph_index, dependency.seed_origin_index, dependency.seed_relation, dependency.ordinal, dependency.dependency, dependency.replay); }
    println!("R173 Capture/maps routes={} route_complete={} bounds_complete={} maps_complete={}", observation.provider_route_matches, observation.provider_route_complete, observation.capture_bounds_complete, observation.maps_complete);
    for capture in &observation.captures { println!("  graph={} route={} occurrence={:?} use={} relation={:?} kind={:?} ordinal={} map={:?} entry={:?} structure={:?}", capture.graph_index, capture.route, capture.route_occurrence, capture.context_use, capture.relation, capture.kind, capture.ordinal, capture.map_name, capture.map_entry, capture.structure); }
    println!("R173 consumer Apply={:?} callee={:?} target={:?} native_callee={:?} native_demand={:?}", observation.consumer.apply, observation.consumer.callee, observation.consumer.module_target, observation.consumer.native_callee, observation.consumer.native_demand);
    println!("R173 direct_source_drain_attribution={:?} captures_structured={} maps_structured={} consumer_relation_join_complete={} discriminating={}", observation.direct_source_drain_attribution, observation.captures_structured, observation.maps_structured, observation.consumer_relation_join_complete, observation.source_to_consumer_discriminating());
    for relation in &observation.consumer_relations { println!("  consumer graph={} drain={} cause={:?} task={:?} relation={}", relation.graph_index, relation.drain_index, relation.cause, relation.task, relation.relation); }
    println!("R173 forwarding callee source={:?}", forwarding_callee.occurrence);
    Ok(())
}
