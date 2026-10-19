use super::*;
use std::collections::HashSet;
use yu_hir::shadow::{
    LocalSourceForm, LocalSourceResolution, ShadowArtifact, lower_module_with_local_source,
};

const SOURCE: &str = "act io:\n    our tick: int -> int\n\nmy outer (q:[io] int) = {\n    my loop (x:[io] int) = {\n        my direct = loop x\n        my helper (y:[io] int) = loop y\n        helper x\n    }\n    loop q\n}\n";

fn fixed_hir() -> (Arc<HirModule>, ShadowArtifact) {
    let source: Arc<yu_syntax::SourceText> = Arc::from(SOURCE);
    let parsed = yu_syntax::parse_file(
        source.clone(),
        Arc::new(yu_syntax::scan_header(source)),
        Arc::new(yu_syntax::SyntaxEnvironment::empty()),
    );
    assert!(parsed.syntax_diagnostics().unwrap().is_empty());
    assert!(parsed.structural_recoveries().is_empty());
    let shadow = ShadowArtifact::from_parsed(parsed.clone()).unwrap();
    let hir = Arc::new(
        lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new("r74-c1", "source.yu"))),
            &parsed,
            SemanticImports::empty(),
        )
        .unwrap(),
    );
    (hir, shadow)
}

#[derive(Default)]
struct IdentityLabels {
    definitions: Vec<DefinitionRootId>,
    occurrences: Vec<HirOccurrenceId>,
    locals: Vec<yu_hir::HirLocalId>,
    parameters: Vec<yu_hir::HirParameterId>,
    catch_binders: Vec<yu_hir::shadow::LocalSourceCatchBinderId>,
    definitions_by_payload: Vec<DefId>,
    constraints: Vec<ConstraintOccurrenceId>,
}

fn identity_label<T: Eq + Clone>(items: &mut Vec<T>, item: &T) -> usize {
    if let Some(index) = items.iter().position(|previous| previous == item) {
        index
    } else {
        let index = items.len();
        items.push(item.clone());
        index
    }
}

fn collect_hir_expression(expression: &ResolvedExpr, labels: &mut IdentityLabels) {
    identity_label(&mut labels.occurrences, expression.occurrence());
    match expression {
        ResolvedExpr::Apply {
            callee, argument, ..
        } => {
            collect_hir_expression(callee, labels);
            collect_hir_expression(argument, labels);
        }
        ResolvedExpr::Group { inner, .. } => collect_hir_expression(inner, labels),
        ResolvedExpr::Lambda {
            parameter, body, ..
        } => {
            identity_label(&mut labels.parameters, parameter);
            collect_hir_expression(body, labels);
        }
        ResolvedExpr::Integer { .. } | ResolvedExpr::Name { .. } | ResolvedExpr::Error { .. } => {}
    }
}

fn collect_hir_identities(hir: &HirModule, labels: &mut IdentityLabels) {
    for item in hir.items() {
        match item {
            HirItem::Binding(binding) => {
                identity_label(&mut labels.definitions, binding.definition_root());
                for parameter in binding.parameters() {
                    identity_label(&mut labels.parameters, parameter.id());
                }
                collect_hir_expression(binding.value(), labels);
                if let Some(source) = hir.local_source(binding.definition_root()).unwrap() {
                    for expression in source.expressions() {
                        identity_label(&mut labels.occurrences, &expression.occurrence);
                        if let LocalSourceForm::Catch { arms, .. } = &expression.form {
                            for arm in arms {
                                use yu_hir::shadow::{
                                    LocalSourceCatchPattern as Pattern,
                                    LocalSourceCatchPayloadPattern as Payload,
                                    LocalSourceCatchValuePattern as PatternValue,
                                };
                                let mut collect_pattern = |value: &PatternValue| {
                                    if let PatternValue::Binder(binder) = value {
                                        identity_label(&mut labels.catch_binders, &binder.id);
                                    }
                                };
                                match &arm.pattern {
                                    Pattern::Value(value) => collect_pattern(value),
                                    Pattern::Operation {
                                        payloads,
                                        continuation,
                                        ..
                                    } => {
                                        for payload in payloads {
                                            if let Payload::Value(value) = payload {
                                                collect_pattern(value);
                                            }
                                        }
                                        collect_pattern(continuation);
                                    }
                                }
                            }
                        }
                    }
                    for local in source.bindings() {
                        identity_label(&mut labels.locals, &local.id);
                        for parameter in &local.parameters {
                            identity_label(&mut labels.parameters, &parameter.id);
                        }
                    }
                }
            }
            HirItem::Expression(expression) => collect_hir_expression(expression, labels),
            HirItem::Error { .. } => {}
        }
    }
}

fn value_identity_labels(
    projection: &candidate_value_graph::C1IdentityProjection,
    hir: &HirModule,
) -> IdentityLabels {
    let mut labels = IdentityLabels::default();
    collect_hir_identities(hir, &mut labels);
    for (root, id) in &projection.modules {
        identity_label(&mut labels.definitions, root);
        identity_label(&mut labels.definitions_by_payload, id);
    }
    let mut visit_value = |value: &candidate_value_graph::Value| match value {
        candidate_value_graph::Value::Module(id) => {
            identity_label(&mut labels.definitions_by_payload, id);
        }
        candidate_value_graph::Value::Local(id) => {
            identity_label(&mut labels.locals, id);
            if let Some(root) = id.definition_root() {
                identity_label(&mut labels.definitions, root);
            }
        }
        candidate_value_graph::Value::Parameter(id) => {
            identity_label(&mut labels.parameters, id);
            if let Some(root) = id.definition_root() {
                identity_label(&mut labels.definitions, root);
            }
        }
        candidate_value_graph::Value::CatchBinder(id) => {
            identity_label(&mut labels.catch_binders, id);
            if let Some(root) = id.definition_root() {
                identity_label(&mut labels.definitions, root);
            }
        }
        candidate_value_graph::Value::Expression(id) => {
            identity_label(&mut labels.occurrences, id);
        }
    };
    for (value, _) in &projection.vertices {
        visit_value(value);
    }
    for (_, value) in &projection.values_by_ordinal {
        visit_value(value);
    }
    for (constraint, _) in &projection.checking {
        identity_label(&mut labels.constraints, constraint);
        identity_label(&mut labels.occurrences, constraint.occurrence());
    }
    for (_, constraint) in &projection.checking_by_event {
        identity_label(&mut labels.constraints, constraint);
        identity_label(&mut labels.occurrences, constraint.occurrence());
    }
    labels
}

fn c1_identity_ledger(
    projection: &candidate_value_graph::C1IdentityProjection,
    labels: &IdentityLabels,
    hir: &HirModule,
    shadow: &ShadowArtifact,
) -> String {
    use candidate_value_graph::Value;
    let mut out = String::new();
    out.push_str("HIR_IDENTITY_OWNERS_BEGIN\n");
    for (index, root) in labels.definitions.iter().enumerate() {
        let position = shadow.definition_source_position(hir, root).unwrap();
        out.push_str(&format!(
            "definition d{index} source_position={position:?}\n"
        ));
    }
    for (index, occurrence) in labels.occurrences.iter().enumerate() {
        let position = shadow.occurrence_source_position(hir, occurrence).unwrap();
        out.push_str(&format!(
            "occurrence o{index} ordinal={} source_position={position:?}\n",
            occurrence.ordinal()
        ));
    }
    for (index, local) in labels.locals.iter().enumerate() {
        let position = shadow.local_source_position(hir, local).unwrap();
        let owner = local.definition_root().map(|root| {
            format!(
                "d{}",
                labels
                    .definitions
                    .iter()
                    .position(|item| item == root)
                    .unwrap()
            )
        });
        out.push_str(&format!(
            "local l{index} ordinal={} owner={owner:?} source_position={position:?}\n",
            local.ordinal()
        ));
    }
    for (index, parameter) in labels.parameters.iter().enumerate() {
        let origin = shadow.parameter_source_origin(hir, parameter).unwrap();
        let owner = parameter.definition_root().map(|root| {
            format!(
                "d{}",
                labels
                    .definitions
                    .iter()
                    .position(|item| item == root)
                    .unwrap()
            )
        });
        out.push_str(&format!(
            "parameter p{index} ordinal={} owner={owner:?} source_origin={origin:?}\n",
            parameter.ordinal()
        ));
    }
    out.push_str("HIR_IDENTITY_OWNERS_END\nCANDIDATE_VALUE_GRAPH_MAPS_BEGIN\n");
    for (root, id) in &projection.modules {
        let root_label = labels
            .definitions
            .iter()
            .position(|item| item == root)
            .unwrap();
        let id_label = labels
            .definitions_by_payload
            .iter()
            .position(|item| item == id)
            .unwrap();
        out.push_str(&format!("modules d{root_label}->defid m{id_label}\n"));
    }
    let mut value_label = |value: &Value| match value {
        Value::Module(id) => format!(
            "module:m{}",
            labels
                .definitions_by_payload
                .iter()
                .position(|item| item == id)
                .unwrap()
        ),
        Value::Local(id) => format!(
            "local:l{}",
            labels.locals.iter().position(|item| item == id).unwrap()
        ),
        Value::Parameter(id) => format!(
            "parameter:p{}",
            labels
                .parameters
                .iter()
                .position(|item| item == id)
                .unwrap()
        ),
        Value::CatchBinder(id) => format!(
            "catch:b{}",
            labels
                .catch_binders
                .iter()
                .position(|item| item == id)
                .unwrap()
        ),
        Value::Expression(id) => format!(
            "expression:o{}",
            labels
                .occurrences
                .iter()
                .position(|item| item == id)
                .unwrap()
        ),
    };
    for (value, ordinal) in &projection.vertices {
        out.push_str(&format!("vertices {}->{ordinal}\n", value_label(value)));
    }
    for (ordinal, value) in &projection.values_by_ordinal {
        out.push_str(&format!(
            "values_by_ordinal {ordinal}->{}\n",
            value_label(value)
        ));
    }
    for (constraint, event) in &projection.checking {
        let constraint_label = labels
            .constraints
            .iter()
            .position(|item| item == constraint)
            .unwrap();
        let occurrence_label = labels
            .occurrences
            .iter()
            .position(|item| item == constraint.occurrence())
            .unwrap();
        out.push_str(&format!(
            "checking c{constraint_label}->event:{event} source=o{occurrence_label}/slot:{}\n",
            constraint.local_slot()
        ));
    }
    for (event, constraint) in &projection.checking_by_event {
        let constraint_label = labels
            .constraints
            .iter()
            .position(|item| item == constraint)
            .unwrap();
        let occurrence_label = labels
            .occurrences
            .iter()
            .position(|item| item == constraint.occurrence())
            .unwrap();
        out.push_str(&format!(
            "checking_by_event {event}->c{constraint_label} source=o{occurrence_label}/slot:{}\n",
            constraint.local_slot()
        ));
    }
    out.push_str("CANDIDATE_VALUE_GRAPH_MAPS_END\n");
    out
}

#[test]
fn fixed_ordinary_candidate_source_records_exact_helper_c1_without_solver_mutation() {
    let (hir, shadow) = fixed_hir();
    let owner = hir
        .items()
        .iter()
        .find_map(|item| match item {
            HirItem::Binding(binding) if binding.name().spelling() == "outer" => {
                Some(binding.definition_root().clone())
            }
            _ => None,
        })
        .expect("fixed outer binding");
    let source = hir
        .local_source(&owner)
        .unwrap()
        .expect("ordinary local source");
    let helper = source
        .bindings()
        .iter()
        .find(|binding| binding.spelling.as_ref() == "helper")
        .expect("fixed helper local")
        .id
        .clone();
    let helper_occurrences: Vec<_> = source.expressions().iter().filter(|expression| matches!(
        &expression.form,
        LocalSourceForm::Name { resolution: LocalSourceResolution::Local(local), .. } if local == &helper
    )).map(|expression| expression.occurrence.clone()).collect();
    assert_eq!(
        helper_occurrences.len(),
        1,
        "the fixed source has one helper Local use"
    );

    let batch = ConstraintBatch::collect_candidate_mode(hir, true, true).unwrap();
    assert!(
        !batch.candidate_source.scoped_experiment,
        "the fixed source uses ordinary candidate mode"
    );
    let mut session = InferenceSession::try_new_candidate(batch).unwrap();
    candidate_scheme::candidate_test_begin_c1_observation();
    session.execute().unwrap();
    let observations = candidate_scheme::candidate_test_take_c1_observations();
    let helper_observations: Vec<_> = observations
        .iter()
        .filter(|row| row.local == helper)
        .collect();
    assert_eq!(
        helper_observations.len(),
        1,
        "the exact helper Local occurrence reaches C1 once"
    );
    let observation = helper_observations[0];
    assert_eq!(observation.occurrence, helper_occurrences[0]);
    assert_eq!(
        observation.cursor,
        candidate_scheme::LocalUseCursor::default()
    );
    assert_eq!(
        (
            observation.cursor.next_bound,
            observation.cursor.restoration,
            observation.cursor.complete
        ),
        (0, None, false)
    );
    assert!(observation.ledger.contains("BY_OUTPUT_INDEX="));
    assert!(observation.ledger.contains("TYPED_PAIR_MEMOS="));
    assert!(observation.ledger.contains("SOURCE_PLAN="));
    let labels = value_identity_labels(&observation.value_graph, &hir);
    let identity_ledger = c1_identity_ledger(&observation.value_graph, &labels, &hir, &shadow);
    assert!(
        labels.catch_binders.is_empty(),
        "the fixed source has no catch binders"
    );
    assert_eq!(
        labels.definitions.len(),
        1,
        "the fixed HIR has one definition owner"
    );
    assert!(
        labels
            .locals
            .iter()
            .all(|local| local.definition_root() == Some(&labels.definitions[0]))
    );
    assert!(
        labels
            .parameters
            .iter()
            .all(|parameter| parameter.definition_root() == Some(&labels.definitions[0]))
    );
    assert!(labels.definitions_by_payload.iter().all(|id| {
        observation
            .value_graph
            .modules
            .iter()
            .any(|(_, module_id)| module_id == id)
    }));
    assert_eq!(
        labels
            .occurrences
            .iter()
            .map(HirOccurrenceId::ordinal)
            .collect::<HashSet<_>>()
            .len(),
        labels.occurrences.len(),
        "occurrence ordinals are unique within the one fixed HIR artifact"
    );
    assert_eq!(
        labels
            .locals
            .iter()
            .map(yu_hir::HirLocalId::ordinal)
            .collect::<HashSet<_>>()
            .len(),
        labels.locals.len(),
        "local ordinals are unique under the one fixed definition owner"
    );
    assert_eq!(
        labels
            .parameters
            .iter()
            .map(yu_hir::HirParameterId::ordinal)
            .collect::<HashSet<_>>()
            .len(),
        labels.parameters.len(),
        "parameter ordinals are unique under the one fixed definition owner"
    );
    assert!(labels.constraints.len() >= observation.value_graph.checking.len());
    println!(
        "R75-C1-LEDGER-BEGIN\n{}{}R75-C1-LEDGER-END",
        observation.ledger, identity_ledger
    );

    let result = session.finish_candidate().unwrap();
    assert!(
        result.data.errors.is_empty(),
        "observer did not prevent the fixed candidate execution from completing"
    );
}
