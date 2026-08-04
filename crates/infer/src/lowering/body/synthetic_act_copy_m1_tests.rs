use super::act_copy_census::{
    ActTemplateCatalogSource, SyntheticActCopyKind, capture_synthetic_act_copy_census,
};
use super::*;
use crate::module_table::nominal_act_identity::{
    NominalActInstanceSubstitution, NominalActTemplateIdentity, NominalActTypeRole,
    NominalActValueMemberKind,
};
use crate::module_table::typed_act_catalog::TypedActTemplateCatalog;
use crate::module_table::typed_act_template::{
    StableExternalReferenceKey, StableReceiverKind, TypedActTemplate,
};
use poly::expr::{Def, Expr};
use rustc_hash::FxHashSet;

const VAR_TEMPLATE: &str = concat!(
    "pub act ref_update 'a:\n",
    "  pub update: 'a -> 'a\n",
    "pub type ref 'e 'a with:\n",
    "  struct self:\n",
    "    get: () -> ['e] 'a\n",
    "    update_effect: () -> [ref_update 'a; 'e] ()\n",
    "  pub r.update(f: 'a -> 'a): ['e] () =\n",
    "    my loop(x: [_] _) = catch x:\n",
    "      ref_update::update v, k -> loop:k:f v\n",
    "    loop:r.update_effect()\n",
    "pub act var 't:\n",
    "  pub get: () -> 't\n",
    "  pub set: 't -> ()\n",
    "  my var_ref(): std::control::var::ref '[var 't] 't = std::control::var::ref {\n",
    "    get: \\() -> get(),\n",
    "    update_effect: \\() -> set:std::control::var::ref_update::update:get()\n",
    "  }\n",
    "  my run(v: 't, x: [_] 'r): 'r = catch x:\n",
    "    get(), k -> run v: k v\n",
    "    set v, k -> run v: k()\n",
);
const FLOW_TEMPLATE: &str = concat!(
    "pub act sub 'a:\n",
    "  pub return: 'a -> never\n",
    "  pub sub(x: [_] 'a): 'a = catch x:\n",
    "    return a, _ -> a\n",
    "    a -> a\n",
    "pub act label_sub 'a:\n",
    "  pub return: 'a -> never\n",
    "  pub struct label { marker: unit }\n",
    "  our control_label = label { marker: () }\n",
    "  pub sub(x: [_] 'a): 'a = catch x:\n",
    "    return a, _ -> a\n",
    "    sub::return a, _ -> a\n",
    "    a -> a\n",
);

#[test]
fn m1_0_census_distinguishes_cold_embedded_and_warm_prefix_legacy_routes() {
    let source = mixed_source(1);
    let cold_files = std_loaded(&format!("mod std;\n{source}"));
    let (cold, cold_census) =
        capture_synthetic_act_copy_census(|| lower_loaded_files(&cold_files).unwrap());
    assert!(cold.errors.is_empty(), "cold: {:?}", cold.errors);
    assert_legacy_cell(
        cold_census.cell(
            SyntheticActCopyKind::Var,
            ActTemplateCatalogSource::Embedded,
        ),
        1,
    );
    assert_legacy_cell(
        cold_census.cell(
            SyntheticActCopyKind::LabelSub,
            ActTemplateCatalogSource::Embedded,
        ),
        1,
    );
    assert_eq!(
        cold_census.cell(SyntheticActCopyKind::Var, ActTemplateCatalogSource::Prefix),
        Default::default(),
    );

    let prefix = std_prefix();
    let suffix = sources::load(vec![source_file(&[], &source)]);
    let (warm, warm_census) = capture_synthetic_act_copy_census(|| {
        lower_loaded_files_with_prefix(&prefix, &suffix).unwrap()
    });
    assert!(warm.errors.is_empty(), "warm: {:?}", warm.errors);
    assert_legacy_cell(
        warm_census.cell(SyntheticActCopyKind::Var, ActTemplateCatalogSource::Prefix),
        1,
    );
    assert_legacy_cell(
        warm_census.cell(
            SyntheticActCopyKind::LabelSub,
            ActTemplateCatalogSource::Prefix,
        ),
        1,
    );
    assert_eq!(
        warm_census.cell(
            SyntheticActCopyKind::LabelSub,
            ActTemplateCatalogSource::Embedded,
        ),
        Default::default(),
    );
    assert_warm_cold_normalized_scheme_parity(&cold, &warm, SyntheticActCopyKind::Var);
    assert_warm_cold_normalized_scheme_parity(&cold, &warm, SyntheticActCopyKind::LabelSub);
}

#[test]
fn m1_0_legacy_cost_fixtures_pin_warm_and_cold_var_and_label_sub_slopes() {
    let prefix = std_prefix();
    let mut var_timings = Vec::new();
    let mut label_timings = Vec::new();
    let mut cold_var_timings = Vec::new();
    let mut cold_label_timings = Vec::new();
    for count in 1..=3 {
        let (var, var_census) = warm_case(&prefix, &var_source(count));
        assert_legacy_cell(
            var_census.cell(SyntheticActCopyKind::Var, ActTemplateCatalogSource::Prefix),
            count,
        );
        assert_eq!(var.modules.synthetic_var_act_copy_ids().len(), count);
        assert_instances_have_one_normalized_scheme_view(
            &var,
            SyntheticActCopyKind::Var,
            var.modules.synthetic_var_act_copy_ids(),
        );
        var_timings.push(var.timing.synthetic_act_copy);

        let (label, label_census) = warm_case(&prefix, &label_source(count));
        assert_legacy_cell(
            label_census.cell(
                SyntheticActCopyKind::LabelSub,
                ActTemplateCatalogSource::Prefix,
            ),
            count,
        );
        assert_eq!(
            label.modules.synthetic_sub_label_act_copy_ids().len(),
            count
        );
        assert_instances_have_one_normalized_scheme_view(
            &label,
            SyntheticActCopyKind::LabelSub,
            label.modules.synthetic_sub_label_act_copy_ids(),
        );
        label_timings.push(label.timing.synthetic_act_copy);

        let (cold_var, cold_var_census) = cold_case(&var_source(count));
        assert_legacy_cell(
            cold_var_census.cell(
                SyntheticActCopyKind::Var,
                ActTemplateCatalogSource::Embedded,
            ),
            count,
        );
        cold_var_timings.push(cold_var.timing.synthetic_act_copy);

        let (cold_label, cold_label_census) = cold_case(&label_source(count));
        assert_legacy_cell(
            cold_label_census.cell(
                SyntheticActCopyKind::LabelSub,
                ActTemplateCatalogSource::Embedded,
            ),
            count,
        );
        cold_label_timings.push(cold_label.timing.synthetic_act_copy);
    }

    eprintln!("M1-0 warm var synthetic-copy timings: {var_timings:?}");
    eprintln!("M1-0 warm label_sub synthetic-copy timings: {label_timings:?}");
    eprintln!("M1-0 cold var synthetic-copy timings: {cold_var_timings:?}");
    eprintln!("M1-0 cold label_sub synthetic-copy timings: {cold_label_timings:?}");
    assert!(var_timings.iter().all(|elapsed| *elapsed > Duration::ZERO));
    assert!(
        label_timings
            .iter()
            .all(|elapsed| *elapsed > Duration::ZERO)
    );
    assert!(
        var_timings[2] > var_timings[0],
        "var fixture lost its positive cost slope"
    );
    assert!(
        label_timings[2] > label_timings[0],
        "label_sub fixture lost its positive cost slope"
    );
    assert!(
        cold_var_timings[2] > cold_var_timings[0],
        "cold var fixture lost its positive cost slope"
    );
    assert!(
        cold_label_timings[2] > cold_label_timings[0],
        "cold label_sub fixture lost its positive cost slope"
    );
}

#[test]
fn m1_1_records_complete_var_and_label_sub_nominal_shell_substitutions() {
    let source = mixed_source(2);
    let (cold, _) = cold_case(&source);
    assert_complete_nominal_shell_recording(&cold);
    let prefix = std_prefix();
    let (warm, _) = warm_case(&prefix, &source);
    assert_complete_nominal_shell_recording(&warm);
}

#[test]
fn m1_2_captures_and_substitutes_closed_var_and_label_sub_scheme_graphs() {
    let (output, _) = cold_case(&mixed_source(2));
    assert_typed_scheme_template_round_trip(
        &output,
        output.modules.synthetic_var_act_copy_ids(),
        &[vec!["std", "control", "var", "ref"]],
    );
    assert_typed_scheme_template_round_trip(
        &output,
        output.modules.synthetic_sub_label_act_copy_ids(),
        &[vec!["std", "control", "flow", "sub"]],
    );

    // Scheme capture emits nominal/effect paths today. These additional stable variants reserve
    // body-reference keys without smuggling arena-local DefIds into the M1-3 format.
    let expected_body_external_keys = FxHashSet::from_iter([
        StableExternalReferenceKey::Method {
            owner: vec!["std".into(), "control".into(), "var".into(), "ref".into()],
            name: "update".into(),
            receiver: StableReceiverKind::Value,
        },
        StableExternalReferenceKey::Operation {
            family: vec![
                "std".into(),
                "control".into(),
                "var".into(),
                "ref_update".into(),
            ],
            name: "update".into(),
        },
        StableExternalReferenceKey::Operation {
            family: vec!["std".into(), "control".into(), "flow".into(), "sub".into()],
            name: "return".into(),
        },
    ]);
    let ref_type = type_at_path(&output, &["std", "control", "var", "ref"]);
    let ref_update_type = type_at_path(&output, &["std", "control", "var", "ref_update"]);
    let sub_type = type_at_path(&output, &["std", "control", "flow", "sub"]);
    let ref_update = output.modules.value_decls(
        output.modules.type_companion(ref_update_type.id).unwrap(),
        &Name("update".into()),
    )[0]
    .def;
    let sub_return = output.modules.value_decls(
        output.modules.type_companion(sub_type.id).unwrap(),
        &Name("return".into()),
    )[0]
    .def;
    let ref_update_method = output
        .modules
        .type_methods(ref_type.id)
        .iter()
        .find(|method| method.name == Name("update".into()))
        .unwrap()
        .def;
    let actual_body_external_keys = FxHashSet::from_iter([
        output
            .modules
            .stable_external_reference_key(ref_update_method)
            .unwrap(),
        output
            .modules
            .stable_external_reference_key(ref_update)
            .unwrap(),
        output
            .modules
            .stable_external_reference_key(sub_return)
            .unwrap(),
    ]);
    assert_eq!(actual_body_external_keys, expected_body_external_keys);
    assert!(
        output
            .session
            .poly
            .refs()
            .iter()
            .any(|target| *target == Some(ref_update))
    );
    assert!(output.session.poly.exprs().iter().any(|expr| {
        let Expr::Catch(_, arms) = expr else {
            return false;
        };
        arms.iter().any(|arm| {
            arm.operation
                .as_ref()
                .is_some_and(|operation| operation.def == Some(sub_return))
        })
    }));
}

#[test]
fn m1_3_clones_var_and_label_sub_body_graphs_with_mixed_catch_identity_parity() {
    let (output, _) = cold_case(&mixed_source(2));
    let var_destinations = output.modules.synthetic_var_act_copy_ids();
    let label_destinations = output.modules.synthetic_sub_label_act_copy_ids();
    assert_body_graph_parity(&output, &var_destinations, "run");
    assert_body_graph_parity(&output, &label_destinations, "return");

    let destination = label_destinations[0];
    let substitution = output
        .modules
        .nominal_act_instance_substitution(destination)
        .unwrap();
    let identity = template_for_instance(&output, destination);
    let typed = TypedActTemplate::capture(identity, &output.session.poly).unwrap();
    let body = typed
        .capture_body(
            identity,
            &output.session.poly,
            &output.modules,
            &output.labels,
        )
        .unwrap_or_else(|error| {
            panic!(
                "body capture {error:?}; labels={:?}",
                output.labels.def_labels().collect::<Vec<_>>()
            )
        });
    let product = body.apply(substitution).unwrap();
    let source_return = identity
        .value_members
        .iter()
        .find(|member| member.name == Name("return".into()))
        .unwrap();
    let NominalActValueMemberKind::Operation {
        operation_path: source_return_path,
    } = &source_return.kind
    else {
        panic!("label_sub.return must be an operation");
    };
    let destination_return_path = crate::namespace_path(
        substitution
            .operation_path_map
            .get(source_return_path)
            .unwrap(),
    );
    let destination_return = substitution.def_map[&source_return.source];
    let detached_return = product
        .member_destinations
        .iter()
        .find_map(|(detached, destination)| {
            (*destination == destination_return).then_some(*detached)
        })
        .unwrap();
    let external_return = StableExternalReferenceKey::Operation {
        family: vec!["std".into(), "control".into(), "flow".into(), "sub".into()],
        name: "return".into(),
    };
    let mut local_arms = 0;
    let mut external_arms = 0;
    for (expr_index, expr) in product.arena.exprs().iter().enumerate() {
        let Expr::Catch(_, arms) = expr else { continue };
        for (arm_index, arm) in arms.iter().enumerate() {
            let Some(operation) = &arm.operation else {
                continue;
            };
            let site = crate::module_table::typed_act_body::CatchSite {
                expr: poly::expr::ExprId(expr_index as u32),
                arm: arm_index,
            };
            if operation.def == Some(detached_return) {
                local_arms += 1;
                assert_eq!(operation.path, destination_return_path);
                assert!(!product.external_catches.contains_key(&site));
            }
            if product.external_catches.get(&site) == Some(&external_return) {
                external_arms += 1;
                assert_eq!(
                    operation.path,
                    vec!["std", "control", "flow", "sub", "return"]
                        .into_iter()
                        .map(str::to_string)
                        .collect::<Vec<_>>()
                );
                assert_eq!(operation.def, None);
            }
        }
    }
    assert_eq!(local_arms, 1, "fresh label_sub.return catch arm");
    assert_eq!(external_arms, 1, "canonical sub.return catch arm");
}

#[test]
fn m1_4_catalog_installs_finalized_var_and_label_sub_instances_before_use_drain() {
    let source = concat!(
        "my var_case =\n",
        "  my $v = 1\n",
        "  &v = $v\n",
        "  $v\n",
        "my label_case = sub 'outer:\n",
        "  'outer.return 7\n",
        "var_case\n",
        "label_case\n",
    );
    let prefix = std_prefix();
    let (legacy, _) = warm_case(&prefix, source);
    let legacy_runtime = m1_runtime_output(
        &legacy.session.poly,
        legacy.subtype_provenance(),
        &legacy.labels,
    );
    let var_destination = legacy.modules.synthetic_var_act_copy_ids()[0];
    let label_destination = legacy.modules.synthetic_sub_label_act_copy_ids()[0];
    let var_substitution = legacy
        .modules
        .nominal_act_instance_substitution(var_destination)
        .unwrap()
        .clone();
    let label_substitution = legacy
        .modules
        .nominal_act_instance_substitution(label_destination)
        .unwrap()
        .clone();

    let mut catalog = TypedActTemplateCatalog::new();
    for (kind, substitution) in [
        (SyntheticActCopyKind::Var, &var_substitution),
        (SyntheticActCopyKind::LabelSub, &label_substitution),
    ] {
        let identity = legacy
            .modules
            .nominal_act_template_identity(substitution.template_root_act)
            .unwrap()
            .clone();
        catalog
            .capture(
                kind,
                identity,
                &legacy.session.poly,
                &legacy.modules,
                &legacy.labels,
            )
            .unwrap();
    }

    // Preserve the actual user bodies and namespace IDs, but return the synthetic members to
    // their pre-analysis shell state. Session construction must therefore not seed them as prefix
    // definitions; only the catalog installation below may publish them as finalized.
    let mut comparison_poly = legacy.session.poly.clone();
    for destination in var_substitution
        .def_map
        .values()
        .chain(label_substitution.def_map.values())
        .copied()
    {
        let Def::Let { vis, children, .. } = comparison_poly
            .defs
            .get(destination)
            .expect("destination shell")
            .clone()
        else {
            panic!("template member must be a binding shell");
        };
        comparison_poly.defs.set(
            destination,
            Def::Let {
                vis,
                scheme: None,
                body: None,
                children,
            },
        );
    }
    let mut session = AnalysisSession::new(comparison_poly);
    let mut labels = legacy.labels.clone();
    let var_entry = catalog
        .entry(
            SyntheticActCopyKind::Var,
            var_substitution.template_root_act,
        )
        .unwrap();
    let label_entry = catalog
        .entry(
            SyntheticActCopyKind::LabelSub,
            label_substitution.template_root_act,
        )
        .unwrap();
    let var_installed = var_entry
        .install(
            &var_substitution,
            &mut session,
            &legacy.modules,
            &mut labels,
        )
        .unwrap();
    let label_installed = label_entry
        .install(
            &label_substitution,
            &mut session,
            &legacy.modules,
            &mut labels,
        )
        .unwrap();

    for (installed, entry) in [(&var_installed, var_entry), (&label_installed, label_entry)] {
        for member in &installed.schemes.members {
            let Def::Let {
                scheme: Some(actual),
                body,
                ..
            } = session.poly.defs.get(member.destination).unwrap()
            else {
                panic!("installed member must be closed");
            };
            let Def::Let {
                scheme: Some(expected),
                body: expected_body,
                ..
            } = legacy.session.poly.defs.get(member.destination).unwrap()
            else {
                unreachable!();
            };
            assert_eq!(
                format_scheme_with_stable_external_keys(
                    &session.poly.typ,
                    actual,
                    &entry.typed.external_references,
                ),
                format_scheme_with_stable_external_keys(
                    &legacy.session.poly.typ,
                    expected,
                    &entry.typed.external_references,
                ),
                "catalog scheme parity for {:?}",
                member.key,
            );
            assert_eq!(
                body.is_some(),
                expected_body.is_some(),
                "body parity for {:?}",
                member.key
            );
            assert_eq!(
                session
                    .poly
                    .effect_operations
                    .contains_key(&member.destination),
                legacy
                    .session
                    .poly
                    .effect_operations
                    .contains_key(&member.destination),
                "effect-operation parity for {:?}",
                member.key,
            );
            assert_eq!(
                session.poly.constructors.contains_key(&member.destination),
                legacy
                    .session
                    .poly
                    .constructors
                    .contains_key(&member.destination),
                "constructor parity for {:?}",
                member.key,
            );
            assert_eq!(
                session.poly.field_projections.contains(&member.destination),
                legacy
                    .session
                    .poly
                    .field_projections
                    .contains(&member.destination),
                "field-projection parity for {:?}",
                member.key,
            );
            assert!(session.is_finalized_template_def(member.destination));
        }
    }

    // Trace the real queue item at the lifecycle boundary. The target is already quantified at
    // the instant the first UseResolved item is observed, and no source-lowering lifecycle item
    // exists for any installed member.
    let target = var_installed.member_defs[0];
    let parent = var_installed.member_defs[1];
    let use_value = session.infer.fresh_type_var_at(TypeLevel::secondary());
    session.enqueue(AnalysisWork::Scc(SccInput::UseResolved {
        parent,
        target,
        use_value,
    }));
    let trace = session.work().iter().cloned().collect::<Vec<_>>();
    assert!(session.is_finalized_template_def(target));
    assert!(matches!(
        trace.first(),
        Some(AnalysisWork::Scc(SccInput::UseResolved { target: found, .. })) if *found == target
    ));
    assert!(!trace.iter().any(|work| matches!(
        work,
        AnalysisWork::Scc(SccInput::RegisterDef { def, .. }
            | SccInput::DefFinished { def }) if var_installed.member_defs.contains(def)
    )));
    while session.step() {}
    assert!(session.take_diagnostics().is_empty());
    assert!(legacy.errors.is_empty());
    assert_eq!(
        m1_runtime_output(&session.poly, legacy.subtype_provenance(), &labels),
        legacy_runtime,
    );
}

fn m1_runtime_output(
    arena: &poly::expr::Arena,
    provenance: &poly::provenance::SubtypeProvenanceSidecar,
    labels: &poly::dump::DumpLabels,
) -> String {
    let specialized = specialize::specialize_with_runtime_evidence(arena, provenance)
        .expect("M1 runtime parity specialization");
    let control = control_ir::lower(&specialized.program).expect("M1 control lowering");
    let plan = evidence_vm::build_plan(&control, &specialized.runtime_evidence);
    evidence_vm::run_program_with_plan(&control, &plan)
        .expect("M1 evidence VM run")
        .roots_text_with_labels(Some(labels))
}

fn assert_body_graph_parity(output: &BodyLowering, destinations: &[TypeDeclId], recursive: &str) {
    assert_eq!(destinations.len(), 2);
    let identity = template_for_instance(output, destinations[0]);
    let typed = TypedActTemplate::capture(identity, &output.session.poly).unwrap();
    let body = typed
        .capture_body(
            identity,
            &output.session.poly,
            &output.modules,
            &output.labels,
        )
        .unwrap_or_else(|error| {
            panic!(
                "{recursive} body capture {error:?}; labels={:?}",
                output.labels.def_labels().collect::<Vec<_>>()
            )
        });
    assert_eq!(body.members.len(), identity.value_members.len());
    let census = body.census();
    match recursive {
        "run" => {
            assert_eq!(census.effect_operations, 2);
            assert_eq!(census.constructors, 0);
            assert_eq!(census.nominal_record_shapes, 0);
            assert_eq!(census.external_catches, 0);
            assert!(census.external_refs > 0);
        }
        "return" => {
            assert_eq!(census.effect_operations, 1);
            assert_eq!(census.constructors, 1);
            assert_eq!(census.nominal_record_shapes, 1);
            assert_eq!(census.external_catches, 1);
        }
        _ => unreachable!(),
    }
    for destination in destinations {
        let substitution = output
            .modules
            .nominal_act_instance_substitution(*destination)
            .unwrap();
        let product = body.apply(substitution).unwrap();
        for member in &identity.value_members {
            let NominalActValueMemberKind::Operation { operation_path } = &member.kind else {
                continue;
            };
            let destination_def = substitution.def_map[&member.source];
            let detached_def = product
                .member_destinations
                .iter()
                .find_map(|(detached, destination)| {
                    (*destination == destination_def).then_some(*detached)
                })
                .unwrap();
            assert_eq!(
                product.arena.effect_operations[&detached_def].path,
                crate::namespace_path(&substitution.operation_path_map[operation_path]),
                "{} operation metadata path",
                member.name.0,
            );
        }
        for nominal in &identity.nominal_types {
            let destination_path =
                crate::namespace_path(&substitution.type_path_map[&nominal.source_path]);
            if nominal.role == NominalActTypeRole::NestedDeclaration {
                assert!(
                    product
                        .arena
                        .nominal_record_shapes
                        .contains_key(&destination_path)
                );
                assert!(
                    product
                        .arena
                        .constructors
                        .values()
                        .any(|constructor| constructor.owner_path == destination_path)
                );
            }
        }
        let legacy_identity = output
            .modules
            .nominal_act_identity_for_test(*destination)
            .unwrap();
        let legacy = typed
            .capture_body(
                &legacy_identity,
                &output.session.poly,
                &output.modules,
                &output.labels,
            )
            .unwrap();
        assert_eq!(product.census(), legacy.census());

        let source_member = identity
            .value_members
            .iter()
            .find(|member| member.name == Name(recursive.into()))
            .unwrap();
        let destination_member = substitution.def_map[&source_member.source];
        let detached_member = product
            .member_destinations
            .iter()
            .find_map(|(detached, destination)| {
                (*destination == destination_member).then_some(*detached)
            })
            .unwrap();
        assert!(
            product
                .arena
                .refs()
                .iter()
                .any(|target| *target == Some(detached_member))
                || product.arena.exprs().iter().any(|expr| {
                    let Expr::Catch(_, arms) = expr else {
                        return false;
                    };
                    arms.iter().any(|arm| {
                        arm.operation
                            .as_ref()
                            .is_some_and(|operation| operation.def == Some(detached_member))
                    })
                }),
            "{recursive} must retain an internal recursive/local-operation reference"
        );
    }
}

fn type_at_path(output: &BodyLowering, path: &[&str]) -> ModuleTypeDecl {
    let path = path
        .iter()
        .map(|segment| Name((*segment).into()))
        .collect::<Vec<_>>();
    output
        .modules
        .type_path_at(
            output.modules.root_id(),
            &path,
            ModuleOrder::from_index(u32::MAX),
        )
        .found()
        .expect("stable external type path")
}

fn assert_typed_scheme_template_round_trip(
    output: &BodyLowering,
    destinations: Vec<TypeDeclId>,
    expected_external_paths: &[Vec<&str>],
) {
    assert_eq!(destinations.len(), 2);
    let identity = template_for_instance(output, destinations[0]);
    let template = TypedActTemplate::capture(identity, &output.session.poly)
        .expect("finalized template schemes must form a closed detached graph");
    assert_eq!(template.members.len(), identity.value_members.len());
    assert!(template.types.node_len() > 0);
    assert!(template.types.node_len() < output.session.poly.typ.node_len());
    for expected in expected_external_paths {
        let expected = StableExternalReferenceKey::NominalPath(
            expected
                .iter()
                .map(|segment| (*segment).to_string())
                .collect(),
        );
        assert!(
            template.external_references.contains(&expected),
            "missing stable external type reference {expected:?}; actual={:?}",
            template.external_references,
        );
    }

    for destination in destinations {
        let substitution = output
            .modules
            .nominal_act_instance_substitution(destination)
            .expect("M1-1 substitution");
        let instantiated = template.apply(substitution).expect("shadow scheme import");
        assert_eq!(instantiated.destination_root_act, destination);
        assert_eq!(instantiated.members.len(), identity.value_members.len());
        for member in &instantiated.members {
            let Some(Def::Let {
                scheme: Some(actual),
                ..
            }) = output.session.poly.defs.get(member.destination)
            else {
                panic!("destination member must retain its legacy finalized scheme");
            };
            assert_eq!(
                format_scheme_with_stable_external_keys(
                    &instantiated.types,
                    &member.scheme,
                    &template.external_references,
                ),
                format_scheme_with_stable_external_keys(
                    &output.session.poly.typ,
                    actual,
                    &template.external_references,
                ),
                "shadow scheme diverged for {:?}",
                member.key,
            );
        }
    }
}

fn format_scheme_with_stable_external_keys(
    types: &poly::types::TypeArena,
    scheme: &poly::types::Scheme,
    external_references: &FxHashSet<StableExternalReferenceKey>,
) -> String {
    let external_nominal_paths = external_references
        .iter()
        .filter_map(|key| match key {
            StableExternalReferenceKey::NominalPath(path) => Some(path),
            StableExternalReferenceKey::ValuePath(_)
            | StableExternalReferenceKey::Operation { .. }
            | StableExternalReferenceKey::FieldMethod { .. }
            | StableExternalReferenceKey::Method { .. }
            | StableExternalReferenceKey::Constructor { .. } => None,
        })
        .collect::<Vec<_>>();
    let rewrite = |path: &[String]| {
        let stable = external_nominal_paths
            .iter()
            .copied()
            .find(|external| external.as_slice() == path)
            .or_else(|| {
                (path.len() == 1)
                    .then(|| {
                        external_nominal_paths
                            .iter()
                            .copied()
                            .filter(|external| external.last() == path.first())
                            .collect::<Vec<_>>()
                    })
                    .and_then(|matches| (matches.len() == 1).then(|| matches[0]))
            });
        stable
            .map(|stable| {
                std::iter::once("<external>".to_string())
                    .chain(stable.iter().cloned())
                    .collect()
            })
            .unwrap_or_else(|| path.to_vec())
    };
    poly::dump::format_scheme_with_path_rewriter(types, scheme, &rewrite)
}

fn assert_complete_nominal_shell_recording(output: &BodyLowering) {
    let var_ids = output.modules.synthetic_var_act_copy_ids();
    let label_ids = output.modules.synthetic_sub_label_act_copy_ids();
    assert_eq!(var_ids.len(), 2);
    assert_eq!(label_ids.len(), 2);
    assert_eq!(
        output.modules.nominal_act_instance_substitutions().count(),
        4
    );

    let var_template = template_for_instance(output, var_ids[0]);
    assert_eq!(var_template.nominal_types.len(), 1);
    assert_eq!(
        var_template.nominal_types[0].role,
        NominalActTypeRole::RootAct
    );
    assert_eq!(
        member_kind_names(var_template),
        FxHashSet::from_iter([
            "operation:get".to_string(),
            "operation:set".to_string(),
            "binding:var_ref".to_string(),
            "binding:run".to_string(),
        ])
    );

    let label_template = template_for_instance(output, label_ids[0]);
    assert_eq!(label_template.nominal_types.len(), 2);
    let nested_label = label_template
        .nominal_types
        .iter()
        .find(|identity| identity.role == NominalActTypeRole::NestedDeclaration)
        .expect("label_sub must close over its nested label type");
    assert_eq!(
        nested_label.source_path.segments.last(),
        Some(&Name("label".into()))
    );
    assert_eq!(
        member_kind_names(label_template),
        FxHashSet::from_iter([
            "operation:return".to_string(),
            "constructor:label".to_string(),
            "field-value:marker".to_string(),
            "field-ref:marker".to_string(),
            "binding:control_label".to_string(),
            "binding:sub".to_string(),
        ])
    );
    assert!(
        label_template
            .value_members
            .iter()
            .filter(|member| matches!(
                member.kind,
                NominalActValueMemberKind::Constructor
                    | NominalActValueMemberKind::FieldMethod { .. }
            ))
            .all(|member| member.owner == nested_label.source)
    );

    let mut all_destination_defs = FxHashSet::default();
    for destination in var_ids.into_iter().chain(label_ids) {
        let substitution = output
            .modules
            .nominal_act_instance_substitution(destination)
            .expect("every synthetic copy must record a shell substitution");
        let template = output
            .modules
            .nominal_act_template_identity(substitution.template_root_act)
            .expect("each substitution must retain its template identity");
        assert_complete_substitution(output, template, substitution);
        for def in substitution.def_map.values() {
            assert!(
                all_destination_defs.insert(*def),
                "separate instances must mint separate destination DefIds"
            );
        }
    }
}

fn template_for_instance(
    output: &BodyLowering,
    destination: TypeDeclId,
) -> &NominalActTemplateIdentity {
    let substitution = output
        .modules
        .nominal_act_instance_substitution(destination)
        .expect("synthetic instance substitution");
    output
        .modules
        .nominal_act_template_identity(substitution.template_root_act)
        .expect("synthetic template identity")
}

fn member_kind_names(identity: &NominalActTemplateIdentity) -> FxHashSet<String> {
    identity
        .value_members
        .iter()
        .map(|member| {
            let kind = match member.kind {
                NominalActValueMemberKind::Operation { .. } => "operation",
                NominalActValueMemberKind::Binding => "binding",
                NominalActValueMemberKind::Constructor => "constructor",
                NominalActValueMemberKind::FieldMethod {
                    receiver: TypeMethodReceiver::Value,
                } => "field-value",
                NominalActValueMemberKind::FieldMethod {
                    receiver: TypeMethodReceiver::Ref,
                } => "field-ref",
            };
            format!("{kind}:{}", member.name.0)
        })
        .collect()
}

fn assert_complete_substitution(
    output: &BodyLowering,
    template: &NominalActTemplateIdentity,
    substitution: &NominalActInstanceSubstitution,
) {
    assert_eq!(
        substitution.type_decl_map[&template.root_act],
        substitution.destination_root_act
    );
    assert_eq!(
        substitution.type_decl_map.len(),
        template.nominal_types.len()
    );
    assert_eq!(
        substitution.type_path_map.len(),
        template.nominal_types.len()
    );
    assert_eq!(substitution.def_map.len(), template.value_members.len());
    let operation_count = template
        .value_members
        .iter()
        .filter(|member| matches!(member.kind, NominalActValueMemberKind::Operation { .. }))
        .count();
    assert_eq!(substitution.operation_path_map.len(), operation_count);

    for nominal in &template.nominal_types {
        let destination = substitution.type_decl_map[&nominal.source];
        let destination_decl = output.modules.type_decl_by_id(destination).unwrap();
        assert_eq!(
            substitution.type_path_map[&nominal.source_path],
            output.modules.type_decl_path(&destination_decl)
        );
    }
    for member in &template.value_members {
        let actual = substitution.def_map[&member.source];
        let destination_owner = substitution.type_decl_map[&member.owner];
        let expected = expected_destination_member(output, substitution, member, destination_owner);
        assert_eq!(actual, expected, "{}", member.name.0);
        if let NominalActValueMemberKind::Operation { operation_path } = &member.kind {
            let destination_decl = output.modules.type_decl_by_id(destination_owner).unwrap();
            let mut expected_path = output.modules.type_decl_path(&destination_decl);
            expected_path.segments.push(member.name.clone());
            assert_eq!(
                substitution.operation_path_map[operation_path],
                expected_path
            );
        }
    }
}

fn expected_destination_member(
    output: &BodyLowering,
    substitution: &NominalActInstanceSubstitution,
    member: &crate::module_table::nominal_act_identity::NominalActTemplateValueIdentity,
    destination_owner: TypeDeclId,
) -> DefId {
    match member.kind {
        NominalActValueMemberKind::Operation { .. } | NominalActValueMemberKind::Binding => {
            let companion = output.modules.type_companion(destination_owner).unwrap();
            output.modules.value_decls(companion, &member.name)[0].def
        }
        NominalActValueMemberKind::Constructor => {
            substitution
                .type_decl_map
                .values()
                .filter_map(|owner| output.modules.type_companion(*owner))
                .flat_map(|module| output.modules.module_value_decls(module))
                .find(|decl| {
                    decl.name == member.name
                        && output
                            .modules
                            .constructor_by_def(decl.def)
                            .is_some_and(|constructor| constructor.owner == destination_owner)
                })
                .expect("destination constructor")
                .def
        }
        NominalActValueMemberKind::FieldMethod { receiver } => {
            output
                .modules
                .type_field_methods(destination_owner)
                .iter()
                .find(|method| method.name == member.name && method.receiver_kind == receiver)
                .expect("destination field method")
                .def
        }
    }
}

fn warm_case(
    prefix: &BodyLoweringPrefix,
    source: &str,
) -> (
    BodyLowering,
    act_copy_census::SyntheticActCopyCensusSnapshot,
) {
    let suffix = sources::load(vec![source_file(&[], source)]);
    let (output, census) = capture_synthetic_act_copy_census(|| {
        lower_loaded_files_with_prefix(prefix, &suffix).unwrap()
    });
    assert!(output.errors.is_empty(), "{source}\n{:?}", output.errors);
    (output, census)
}

fn cold_case(
    source: &str,
) -> (
    BodyLowering,
    act_copy_census::SyntheticActCopyCensusSnapshot,
) {
    let files = std_loaded(&format!("mod std;\n{source}"));
    let (output, census) =
        capture_synthetic_act_copy_census(|| lower_loaded_files(&files).unwrap());
    assert!(output.errors.is_empty(), "{source}\n{:?}", output.errors);
    (output, census)
}

fn assert_warm_cold_normalized_scheme_parity(
    cold: &BodyLowering,
    warm: &BodyLowering,
    kind: SyntheticActCopyKind,
) {
    let (cold_ids, warm_ids) = match kind {
        SyntheticActCopyKind::Var => (
            cold.modules.synthetic_var_act_copy_ids(),
            warm.modules.synthetic_var_act_copy_ids(),
        ),
        SyntheticActCopyKind::LabelSub => (
            cold.modules.synthetic_sub_label_act_copy_ids(),
            warm.modules.synthetic_sub_label_act_copy_ids(),
        ),
    };
    assert_eq!(cold_ids.len(), 1);
    assert_eq!(warm_ids.len(), 1);
    assert_eq!(
        normalized_legacy_scheme_view(cold, kind, cold_ids[0]),
        normalized_legacy_scheme_view(warm, kind, warm_ids[0]),
    );
}

fn assert_legacy_cell(cell: act_copy_census::SyntheticActCopyCensusCell, expected: usize) {
    assert_eq!(cell.not_attempted, expected);
    assert_eq!(cell.legacy_cst_lowerings, expected);
    assert_eq!(cell.eligible, 0);
    assert_eq!(cell.miss, 0);
    assert_eq!(cell.fallback, 0);
}

fn assert_instances_have_one_normalized_scheme_view(
    output: &BodyLowering,
    kind: SyntheticActCopyKind,
    ids: Vec<TypeDeclId>,
) {
    let views = ids
        .into_iter()
        .map(|id| normalized_legacy_scheme_view(output, kind, id))
        .collect::<Vec<_>>();
    let Some(expected) = views.first() else {
        panic!("fixture must contain a synthetic copy");
    };
    assert!(views.iter().all(|view| view == expected), "{views:#?}");
}

/// Binder names and the per-site nominal prefix are deliberately removed. M1-2 can compare its
/// detached scheme importer against this legacy baseline without depending on arena allocation.
fn normalized_legacy_scheme_view(
    output: &BodyLowering,
    kind: SyntheticActCopyKind,
    id: TypeDeclId,
) -> Vec<(String, String)> {
    let decl = output
        .modules
        .type_decl_by_id(id)
        .expect("synthetic act decl");
    let family = crate::namespace_path(&output.modules.type_decl_path(&decl));
    let companion = output
        .modules
        .type_companion(id)
        .expect("synthetic companion");
    let names: &[&str] = match kind {
        SyntheticActCopyKind::Var => &["get", "set", "var_ref", "run"],
        SyntheticActCopyKind::LabelSub => &["return", "label", "control_label", "sub"],
    };
    names
        .iter()
        .map(|name| {
            let def = output.modules.value_decls(companion, &Name((*name).into()))[0].def;
            let Some(Def::Let {
                scheme: Some(scheme),
                ..
            }) = output.session.poly.defs.get(def)
            else {
                panic!("{name} must have a finalized scheme");
            };
            let rewrite = |path: &[String]| {
                path.strip_prefix(family.as_slice())
                    .map(|suffix| {
                        std::iter::once("<synthetic-act>".to_string())
                            .chain(suffix.iter().cloned())
                            .collect()
                    })
                    .unwrap_or_else(|| path.to_vec())
            };
            (
                (*name).to_string(),
                poly::dump::format_scheme_with_path_rewriter(
                    &output.session.poly.typ,
                    scheme,
                    &rewrite,
                ),
            )
        })
        .collect()
}

fn std_prefix() -> BodyLoweringPrefix {
    let files = std_loaded("mod std;\n");
    let output = lower_loaded_files(&files).expect("lower M1-0 std prefix");
    assert!(output.errors.is_empty(), "prefix: {:?}", output.errors);
    output.into_prefix()
}

fn std_loaded(root: &str) -> Vec<LoadedFile> {
    sources::load(vec![
        source_file(&[], root),
        source_file(&["std"], "pub mod control;\n"),
        source_file(&["std", "control"], "pub mod var;\npub mod flow;\n"),
        source_file(&["std", "control", "var"], VAR_TEMPLATE),
        source_file(&["std", "control", "flow"], FLOW_TEMPLATE),
    ])
}

fn source_file(path: &[&str], source: &str) -> sources::SourceFile {
    sources::SourceFile {
        module_path: Path {
            segments: path.iter().map(|segment| Name((*segment).into())).collect(),
        },
        source: source.to_string(),
    }
}

fn mixed_source(count: usize) -> String {
    format!("{}\n{}", var_source(count), label_source(count))
}

fn var_source(count: usize) -> String {
    let mut source = "my var_case =\n".to_string();
    for index in 0..count {
        source.push_str(&format!("  my $v{index} = {index}\n"));
    }
    source.push_str("  0\nvar_case\n");
    source
}

fn label_source(count: usize) -> String {
    let mut source = String::new();
    for index in 0..count {
        source.push_str(&format!(
            "my label_case_{index} = sub 'label{index}: {index}\n"
        ));
    }
    source.push_str("label_case_0\n");
    source
}
