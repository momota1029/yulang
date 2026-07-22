use super::*;

fn collected(path: &str, module: &[&str], source: &str) -> CollectedSource {
    CollectedSource::new(
        PathBuf::from(path),
        path_from_segments(module),
        source.to_string(),
    )
}

fn collected_with_resolution_imports(
    path: &str,
    module: &[&str],
    source: &str,
    resolution_imports: Vec<sources::UseImport>,
) -> CollectedSource {
    CollectedSource::with_resolution_imports(
        PathBuf::from(path),
        path_from_segments(module),
        source.to_string(),
        resolution_imports,
    )
}

fn path_from_segments(segments: &[&str]) -> Path {
    Path {
        segments: segments
            .iter()
            .map(|segment| Name((*segment).to_string()))
            .collect(),
    }
}

const IMPLICIT_CAST_DIAGNOSTIC_SOURCE: &str = "my owner = 0\n\
my cast_one = 1\n\
my cast_two = 2\n\
my cast_three = 3\n";

fn implicit_cast_diagnostic_lowering() -> infer::lowering::BodyLowering {
    let loaded = sources::load(vec![sources::SourceFile {
        module_path: Path::default(),
        source: IMPLICIT_CAST_DIAGNOSTIC_SOURCE.to_string(),
    }]);
    let lowering = infer::lowering::lower_loaded_files(&loaded)
        .expect("implicit-cast diagnostic fixture should lower");
    assert!(lowering.errors.is_empty(), "{:?}", lowering.errors);
    lowering
}

fn labeled_def(labels: &poly::dump::DumpLabels, name: &str) -> poly::expr::DefId {
    labels
        .def_labels()
        .find_map(|(def, label)| {
            (label == name || label.ends_with(&format!(".{name}"))).then_some(def)
        })
        .unwrap_or_else(|| panic!("missing fixture definition label {name:?}"))
}

fn mono_con(path: &str) -> specialize::mono::Type {
    specialize::mono::Type::Con {
        path: vec![path.to_string()],
        args: Vec::new(),
    }
}

fn alias_import(name: &str, path: &[&str], route: sources::UsePathRoute) -> sources::UseImport {
    sources::UseImport::Alias {
        name: Name(name.to_string()),
        path: path_from_segments(path),
        route,
        version: None,
        anchor: None,
    }
}

fn write_current_realm_resolution_cache_entry(
    cache_root: &FsPath,
    main_path: &FsPath,
    main_source: &str,
    request: sources::UseImport,
    target_path: &FsPath,
    target_source_for_hash: &str,
) {
    let cache = crate::cache::ArtifactCache::new(cache_root);
    let source_realm = sources::local_realm_id(main_path);
    let main = CollectedSource::with_resolution_imports(
        main_path.to_path_buf(),
        Path::default(),
        main_source.to_string(),
        vec![request.clone()],
    );
    let target = CollectedSource::with_band_path(
        target_path.to_path_buf(),
        path_from_segments(&["helper"]),
        path_from_segments(&["helper"]),
        target_source_for_hash.to_string(),
    );
    let key = crate::cache::realm_resolution_cache_key(&main, &request);
    let artifact = crate::cache::CachedRealmResolutionArtifact {
        source_realm: source_realm.clone(),
        request,
        target: crate::cache::CachedRealmResolutionTarget {
            realm: source_realm.clone(),
            band_path: path_from_segments(&["helper"]),
            module_path: path_from_segments(&["helper"]),
            source_path: target_path.to_string_lossy().into_owned(),
            source_len: target_source_for_hash.len(),
            source_hash: crate::cache::source_file_hash(&target),
        },
    };

    cache
        .write_realm_resolution_artifact(&source_realm, key, &artifact)
        .unwrap();
}

#[test]
fn dump_mono_without_std_specializes_method_select_result() {
    let root = temp_root("dump-mono-method-select-result");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("main.yu"),
        "type User with:\n\
             \x20 our x.id = x\n\
             my u: User = 1\n\
             my keep x = x\n\
             keep(u.id)\n",
    )
    .unwrap();

    let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_mono_dump_contains(&output, ".id <method>");
    assert_mono_dump_contains(&output, "m0 = d3 : User -> User");
    assert_mono_dump_contains(&output, "m2 = d1 : User -> User");
}

#[test]
fn dump_mono_without_std_specializes_method_select_remaining_function() {
    let root = temp_root("dump-mono-method-select-function");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("main.yu"),
        "type User with:\n\
             \x20 our x.pick y = y\n\
             my u: User = 1\n\
             my keep x = x\n\
             keep(u.pick(1))\n",
    )
    .unwrap();

    let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_mono_dump_contains(&output, ".pick <method>");
    assert_mono_dump_contains(&output, "m0 = d3 : int -> int");
    assert_mono_dump_contains(&output, "m2 = d1 : User -> int -> int");
}

#[test]
fn dump_mono_without_std_specializes_attached_role_impl_methods() {
    let entry = write_main(
        "dump-mono-attached-role-impl-methods",
        "role Pick 'container 'key:\n\
             \x20 type value\n\
             \x20 our container.pick: 'key -> value\n\
             \n\
             struct pair 'left 'right { left: 'left, right: 'right } with:\n\
             \x20 impl Pick int:\n\
             \x20   type value = 'left\n\
             \x20   our p.pick _ = p.left\n\
             \n\
             \x20 impl Pick bool:\n\
             \x20   type value = 'right\n\
             \x20   our p.pick _ = p.right\n\
             \n\
             my p = pair { left: 10, right: false }\n\
             \n\
             (p.pick 0, p.pick true)\n",
    );

    let output = dump_mono_from_entry(entry).unwrap();

    assert_eq!(output.file_count, 1);
    assert_mono_dump_contains(&output, ".pick <method>");
    assert_mono_dump_contains(&output, "pair(int, bool) -> int -> int");
    assert_mono_dump_contains(&output, "pair(int, bool) -> bool -> bool");
}

#[test]
fn build_poly_without_std_records_attached_role_impl_method_mappings() {
    let entry = write_main(
        "poly-attached-role-impl-method-mappings",
        "role Pick 'container 'key:\n\
             \x20 type value\n\
             \x20 our container.pick: 'key -> value\n\
             \n\
             struct pair 'left 'right { left: 'left, right: 'right } with:\n\
             \x20 impl Pick int:\n\
             \x20   type value = 'left\n\
             \x20   our p.pick _ = p.left\n\
             \n\
             \x20 impl Pick bool:\n\
             \x20   type value = 'right\n\
             \x20   our p.pick _ = p.right\n",
    );

    let output = build_poly_from_sources(collect_local_sources(entry).unwrap()).unwrap();
    let candidates = output.arena.role_impls.candidates(&["Pick".to_string()]);

    assert_eq!(candidates.len(), 2);
    assert!(
        candidates
            .iter()
            .all(|candidate| candidate.methods.len() == 1)
    );
}

#[test]
fn build_poly_preserves_role_method_selection_and_candidate_source_spans() {
    let source = "role R 'a:\n    our a.foo: int\n\nimpl int: R:\n    our x.foo = 1\n\nimpl int: R:\n    our x.foo = 2\n\n1.foo\n";
    let mut output = build_poly_from_collected_sources(vec![collected("main.yu", &[], source)])
        .expect("role-method canary should lower");
    let error = match specialize::specialize(&output.arena, &output.subtype_provenance) {
        Ok(_) => panic!("ambiguous role-method canary should fail specialization"),
        Err(error) => error,
    };
    let (expr, candidates) = match &error {
        specialize::SpecializeError::AmbiguousTypeclassMethod {
            expr, candidates, ..
        } => (*expr, candidates.clone()),
        _ => panic!("expected ambiguous role-method error, got {error:?}"),
    };
    let poly::expr::Expr::Select(_, select) = output.arena.expr(poly::expr::ExprId(expr)) else {
        panic!("role-method error should retain its source Select expression");
    };
    let field_start = source.rfind(".foo").expect("source field token") + 1;
    let span = output
        .selection_provenance
        .selection_span(*select)
        .expect("resolved selection should retain its source span");

    assert_eq!(
        span.range,
        SourceRange {
            start: field_start,
            end: field_start + "foo".len(),
        }
    );
    assert_eq!(span.file, Path::default());
    assert_eq!(candidates.len(), 2);
    for candidate in candidates {
        let candidate = poly::expr::DefId(candidate.0);
        assert!(
            output
                .selection_provenance
                .definition_span(candidate)
                .is_some(),
            "candidate d{} should retain its declaration span",
            candidate.0
        );
    }

    let routed = specialize_route_error(error.clone(), &output);
    let RouteError::SpecializeDiagnostic { context, .. } = routed else {
        panic!("same-file role-method candidates should produce a ranged route error");
    };
    assert_eq!(context.range, span.range);
    assert_eq!(context.related.len(), 2);

    let candidates = match &error {
        specialize::SpecializeError::AmbiguousTypeclassMethod { candidates, .. } => candidates,
        _ => unreachable!(),
    };
    let selection_span = span.clone();
    let first_candidate = poly::expr::DefId(candidates[0].0);
    let second_candidate = poly::expr::DefId(candidates[1].0);
    let first_span = output
        .selection_provenance
        .definition_span(first_candidate)
        .unwrap()
        .clone();
    let mut cross_file_span = output
        .selection_provenance
        .definition_span(second_candidate)
        .unwrap()
        .clone();
    cross_file_span.file = path_from_segments(&["dependency"]);
    output.selection_provenance = infer::lowering::SelectionProvenanceTable::from_source_spans(
        [(*select, selection_span)],
        [
            (first_candidate, first_span.clone()),
            (second_candidate, cross_file_span.clone()),
        ],
    );
    let routed = specialize_route_error(error, &output);
    let RouteError::SpecializeDiagnostic { context, .. } = routed else {
        panic!("cross-file role-method candidates should retain a ranged route error");
    };
    assert_eq!(context.file, Path::default());
    assert_eq!(context.related.len(), 2);
    assert_eq!(context.related[0].file, first_span.file);
    assert_eq!(context.related[1].file, cross_file_span.file);
}

#[test]
fn specialize_missing_record_field_diagnostic_uses_selection_source_span() {
    let source = "{ a: 1 }.b\n";
    let mut output = build_poly_from_collected_sources(vec![collected("main.yu", &[], source)])
        .expect("missing-record-field canary should lower");
    let error = specialize::specialize(&output.arena, &output.subtype_provenance)
        .expect_err("missing-record-field canary should fail specialization");
    let select = match &error {
        specialize::SpecializeError::UnsatisfiedSubtype {
            origin:
                Some(specialize::UnsatisfiedSubtypeOrigin::MissingRecordField {
                    select: Some(select),
                    ..
                }),
            ..
        } => *select,
        _ => panic!("expected missing-record-field selection origin, got {error:?}"),
    };
    let field_start = source.find('b').expect("source field token");
    let span = output
        .selection_provenance
        .selection_span(select)
        .expect("selection should retain its source span")
        .clone();

    assert_eq!(
        span.range,
        SourceRange {
            start: field_start,
            end: field_start + 1,
        }
    );
    let routed = specialize_route_error(error.clone(), &output);
    let RouteError::SpecializeDiagnostic { context, .. } = routed else {
        panic!("missing-record-field selection should produce a ranged route error");
    };
    assert_eq!(context.range, span.range);
    assert!(context.related.is_empty());

    output.selection_provenance = infer::lowering::SelectionProvenanceTable::default();
    assert!(matches!(
        specialize_route_error(error, &output),
        RouteError::Specialize(specialize::SpecializeError::UnsatisfiedSubtype { .. })
    ));
}

#[test]
fn specialize_role_method_diagnostic_falls_back_for_non_select_origin() {
    let output = build_poly_from_collected_sources(vec![collected(
        "main.yu",
        &[],
        "my value = 1\nvalue\n",
    )])
    .expect("non-select fallback canary should lower");
    let expr = output
        .arena
        .exprs()
        .iter()
        .position(|expr| matches!(expr, poly::expr::Expr::Var(_)))
        .expect("canary should contain a Var expression") as u32;
    let error = specialize::SpecializeError::UnresolvedTypeclassMethod {
        expr,
        member: specialize::mono::DefId(0),
        receiver: specialize::mono::Type::Any,
    };

    assert!(matches!(
        specialize_route_error(error, &output),
        RouteError::Specialize(
            specialize::SpecializeError::UnresolvedTypeclassMethod { .. }
        )
    ));
}

#[test]
fn specialize_missing_implicit_cast_diagnostic_maps_optional_definition_owner() {
    let output = build_poly_from_collected_sources(vec![collected(
        "main.yu",
        &[],
        IMPLICIT_CAST_DIAGNOSTIC_SOURCE,
    )])
    .expect("implicit-cast diagnostic fixture should lower");
    let owner = labeled_def(&output.labels, "owner");
    let owner_span = output
        .selection_provenance
        .definition_span(owner)
        .expect("owner definition span")
        .clone();
    let error = specialize::SpecializeError::UnsatisfiedSubtype {
        lower: mono_con("int"),
        upper: mono_con("bool"),
        origin: Some(specialize::UnsatisfiedSubtypeOrigin::MissingImplicitCast {
            source: vec!["int".to_string()],
            target: vec!["bool".to_string()],
            owner: Some(owner),
        }),
    };

    let diagnostic = source_diagnostic_from_specialize_implicit_cast_error(&error, &output)
        .expect("missing-cast error should map to a source diagnostic");

    assert_eq!(
        diagnostic,
        SourceDiagnostic {
            severity: SourceDiagnosticSeverity::Error,
            code: Some("yulang.missing-implicit-cast".to_string()),
            label: None,
            file: Some(owner_span.file.clone()),
            range: Some(owner_span.range),
            message:
                "cannot use `int` where `bool` is required: no implicit cast from `int` to `bool`"
                    .to_string(),
            hint: Some(
                "declare a `cast` from `int` to `bool`, or check whether a different type was intended"
                    .to_string(),
            ),
            related: Vec::new(),
        }
    );
    assert_eq!(
        error.to_string(),
        "cannot use `int` where `bool` is required: no implicit cast from `int` to `bool`"
    );

    let without_owner = specialize::SpecializeError::UnsatisfiedSubtype {
        lower: mono_con("int"),
        upper: mono_con("bool"),
        origin: Some(specialize::UnsatisfiedSubtypeOrigin::MissingImplicitCast {
            source: vec!["int".to_string()],
            target: vec!["bool".to_string()],
            owner: None,
        }),
    };
    let diagnostic = source_diagnostic_from_specialize_implicit_cast_error(&without_owner, &output)
        .expect("unranged missing-cast error should still map");
    assert_eq!(diagnostic.file, None);
    assert_eq!(diagnostic.range, None);
    assert_eq!(
        diagnostic.code.as_deref(),
        Some("yulang.missing-implicit-cast")
    );
    assert_eq!(diagnostic.message, error.to_string());
    assert!(diagnostic.related.is_empty());
}

#[test]
fn specialize_ambiguous_implicit_cast_diagnostic_maps_candidates_without_raw_ids() {
    let mut output = build_poly_from_collected_sources(vec![collected(
        "main.yu",
        &[],
        IMPLICIT_CAST_DIAGNOSTIC_SOURCE,
    )])
    .expect("implicit-cast diagnostic fixture should lower");
    let owner = labeled_def(&output.labels, "owner");
    let candidates = [
        labeled_def(&output.labels, "cast_one"),
        labeled_def(&output.labels, "cast_two"),
        labeled_def(&output.labels, "cast_three"),
    ];
    let owner_span = output
        .selection_provenance
        .definition_span(owner)
        .expect("owner definition span")
        .clone();
    let candidate_spans = candidates.map(|candidate| {
        output
            .selection_provenance
            .definition_span(candidate)
            .expect("candidate definition span")
            .clone()
    });
    let mut labels = poly::dump::DumpLabels::new();
    labels
        .set_def_label(candidates[0], "example.cast_one")
        .set_def_label(candidates[1], "example.cast_two")
        .set_def_label(candidates[2], "example.cast_three");
    output.labels = labels;
    let error = specialize::SpecializeError::AmbiguousImplicitCast {
        actual: mono_con("int"),
        expected: mono_con("frac"),
        candidates: candidates.to_vec(),
        owner: Some(owner),
    };

    let diagnostic = source_diagnostic_from_specialize_implicit_cast_error(&error, &output)
        .expect("ambiguous-cast error should map to a source diagnostic");

    assert_eq!(
        diagnostic,
        SourceDiagnostic {
            severity: SourceDiagnosticSeverity::Error,
            code: Some("yulang.ambiguous-implicit-cast".to_string()),
            label: None,
            file: Some(owner_span.file),
            range: Some(owner_span.range),
            message:
                "implicit cast from `int` to `frac` is ambiguous: 3 visible declarations match"
                    .to_string(),
            hint: Some("declare or import only one matching `cast` for this pair".to_string(),),
            related: vec![
                SourceDiagnosticRelated {
                    message: "matching cast declaration: example.cast_one".to_string(),
                    file: candidate_spans[0].file.clone(),
                    range: candidate_spans[0].range,
                    origin: None,
                },
                SourceDiagnosticRelated {
                    message: "matching cast declaration: example.cast_two".to_string(),
                    file: candidate_spans[1].file.clone(),
                    range: candidate_spans[1].range,
                    origin: None,
                },
                SourceDiagnosticRelated {
                    message: "matching cast declaration: example.cast_three".to_string(),
                    file: candidate_spans[2].file.clone(),
                    range: candidate_spans[2].range,
                    origin: None,
                },
            ],
        }
    );
    assert_eq!(diagnostic.message, error.to_string());

    let mut labels = poly::dump::DumpLabels::new();
    labels
        .set_def_label(candidates[0], "example.cast_one")
        .set_def_label(candidates[1], "example.cast_two");
    output.labels = labels;
    let diagnostic = source_diagnostic_from_specialize_implicit_cast_error(&error, &output)
        .expect("candidate without a label should use the generic message");
    assert_eq!(diagnostic.related[2].message, "matching cast declaration");
    let rendered = std::iter::once(diagnostic.message.as_str())
        .chain(diagnostic.hint.as_deref())
        .chain(
            diagnostic
                .related
                .iter()
                .map(|related| related.message.as_str()),
        )
        .collect::<Vec<_>>()
        .join("\n");
    assert!(
        !rendered.contains(&format!("d{}", candidates[2].0)),
        "raw candidate id leaked into diagnostic:\n{rendered}"
    );
}

#[test]
fn build_poly_and_compiled_unit_from_collected_sources_share_lowering_output() {
    let files = vec![collected(
        "main.yu",
        &[],
        "pub struct Box { value: int }\nmy box = Box { value: 1 }\n",
    )];

    let output = build_poly_and_compiled_unit_from_collected_sources(files).unwrap();

    assert!(output.poly.errors.is_empty(), "{:?}", output.poly.errors);
    assert_eq!(output.compiled_unit.errors, output.poly.errors);
    assert_eq!(output.poly.file_count, 1);
    assert_eq!(output.compiled_unit.manifest.files.len(), 1);
    assert_eq!(
        output.compiled_unit.runtime.arena.defs.len(),
        output.poly.arena.defs.len()
    );
    assert_eq!(output.compiled_unit.runtime.labels, output.poly.labels);
    assert!(!output.poly.subtype_provenance.occurrences.is_empty());
    let restored = build_poly_from_compiled_unit_artifact(output.compiled_unit.clone());
    assert_eq!(restored.errors, output.poly.errors);
    assert_eq!(restored.file_count, output.poly.file_count);
    assert_eq!(restored.arena.defs.len(), output.poly.arena.defs.len());
    assert_eq!(restored.labels, output.poly.labels);
    assert!(restored.selection_provenance.is_empty());
    assert!(restored.subtype_provenance.occurrences.is_empty());
    assert!(
        output
            .compiled_unit
            .lowering
            .constructor_payloads
            .iter()
            .any(|entry| entry.value_path == vec!["Box"]
                && matches!(entry.payload, infer::CompiledConstructorPayload::Record(_)))
    );
}

#[test]
fn build_poly_from_compiled_unit_prefix_lowers_local_suffix_modules() {
    let prefix_files = vec![
        collected("prefix.yu", &[], "mod ops;\n"),
        collected("ops.yu", &["ops"], "pub x = 7\n"),
    ];
    let prefix = build_poly_and_compiled_unit_from_collected_sources(prefix_files)
        .unwrap()
        .compiled_unit;
    let prefix_defs = prefix
        .runtime
        .arena
        .defs
        .iter()
        .map(|(def, _)| def)
        .collect::<std::collections::HashSet<_>>();
    let suffix_files = vec![
        collected("main.yu", &[], "mod local;\nuse local::*\ny\n"),
        collected("local.yu", &["local"], "use ops::*\npub y = x\n"),
    ];

    let output =
        build_poly_from_compiled_unit_prefix_and_collected_sources(prefix, suffix_files).unwrap();
    assert!(output.errors.is_empty(), "{:?}", output.errors);
    assert_eq!(output.file_count, 4);
    assert!(!output.subtype_provenance.occurrences.is_empty());
    assert!(output.subtype_provenance.occurrences.iter().all(|(key, _)| {
        !matches!(
            key.owner,
            poly::provenance::TypeOccurrenceOwner::Definition(def) if prefix_defs.contains(&def)
        )
    }));
    let build = build_control_from_poly_output(&output).unwrap();
    let output = run_built_evidence_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [7]\n");
}

#[test]
fn compiled_unit_prefix_host_manifest_reaches_runtime_capability_boundary() {
    let prefix_files = vec![
        collected("prefix.yu", &[], "mod dep;\n"),
        collected(
            "dep.yu",
            &["dep"],
            "pub host act bridge:\n  pub call: () -> int\n",
        ),
    ];
    let prefix = build_poly_and_compiled_unit_from_collected_sources(prefix_files)
        .unwrap()
        .compiled_unit;
    let suffix_files = vec![collected("main.yu", &[], "use dep::*\nbridge::call()\n")];

    let output =
        build_poly_from_compiled_unit_prefix_and_collected_sources(prefix, suffix_files).unwrap();
    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let build = build_control_from_poly_output(&output).unwrap();
    let plan = evidence_vm::build_plan(&build.program, &build.runtime_evidence);
    let error =
        evidence_vm::run_program_with_plan_with_labels(&build.program, &plan, &build.labels)
            .expect_err("unregistered generated host operation should fail at capability boundary");

    match error {
        evidence_vm::RuntimeEvidenceRunError::UnsupportedHostCapability { path, .. } => {
            assert_eq!(path, vec!["dep".to_string(), "bridge".to_string()]);
        }
        other => panic!("expected unsupported host capability, got {other:?}"),
    }
}

#[test]
fn build_poly_from_non_root_source_unit_prefix_lowers_source_suffix() {
    let files = vec![
        collected("main.yu", &[], "mod a;\nuse a::*\nx\n"),
        collected("a.yu", &["a"], "mod b;\npub x = b::y\n"),
        collected("a/b.yu", &["a", "b"], "pub y = 7\n"),
    ];
    let units = source_compilation_units(&files);
    let b_unit = units.unit_for_file(2).unwrap();
    let prefix =
        crate::cache::compiled_unit_artifact_from_standalone_source_unit(&files, &units, b_unit)
            .unwrap();
    let suffix_files = vec![files[0].clone(), files[1].clone()];

    let output =
        build_poly_from_compiled_unit_prefix_and_collected_sources(prefix, suffix_files).unwrap();

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    assert_eq!(output.file_count, 3);
    let build = build_control_from_poly_output(&output).unwrap();
    let output = run_built_evidence_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [7]\n");
}

#[test]
fn source_compilation_units_order_local_module_dependencies_first() {
    let files = vec![
        collected("main.yu", &[], "mod a;\nx\n"),
        collected("a.yu", &["a"], "mod b;\npub x = b::y\n"),
        collected("a/b.yu", &["a", "b"], "pub y = 7\n"),
    ];

    let units = source_compilation_units(&files);

    assert_eq!(units.unit_for_file(0), Some(2));
    assert_eq!(units.unit_for_file(1), Some(1));
    assert_eq!(units.unit_for_file(2), Some(0));
    assert_eq!(units.units[0].files, vec![2]);
    assert_eq!(units.units[0].dependencies, Vec::<usize>::new());
    assert_eq!(units.units[1].files, vec![1]);
    assert_eq!(units.units[1].dependencies, vec![0]);
    assert_eq!(units.units[2].files, vec![0]);
    assert_eq!(units.units[2].dependencies, vec![1]);
}

#[test]
fn source_compilation_units_select_dependency_closed_available_prefix() {
    let files = vec![
        collected("main.yu", &[], "mod a;\nx\n"),
        collected("a.yu", &["a"], "mod b;\npub x = b::y\n"),
        collected("a/b.yu", &["a", "b"], "pub y = 7\n"),
    ];
    let units = source_compilation_units(&files);

    assert_eq!(
        units.dependency_closed_available_units(&[true, false, true]),
        vec![0]
    );
    assert_eq!(
        units.dependency_closed_available_units(&[true, true, false]),
        vec![0, 1]
    );
    assert_eq!(
        units.dependency_closed_available_units(&[true, true, true]),
        vec![0, 1, 2]
    );
}

#[test]
fn source_compilation_units_build_cache_selection() {
    let files = vec![
        collected("main.yu", &[], "mod a;\nx\n"),
        collected("a.yu", &["a"], "mod b;\npub x = b::y\n"),
        collected("a/b.yu", &["a", "b"], "pub y = 7\n"),
    ];
    let units = source_compilation_units(&files);

    let leaf_only = units.cache_selection(&[true, false, true]);
    assert_eq!(leaf_only.cached_units, vec![0]);
    assert_eq!(leaf_only.cached_files, vec![2]);
    assert_eq!(leaf_only.source_files, vec![0, 1]);

    let dependency_prefix = units.cache_selection(&[true, true, false]);
    assert_eq!(dependency_prefix.cached_units, vec![0, 1]);
    assert_eq!(dependency_prefix.cached_files, vec![1, 2]);
    assert_eq!(dependency_prefix.source_files, vec![0]);
}

#[test]
fn source_compilation_units_current_realm_import_depends_on_band_root() {
    let files = vec![
        collected_with_resolution_imports(
            "main.yu",
            &[],
            "use realm/helper::value\nmy x = value\n",
            vec![alias_import(
                "value",
                &["helper", "value"],
                sources::UsePathRoute::CurrentRealm { band_segments: 1 },
            )],
        ),
        collected("helper.yu", &["helper"], "pub value = 1\n"),
    ];

    let units = source_compilation_units(&files);
    let root_unit = units.unit_for_file(0).unwrap();
    let helper_unit = units.unit_for_file(1).unwrap();

    assert_ne!(root_unit, helper_unit);
    assert!(units.units[root_unit].dependencies.contains(&helper_unit));
}

#[test]
fn source_compilation_units_current_band_import_depends_on_existing_module_prefix() {
    let files = vec![
        collected("helper.yu", &["helper"], "pub value = 1\n"),
        collected_with_resolution_imports(
            "nested.yu",
            &["nested"],
            "use band::helper::value\npub x = value\n",
            vec![alias_import(
                "value",
                &["helper", "value"],
                sources::UsePathRoute::CurrentBand,
            )],
        ),
    ];

    let units = source_compilation_units(&files);
    let helper_unit = units.unit_for_file(0).unwrap();
    let nested_unit = units.unit_for_file(1).unwrap();

    assert_ne!(helper_unit, nested_unit);
    assert!(units.units[nested_unit].dependencies.contains(&helper_unit));
}

#[test]
fn source_compilation_units_slash_qualified_import_does_not_guess_local_prefix() {
    let files = vec![
        collected_with_resolution_imports(
            "main.yu",
            &[],
            "use ui/widget::a\nmy x = 1\n",
            vec![alias_import(
                "a",
                &["ui", "widget", "a"],
                sources::UsePathRoute::SlashQualified { prefix_segments: 2 },
            )],
        ),
        collected("ui/widget.yu", &["ui", "widget"], "pub a = 1\n"),
    ];

    let units = source_compilation_units(&files);
    let root_unit = units.unit_for_file(0).unwrap();
    let local_unit = units.unit_for_file(1).unwrap();

    assert!(!units.units[root_unit].dependencies.contains(&local_unit));
}

#[test]
fn source_unit_lowering_source_files_synthesize_parent_modules() {
    let files = vec![
        collected("main.yu", &[], "pub mod a;\nx\n"),
        collected("a.yu", &["a"], "mod b;\npub x = b::y\n"),
        collected("a/b.yu", &["a", "b"], "pub y = 7\n"),
    ];
    let units = source_compilation_units(&files);
    let b_unit = units.unit_for_file(2).unwrap();

    let lowering_files = source_unit_lowering_source_files(&files, &units, b_unit).unwrap();

    assert_eq!(lowering_files.len(), 3);
    assert_eq!(lowering_files[0].module_path, Path::default());
    assert_eq!(lowering_files[0].source, "pub mod a;\n");
    assert_eq!(
        lowering_files[1].module_path,
        Path {
            segments: vec![Name("a".to_string())],
        }
    );
    assert_eq!(lowering_files[1].source, "mod b;\n");
    assert_eq!(lowering_files[2].module_path, files[2].module_path);
    assert_eq!(lowering_files[2].source, files[2].source);

    let loaded = sources::load(lowering_files);
    let lowered = infer::lowering::lower_loaded_files(&loaded).unwrap();
    assert!(lowered.errors.is_empty(), "{:?}", lowered.errors);
    let y = lowered
        .modules
        .value_path_at(
            lowered.modules.root_id(),
            &[
                Name("a".to_string()),
                Name("b".to_string()),
                Name("y".to_string()),
            ],
            infer::ModuleOrder::from_index(u32::MAX),
        )
        .expect("synthetic parent modules should expose actual unit value");
    assert!(lowered.session.poly.defs.get(y).is_some());
}

#[cfg(unix)]
#[test]
fn run_evidence_with_std_specializes_attached_role_impl_methods() {
    let entry = write_main_with_std(
        "run-evidence-std-attached-role-impl-methods",
        "role Pick 'container 'key:\n\
             \x20 type value\n\
             \x20 our container.pick: 'key -> value\n\
             \n\
             struct pair 'left 'right { left: 'left, right: 'right } with:\n\
             \x20 impl Pick int:\n\
             \x20   type value = 'left\n\
             \x20   our p.pick _ = p.left\n\
             \n\
             \x20 impl Pick bool:\n\
             \x20   type value = 'right\n\
             \x20   our p.pick _ = p.right\n\
             \n\
             my p = pair { left: 10, right: false }\n\
             \n\
             (p.pick 0, p.pick true)\n",
    );

    let output = run_evidence_from_entry_with_std(entry).unwrap();

    assert_eq!(output.text, "run roots [(10, false)]\n");
    assert_eq!(output.errors, Vec::<String>::new());
}

#[test]
fn dump_poly_without_std_infers_local_constructor_application() {
    let root = temp_root("dump-poly-local-constructor");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("main.yu"),
        "enum opt 'a:\n    none\n    some 'a\n\nmy wrap x = opt::some x\n",
    )
    .unwrap();

    let output = dump_poly_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_dump_has_line_starting_with(&output, "  d2:\"opt.some\": 'a -> opt 'a = ");
    assert_dump_has_line_starting_with(&output, "my d3:wrap: 'a -> opt 'a = ");
    assert!(!output.text.contains("std::"));
}

#[test]
fn dump_poly_without_std_lowers_value_catch() {
    let root = temp_root("dump-poly-value-catch");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(root.join("main.yu"), "my handle x = catch x:\n    v -> v\n").unwrap();

    let output = dump_poly_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_dump_has_line_starting_with(&output, "my d0:handle: 'a -> 'a = ");
    assert_dump_contains(&output, "catch ");
    assert!(!output.text.contains("std::"));
}

#[test]
fn dump_poly_without_std_lowers_local_effect_handler() {
    let root = temp_root("dump-poly-local-effect-handler");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
            root.join("main.yu"),
            "act signal:\n    pub ping: () -> int\n\nmy handle x = catch x:\n    signal::ping(), k -> k 1\n    v -> v\n",
        )
        .unwrap();

    let output = dump_poly_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_dump_has_line_starting_with(&output, "my d2:handle: 'a -> 'a = ");
    assert_dump_contains(&output, "catch ");
    assert_dump_contains(&output, "\"signal.ping\"");
    assert!(!output.text.contains("std::"));
}

#[test]
fn dump_poly_without_std_lowers_file_handle_builtin_type() {
    let root = temp_root("dump-poly-file-handle");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("main.yu"),
        "act file:\n    my get: file_handle -> file_handle\n",
    )
    .unwrap();

    let output = dump_poly_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_dump_contains(&output, "file_handle -> [file] file_handle");
    assert_eq!(output.errors, Vec::<String>::new());
}

#[test]
fn dump_poly_without_std_keeps_annotated_shallow_handler_type_clean() {
    let root = temp_root("dump-poly-clean-shallow-handler");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
            root.join("main.yu"),
            "act signal:\n    pub ping: () -> int\n\nmy handle(x: [signal] _) = catch x:\n    signal::ping(), k -> k 1\n    v -> v\n",
        )
        .unwrap();

    let output = dump_poly_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_eq!(output.errors, Vec::<String>::new());
    assert_dump_has_line_starting_with(
        &output,
        "my d2:handle: 'a ['b & [signal; 'b]] -> ['b] 'a = ",
    );
    assert!(!output.text.contains("stack("));
    assert!(!output.text.contains("std::"));
}

#[test]
fn dump_poly_without_std_handles_local_effect_call() {
    let root = temp_root("dump-poly-handle-effect-call");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
            root.join("main.yu"),
            "act signal:\n    pub ping: () -> int\n\nmy handled() = catch signal::ping():\n    signal::ping(), k -> k 1\n",
        )
        .unwrap();

    let output = dump_poly_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_eq!(output.errors, Vec::<String>::new());
    assert_dump_has_line_starting_with(&output, "my d2:handled: () -> [signal] int = ");
    assert_dump_contains(&output, "catch ");
    assert_dump_contains(&output, "\"signal::ping\"");
    assert_dump_contains(&output, "\"signal.ping\"");
    assert_dump_contains(&output, ":k ->");
    assert!(!output.text.contains("std::"));
}

#[test]
fn dump_poly_without_std_reports_type_annotation_mismatch() {
    let root = temp_root("dump-poly-type-error");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(root.join("main.yu"), "my x: bool = 1\n").unwrap();

    let output = dump_poly_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_eq!(
        output.errors,
        vec!["type mismatch: int is not bool".to_string()]
    );
    assert!(!output.text.contains("std::"));
}

#[test]
fn dump_poly_raw_without_std_includes_type_and_expr_graphs() {
    let root = temp_root("dump-poly-raw");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(root.join("main.yu"), "my id x = x\n").unwrap();

    let output = dump_poly_raw_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_eq!(output.errors, Vec::<String>::new());
    assert_dump_contains(&output, "raw roots [d0:id]");
    assert_dump_contains(&output, "scheme {");
    assert_dump_contains(&output, "types:");
    assert_dump_contains(&output, "exprs {");
    assert_dump_contains(&output, "pats {");
    assert_dump_contains(&output, "Lambda(");
    assert!(!output.text.contains("std::"));
}

#[test]
fn collect_local_sources_with_std_reads_nearby_lib_std() {
    let _env = EnvVarGuard::unset(crate::stdlib::YULANG_STD_ENV);
    let root = temp_root("nearby-std");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("lib").join("std")).unwrap();
    fs::write(root.join("main.yu"), "my x = 1\n").unwrap();
    fs::write(root.join("lib").join("std.yu"), "mod prelude;\nmod var;\n").unwrap();
    fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();
    fs::write(root.join("lib").join("std").join("var.yu"), "my y = 2\n").unwrap();

    let files = collect_local_sources_with_std(root.join("main.yu")).unwrap();

    assert!(
        files
            .iter()
            .any(|file| file.module_path.segments == vec![Name("std".into())])
    );
    assert!(
        files
            .iter()
            .any(|file| file.module_path.segments
                == vec![Name("std".into()), Name("prelude".into())])
    );
    assert!(
        files
            .iter()
            .any(|file| file.module_path.segments == vec![Name("std".into()), Name("var".into())])
    );
    let root_source = files
        .iter()
        .find(|file| file.module_path.segments.is_empty())
        .unwrap();
    assert!(root_source.source.starts_with(IMPLICIT_PRELUDE_IMPORT));
    assert!(root_source.source.contains(IMPLICIT_STD_MODULE_DECL));
}

#[test]
fn collect_local_sources_with_std_prefers_yulang_std_over_nearby_lib_std() {
    let root = temp_root("env-std-priority");
    let _ = fs::remove_dir_all(&root);
    let nearby_root = root.join("lib");
    let env_root = root.join("env-lib");
    fs::create_dir_all(nearby_root.join("std")).unwrap();
    fs::create_dir_all(env_root.join("std")).unwrap();
    fs::write(root.join("main.yu"), "my x = 1\n").unwrap();
    fs::write(nearby_root.join("std.yu"), "mod prelude;\nmod nearby;\n").unwrap();
    fs::write(nearby_root.join("std").join("prelude.yu"), "").unwrap();
    fs::write(
        nearby_root.join("std").join("nearby.yu"),
        "my nearby_value = 1\n",
    )
    .unwrap();
    fs::write(env_root.join("std.yu"), "mod prelude;\nmod env;\n").unwrap();
    fs::write(env_root.join("std").join("prelude.yu"), "").unwrap();
    fs::write(env_root.join("std").join("env.yu"), "my env_value = 2\n").unwrap();

    let _env = EnvVarGuard::set_path(crate::stdlib::YULANG_STD_ENV, &env_root);
    let files = collect_local_sources_with_std(root.join("main.yu")).unwrap();

    assert!(
        files
            .iter()
            .any(|file| file.module_path.segments == vec![Name("std".into()), Name("env".into())])
    );
    assert!(
        !files.iter().any(
            |file| file.module_path.segments == vec![Name("std".into()), Name("nearby".into())]
        )
    );
}

#[test]
fn collect_source_text_with_embedded_std_uses_embedded_package() {
    let files =
        collect_source_text_with_embedded_std("playground.yu", "my x = 1\n".to_string()).unwrap();

    assert_eq!(files.len(), embedded_std_files().len() + 1);
    assert!(
        files
            .iter()
            .any(|file| file.module_path.segments == vec![Name("std".into())])
    );
    assert!(files.iter().any(|file| file.module_path.segments
        == vec![
            Name("std".into()),
            Name("control".into()),
            Name("nondet".into())
        ]));
    let root_source = files
        .iter()
        .find(|file| file.module_path.segments.is_empty())
        .unwrap();
    assert!(root_source.source.starts_with(IMPLICIT_PRELUDE_IMPORT));
    assert!(root_source.source.contains(IMPLICIT_STD_MODULE_DECL));
}

#[test]
fn collect_source_text_with_embedded_playground_std_uses_compact_package() {
    let files =
        collect_source_text_with_embedded_playground_std("playground.yu", "my x = 1\n".to_string())
            .unwrap();

    assert!(files.len() < embedded_std_files().len() + 1);
    assert!(
        files
            .iter()
            .any(|file| file.module_path.segments == vec![Name("std".into())])
    );
    assert!(files.iter().any(|file| file.module_path.segments
        == vec![
            Name("std".into()),
            Name("control".into()),
            Name("nondet".into())
        ]));
    assert!(!files.iter().any(|file| file.module_path.segments
        == vec![Name("std".into()), Name("io".into()), Name("file".into())]));
    let root_source = files
        .iter()
        .find(|file| file.module_path.segments.is_empty())
        .unwrap();
    assert!(root_source.source.starts_with(IMPLICIT_PRELUDE_IMPORT));
    assert!(root_source.source.contains(IMPLICIT_STD_MODULE_DECL));
}

#[test]
fn source_text_needs_full_embedded_std_for_playground_detects_full_only_std_modules() {
    assert!(source_text_needs_full_embedded_std_for_playground(
        "use std::text::parse::*\nword()\n"
    ));
    assert!(source_text_needs_full_embedded_std_for_playground(
        "std::text::config::parse \"x = 1\"\n"
    ));
    assert!(source_text_needs_full_embedded_std_for_playground(
        "use std::io::file::*\n1\n"
    ));
    assert!(source_text_needs_full_embedded_std_for_playground(
        "std::time::clock::now()\n"
    ));

    assert!(!source_text_needs_full_embedded_std_for_playground(
        "use std::control::nondet::*\neach(1..3).list\n"
    ));
    assert!(!source_text_needs_full_embedded_std_for_playground(
        "std::text::str::len \"abc\"\n"
    ));
}

#[test]
fn collect_source_text_with_embedded_std_imports_prelude_ops_before_root_parse() {
    let loaded =
        load_source_text_with_embedded_std("playground.yu", "my y = x<..\n".to_string()).unwrap();
    let root = loaded
        .iter()
        .find(|file| file.module_path.segments.is_empty())
        .unwrap();
    let root_cst = rowan::SyntaxNode::<parser::sink::YulangLanguage>::new_root(root.cst.clone());

    assert!(root.op_table.0.get("<..".as_bytes()).is_some());
    assert!(
        root_cst
            .descendants_with_tokens()
            .filter_map(rowan::NodeOrToken::into_token)
            .any(|token| token.kind() == parser::lex::SyntaxKind::Suffix && token.text() == "<..")
    );
}

#[test]
fn run_evidence_source_text_with_embedded_playground_std_runs_arithmetic() {
    let build =
        build_control_from_source_text_with_embedded_playground_std("playground.yu", "1 + 2\n")
            .unwrap();
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_evidence_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [3]\n");
}

#[test]
fn run_evidence_source_text_with_embedded_playground_std_runs_mixed_numeric_add() {
    let build =
        build_control_from_source_text_with_embedded_playground_std("playground.yu", "1 + 1.2\n")
            .unwrap();
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_evidence_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [2.2]\n");
}

#[test]
fn run_evidence_source_text_with_embedded_playground_std_formats_frac_roots() {
    let source = "\
std::num::frac::new 3 2
std::num::frac::new 4 2
";
    let build =
        build_control_from_source_text_with_embedded_playground_std("playground.yu", source)
            .unwrap();
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_evidence_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [3/2, 2]\n");
}

#[test]
fn run_evidence_source_text_with_embedded_playground_std_runs_struct_method_example() {
    let source = "\
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

point { x: 3, y: 4 } .norm2 + 1.12
";
    let build =
        build_control_from_source_text_with_embedded_playground_std("playground.yu", source)
            .unwrap();
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_evidence_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [26.12]\n");
}

#[test]
fn run_evidence_source_text_with_embedded_playground_std_runs_local_change_example() {
    let source = "\
{
    my $total = 0
    for x in 1..5:
        &total = $total + x
    $total
}
";
    let build =
        build_control_from_source_text_with_embedded_playground_std("playground.yu", source)
            .unwrap();
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_evidence_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [15]\n");
}

#[test]
fn run_evidence_source_text_with_embedded_playground_std_runs_list_update_example() {
    let source = yulang_fixture("regressions/runtime/list_update.yu");
    let build =
        build_control_from_source_text_with_embedded_playground_std("playground.yu", &source)
            .unwrap();
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_evidence_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [[2, 6, 4]]\n");
}

#[test]
fn run_evidence_source_text_with_embedded_playground_std_runs_junction_prelude_example() {
    let source = "if all [1, 2, 3] < any [2, 3, 4]:\n  1\nelse:\n  0\n";
    let build =
        build_control_from_source_text_with_embedded_playground_std("playground.yu", source)
            .unwrap();
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_evidence_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [1]\n");
}

#[test]
fn typed_playground_std_prefix_matches_loaded_route_for_list_update() {
    let source = yulang_fixture("regressions/runtime/list_update.yu");
    let loaded =
        load_source_text_with_embedded_playground_std("playground.yu", source.clone()).unwrap();
    let loaded_poly = build_poly_from_loaded_files(loaded).unwrap();
    let loaded_build = build_control_from_poly_output(&loaded_poly).unwrap();
    assert!(loaded_build.errors.is_empty(), "{:?}", loaded_build.errors);
    let loaded_output = run_built_evidence_on_vm_test_stack(loaded_build);

    let cached_build =
        build_control_from_source_text_with_embedded_playground_std("playground.yu", &source)
            .unwrap();
    assert!(cached_build.errors.is_empty(), "{:?}", cached_build.errors);
    let cached_output = run_built_evidence_on_vm_test_stack(cached_build);

    assert_eq!(cached_output.0, loaded_output.0);
    assert_eq!(cached_output.1, loaded_output.1);
}

#[test]
fn run_evidence_source_text_with_embedded_playground_std_runs_sub_return_example() {
    let source = "\
my first_over limit = sub:
    for x in 0..: if x * x > limit: return x
    0

first_over 40
";
    let build =
        build_control_from_source_text_with_embedded_playground_std("playground.yu", source)
            .unwrap();
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_evidence_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [7]\n");
}

#[test]
fn run_evidence_source_text_with_embedded_playground_std_runs_nondet_range_guard() {
    let source = "\
{
    my a = each 1..15
    my b = each a..15
    my c = each b..15
    guard: a * a + b * b == c * c
    (a, b, c)
}.list
";
    let build =
        build_control_from_source_text_with_embedded_playground_std("playground.yu", source)
            .unwrap();
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_evidence_on_vm_test_stack(build);

    assert_eq!(
        output.0,
        "run roots [[(3, 4, 5), (5, 12, 13), (6, 8, 10), (9, 12, 15)]]\n"
    );
}

#[test]
fn run_evidence_source_text_with_embedded_playground_std_runs_nondet_once_range() {
    let source = "\
{
    my a = each 1..
    my b = each a<..
    my c = each b<..

    guard: a * a + b * b == c * c

    (a, b, c)
} .once
";
    let build =
        build_control_from_source_text_with_embedded_playground_std("playground.yu", source)
            .unwrap();
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_evidence_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [opt::just((3, 4, 5))]\n");
}

#[test]
fn run_evidence_source_text_with_embedded_playground_std_replaces_strings() {
    let build = build_control_from_source_text_with_embedded_playground_std(
        "playground.yu",
        r#"("a-b-a".replace_once "a" "x", "a-b-a".replace "a" "x")"#,
    )
    .unwrap();
    assert!(build.file_count < embedded_std_files().len() + 1);
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_evidence_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [(\"x-b-a\", \"x-b-x\")]\n");
}

#[test]
fn run_evidence_source_text_with_embedded_std_runs_root_expression() {
    let output =
        run_evidence_from_source_text_with_embedded_std("playground.yu", "1 + 2\n").unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [3]\n");
}

#[cfg(not(target_arch = "wasm32"))]
#[test]
fn embedded_std_compiled_unit_artifact_persists_to_user_cache() {
    let root = temp_root("embedded-std-compiled-unit-cache");
    let cache_root = root.join("cache");
    let _cache = EnvVarGuard::set_path(crate::stdlib::YULANG_CACHE_DIR_ENV, &cache_root);
    let files =
        embedded_std_sources_with_root(FsPath::new("<embedded-std-cache-test>"), String::new());
    let loaded = load_collected_source_files(files.clone());

    let artifact = cached_embedded_compiled_unit_artifact(&files, &loaded).unwrap();
    let key = crate::cache::source_cache_key(&files);
    let cache = crate::cache::ArtifactCache::new(&cache_root);
    let cached = cache.read_compiled_unit_artifact(key).unwrap().unwrap();
    let cached_again = cached_embedded_compiled_unit_artifact(&files, &loaded).unwrap();

    assert_eq!(artifact.manifest, cached.manifest);
    assert_eq!(artifact.manifest, cached_again.manifest);
    assert_eq!(compiled_unit_artifact_count(&cache_root), 1);
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn run_evidence_source_text_with_embedded_std_runs_parse_word_to_end() {
    let build = build_control_from_source_text_with_embedded_std(
        "playground.yu",
        "use std::text::parse::*\n(run_str(\"abc\", 1, 1, word()), run_str(\"abc!\", 1, 1, word()))\n",
    )
    .unwrap();
    assert_eq!(build.file_count, embedded_std_files().len() + 1);
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_evidence_on_vm_test_stack(build);

    assert_eq!(
        output.0,
        "run roots [(result::ok(\"abc\"), result::ok(\"abc\"))]\n"
    );
}

#[test]
fn run_evidence_source_text_with_embedded_std_runs_user_error_fail_wrap() {
    let source = "\
error small_err:
  nope int

my boom n = fail (small_err::nope n)

(small_err::wrap: 7, small_err::wrap: boom 3)
";
    let build = build_control_from_source_text_with_embedded_std("playground.yu", source).unwrap();
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_evidence_on_vm_test_stack(build);

    assert_eq!(
        output.0,
        "run roots [(result::ok(7), result::err(small_err::nope(3)))]\n"
    );
}

#[test]
fn run_evidence_source_text_with_embedded_std_replaces_strings() {
    let build = build_control_from_source_text_with_embedded_std(
        "playground.yu",
        "\
(
  std::text::str::replace_once(\"a-b-a\", \"a\", \"x\"),
  std::text::str::replace(\"a-b-a\", \"a\", \"x\"),
  std::text::str::replace(\"aaa\", \"aa\", \"x\"),
  std::text::str::replace(\"abc\", \"\", \"x\")
)
",
    )
    .unwrap();
    assert_eq!(build.file_count, embedded_std_files().len() + 1);
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_evidence_on_vm_test_stack(build);

    assert_eq!(
        output.0,
        "run roots [(\"x-b-a\", \"x-b-x\", \"xa\", \"abc\")]\n"
    );
}

#[test]
fn check_poly_source_text_with_embedded_std_resolves_ref_lines_each_update_chain() {
    let output = check_poly_from_source_text_with_embedded_std(
        "playground.yu",
        r#"
use std::control::nondet::*
use std::control::var::*
use std::text::str::*

my path = std::text::path::of_bytes (std::text::str::to_bytes "/tmp/yulang-source-ref-lines-each-update-chain.txt")

my &doc = std::io::file::text path

(&doc.lines.each).update \line ->
    line.replace_once "todo:" "done:"
"#,
    )
    .unwrap();

    assert_check_contains(&output, "check-poly-embedded-std\n");
    assert_check_contains(&output, "  lowering errors: 0\n");
}

#[test]
fn run_evidence_source_text_with_embedded_std_resolves_value_lines_each_replace_once_chain() {
    let build = build_control_from_source_text_with_embedded_std(
        "playground.yu",
        r#"
use std::control::nondet::*
use std::text::str::*

my doc = "keep
todo: one
skip
todo: two"

((doc.lines.each).replace_once "todo:" "done:").list
"#,
    )
    .unwrap();
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_evidence_on_vm_test_stack(build);

    assert_eq!(
        output.0,
        "run roots [[\"keep\\n\", \"done: one\\n\", \"skip\\n\", \"done: two\"]]\n"
    );
}

#[test]
fn run_evidence_source_text_with_embedded_std_edits_parse_matches() {
    let build = build_control_from_source_text_with_embedded_std(
        "playground.yu",
        "\
use std::text::parse::*

my variable = rule { \"{{\" name = word \"}}\" }
my render({name}) = case name:
  \"name\" -> \"Yulang\"
  \"place\" -> \"world\"
  _ -> \"?\"

my template = edit(\"hello {{name}} from {{place}}!\", variable, render)

template
",
    )
    .unwrap();
    assert_eq!(build.file_count, embedded_std_files().len() + 1);
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_evidence_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [\"hello Yulang from world!\"]\n");
}

#[test]
fn run_evidence_source_text_with_embedded_std_replaces_plain_rule_literals() {
    let build = build_control_from_source_text_with_embedded_std(
        "playground.yu",
        "\
use std::text::parse::*

replace(\"hello hello\", ~\"hello\", \"hi\")
",
    )
    .unwrap();
    assert_eq!(build.file_count, embedded_std_files().len() + 1);
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_evidence_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [\"hi hi\"]\n");
}

#[test]
fn run_evidence_source_text_with_embedded_std_edits_capture_rule_literals() {
    let build = build_control_from_source_text_with_embedded_std(
        "playground.yu",
        "\
use std::text::parse::*

edit(\"users/alice/posts users/bob/posts\", ~\"users/:name/posts\", \\{name} -> name)
",
    )
    .unwrap();
    assert_eq!(build.file_count, embedded_std_files().len() + 1);
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_evidence_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [\"alice bob\"]\n");
}

#[test]
fn run_evidence_source_text_with_embedded_std_edits_capture_rule_literal_once() {
    let build = build_control_from_source_text_with_embedded_std(
        "playground.yu",
        "\
use std::text::parse::*

edit_once(\"port = 3000\\nport = 4000\", ~\"port = :value\", \\{value} -> \"port = 8080\")
",
    )
    .unwrap();
    assert_eq!(build.file_count, embedded_std_files().len() + 1);
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_evidence_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [\"port = 8080\\nport = 4000\"]\n");
}

#[test]
fn dump_mono_with_embedded_std_specializes_capture_rule_literal_result() {
    let output = dump_mono_from_source_text_with_embedded_std(
        "playground.yu",
        "\
use std::text::parse::*

edit(\"users/alice/posts users/bob/posts\", ~\"users/:name/posts\", \\{name} -> name)
",
    )
    .unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_mono_dump_contains(&output, "{name: std::text::str::str}");
    assert!(
        !output.text.contains("'open"),
        "mono dump kept unresolved open vars:\n{}",
        output.text
    );
}

#[test]
fn run_evidence_source_text_with_embedded_std_sequences_word_with_suffix() {
    let build = build_control_from_source_text_with_embedded_std(
        "playground.yu",
        "\
use std::text::parse::*

my route(): [parse char str_error (int, int) (str, int, int)] str =
  token(\"users/\")()
  my id = word()
  token(\"/posts\")()
  id

run_str(\"users/alice/posts\", 1, 1, route())
",
    )
    .unwrap();
    assert_eq!(build.file_count, embedded_std_files().len() + 1);
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_evidence_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [result::ok(\"alice\")]\n");
}

#[test]
fn run_evidence_source_text_with_embedded_std_choice_recovers_from_parse_fail() {
    let build = build_control_from_source_text_with_embedded_std(
        "playground.yu",
        "\
use std::text::parse::*

my fail_now() = parse::fail: str_error { line: 1, column: 1, unexpected: nil, expected: [\"x\"], message: [] }

run_str(\"abc\", 1, 1, choice(\\() -> fail_now(), \\() -> \"fallback\", ()))
",
    )
    .unwrap();
    assert_eq!(build.file_count, embedded_std_files().len() + 1);
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_evidence_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [result::ok(\"fallback\")]\n");
}

#[test]
fn run_evidence_source_text_with_embedded_std_repeats_parser_until_delimiter() {
    let build = build_control_from_source_text_with_embedded_std(
        "playground.yu",
        "\
use std::text::parse::*

(
  run_str(\"abc!\", 1, 1, some(satisfy(is_word))()),
  run_str(\"!\", 1, 1, many(satisfy(is_word))()),
  run_str(\"abc!\", 1, 1, many(satisfy(is_word))())
)
",
    )
    .unwrap();
    assert_eq!(build.file_count, embedded_std_files().len() + 1);
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_evidence_on_vm_test_stack(build);

    assert_eq!(
        output.0,
        "run roots [(result::ok([\"a\", \"b\", \"c\"]), result::ok([]), result::ok([\"a\", \"b\", \"c\"]))]\n"
    );
}

#[test]
fn run_evidence_source_text_with_embedded_std_repeats_parser_until_eof() {
    let build = build_control_from_source_text_with_embedded_std(
        "playground.yu",
        "\
use std::text::parse::*

(
  run_str(\"abc\", 1, 1, some(satisfy(is_word))()),
  run_str(\"\", 1, 1, many(satisfy(is_word))())
)
",
    )
    .unwrap();
    assert_eq!(build.file_count, embedded_std_files().len() + 1);
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_evidence_on_vm_test_stack(build);

    assert_eq!(
        output.0,
        "run roots [(result::ok([\"a\", \"b\", \"c\"]), result::ok([]))]\n"
    );
}

#[test]
fn run_evidence_source_text_with_embedded_std_matches_rule_literals_in_case() {
    let build = build_control_from_source_text_with_embedded_std(
        "playground.yu",
        "\
use std::text::parse::*

my route = case \"users/alice/posts\":
  ~\"users/:id/posts\" -> id
  _ -> \"miss\"

my leftover = case \"users/alice/posts!\":
  ~\"users/:id/posts\" -> id
  _ -> \"miss\"

my interp = case \"abc\":
  ~\"{name = word}\" -> name
  _ -> \"miss\"

my literal = case \"hello\":
  ~\"hello\" -> \"hit\"
  _ -> \"miss\"

my literal_leftover = case \"hello!\":
  ~\"hello\" -> \"hit\"
  _ -> \"miss\"

(route, leftover, interp, literal, literal_leftover)
",
    )
    .unwrap();
    assert_eq!(build.file_count, embedded_std_files().len() + 1);
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_evidence_on_vm_test_stack(build);

    assert_eq!(
        output.0,
        "run roots [(\"alice\", \"miss\", \"abc\", \"hit\", \"miss\")]\n"
    );
}

#[test]
fn run_evidence_source_text_with_embedded_std_matches_rule_exprs_in_case() {
    let build = build_control_from_source_text_with_embedded_std(
        "playground.yu",
        "\
use std::text::parse::*

my route = case \"users/alice/posts\":
  rule { \"users/\" id = word \"/posts\" } -> id
  _ -> \"miss\"

my leftover = case \"users/alice/posts!\":
  rule { \"users/\" id = word \"/posts\" } -> id
  _ -> \"miss\"

my literal = case \"hello\":
  rule { \"hello\" } -> \"hit\"
  _ -> \"miss\"

my literal_leftover = case \"hello!\":
  rule { \"hello\" } -> \"hit\"
  _ -> \"miss\"

my alt_left = case \"users/alice/posts\":
  rule { \"users/\" id = word \"/posts\" | \"groups/\" id = word \"/posts\" } -> id
  _ -> \"miss\"

my alt_right = case \"groups/admin/posts\":
  rule { \"users/\" id = word \"/posts\" | \"groups/\" id = word \"/posts\" } -> id
  _ -> \"miss\"

my alt_miss = case \"teams/admin/posts\":
  rule { \"users/\" id = word \"/posts\" | \"groups/\" id = word \"/posts\" } -> id
  _ -> \"miss\"

my alt_after_partial = case \"users/bob/comments\":
  rule { \"users/\" id = word \"/posts\" | \"users/\" id = word \"/comments\" } -> id
  _ -> \"miss\"

(route, leftover, literal, literal_leftover, alt_left, alt_right, alt_miss, alt_after_partial)
",
    )
    .unwrap();
    assert_eq!(build.file_count, embedded_std_files().len() + 1);
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_evidence_on_vm_test_stack(build);

    assert_eq!(
        output.0,
        "run roots [(\"alice\", \"miss\", \"hit\", \"miss\", \"alice\", \"admin\", \"miss\", \"bob\")]\n"
    );
}

#[cfg(unix)]
#[test]
fn run_with_std_formats_frac_roots() {
    let (mono, evidence) = run_with_std_main(
        "run-std-frac-roots",
        "std::num::frac::new 3 2\nstd::num::frac::new 4 2\n",
    );

    assert_eq!(mono.text, "run roots [3/2, 2]\n");
    assert_eq!(evidence.text, "run roots [3/2, 2]\n");
}

#[test]
fn run_evidence_source_text_with_embedded_std_imports_prelude_reexports() {
    let output =
        run_evidence_from_source_text_with_embedded_std("playground.yu", "each(1..3).list\n")
            .unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [[1, 2, 3]]\n");
}

#[test]
fn run_evidence_source_text_with_embedded_std_runs_junction_tour_example() {
    let output = run_with_vm_test_stack(|| {
        let output = run_evidence_from_source_text_with_embedded_std(
            "playground.yu",
            "if all [1, 2, 3] < any [2, 3, 4]:\n  1\nelse:\n  0\n",
        )
        .unwrap();
        (output.file_count, output.text)
    });

    assert_eq!(output.0, embedded_std_files().len() + 1);
    assert_eq!(output.1, "run roots [1]\n");
}

#[test]
fn run_evidence_source_text_with_embedded_std_keeps_std_instances_unmarked_between_roots() {
    let output = run_with_vm_test_stack(|| {
        let output = run_evidence_from_source_text_with_embedded_std(
            "playground.yu",
            "{\n  my a = each 1..3\n  a\n}.list\nif all [1, 2, 3] < any [3, 4, 5]:\n  1\nelse:\n  0\n",
        )
        .unwrap();
        (output.file_count, output.text)
    });

    assert_eq!(output.0, embedded_std_files().len() + 1);
    assert_eq!(output.1, "run roots [[1, 2, 3], 1]\n");
}

#[test]
fn run_evidence_source_text_with_embedded_std_forces_effectful_block_let() {
    let output = run_evidence_from_source_text_with_embedded_std(
        "playground.yu",
        "{\n  my a = each 1..3\n  (a, 1)\n}.list\n",
    )
    .unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [[(1, 1), (2, 1), (3, 1)]]\n");
}

#[test]
fn run_evidence_source_text_with_embedded_std_runs_nondet_triples() {
    let output = run_with_vm_test_stack(|| {
        let output = run_evidence_from_source_text_with_embedded_std(
            "playground.yu",
            "{\n  my a = each 1..15\n  my b = each a..15\n  my c = each b..15\n  guard: a * a + b * b == c * c\n  (a, b, c)\n}.list\n",
        )
        .unwrap();
        (output.file_count, output.text)
    });

    assert_eq!(output.0, embedded_std_files().len() + 1);
    assert_eq!(
        output.1,
        "run roots [[(3, 4, 5), (5, 12, 13), (6, 8, 10), (9, 12, 15)]]\n"
    );
}

#[test]
fn run_evidence_source_text_with_embedded_std_runs_nondet_once_triple() {
    let output = run_with_vm_test_stack(|| {
        let output = run_evidence_from_source_text_with_embedded_std(
            "playground.yu",
            "({\n  my a = each 1..\n  my b = each a<..\n  my c = each b<..\n  guard: a * a + b * b == c * c\n  (a, b, c)\n} .once).show\n",
        )
        .unwrap();
        (output.file_count, output.text)
    });

    assert_eq!(output.0, embedded_std_files().len() + 1);
    assert_eq!(output.1, "run roots [\"just (3, 4, 5)\"]\n");
}

#[test]
fn dump_poly_fixture_data_position_effect_function_public_signature_hides_stack_evidence() {
    let entry = write_main(
        "dump-poly-data-position-effect-function-public-type",
        &yulang_fixture("regressions/effect/data_position_effect_function_public_signature.yu"),
    );
    let output = dump_poly_from_entry(entry).unwrap();

    let ty = assert_public_signature_type_hides_stack_evidence(&output, "box.handle");
    assert_eq!(
        ty, "box('a & 'b, 'c) -> ('c -> ['b] 'c) -> ['b, 'a] ()",
        "data-position effectful function should keep public residuals and hide private evidence"
    );
    assert!(
        !ty.contains("tick"),
        "handled data-position effect should not appear in the public method signature:\n{ty}"
    );
}

#[test]
fn dump_poly_fixture_nested_data_position_effect_function_public_signature_hides_stack_evidence() {
    let entry = write_main(
        "dump-poly-nested-data-position-effect-function-public-type",
        &yulang_fixture(
            "regressions/effect/nested_data_position_effect_function_public_signature.yu",
        ),
    );
    let output = dump_poly_from_entry(entry).unwrap();

    let ty = assert_public_signature_type_hides_stack_evidence(&output, "demo.cell.apply");
    assert_eq!(
        ty, "demo::cell('a & 'b, 'c) -> ('c -> ['b] 'c) -> ['b, 'a] ()",
        "nested data-position effectful function should keep public residuals and hide private evidence"
    );
    assert!(
        !ty.contains("pulse"),
        "handled nested data-position effect should not appear in the public method signature:\n{ty}"
    );
}

#[cfg(unix)]
#[test]
fn dump_poly_fixture_nested_handler_contract_public_signatures() {
    let entry = write_main_with_std(
        "dump-poly-nested-handler-contract-public-types",
        &yulang_fixture("regressions/effect/nested_handler_contract_public_signatures.yu"),
    );
    let output = dump_poly_from_entry_with_std(entry).unwrap();

    assert_eq!(
        assert_public_signature_type_hides_stack_evidence(&output, "all_paths"),
        "'a [flip; 'b] -> ['b] std::data::list::list 'a",
        "all_paths should capture flip and keep the residual row public"
    );

    assert_eq!(
        assert_public_signature_type_hides_stack_evidence(&output, "total_amount"),
        "'a [amount; 'b] -> ['b] std::data::list::list 'a",
        "total_amount should capture amount and keep the residual row public"
    );

    assert_eq!(
        assert_public_signature_type_hides_stack_evidence(&output, "compose"),
        "('a ['b] -> ['c] 'd) -> ('e ['f] -> ['b] 'a) -> 'e ['f] -> ['c] 'd",
        "explicit compose contracts should expose g(x) surface effects to f without empty visibility evidence"
    );
}

#[test]
fn dump_poly_fixture_public_type_display_order_signatures() {
    let entry = write_main(
        "dump-poly-public-type-display-order-signatures",
        &yulang_fixture("regressions/effect/public_type_display_order_signatures.yu"),
    );
    let output = dump_poly_from_entry(entry).unwrap();

    assert_public_signature_type_eq(&output, "apply", "('a -> ['b] 'c) -> 'a -> ['b] 'c");
    assert_public_signature_type_eq(
        &output,
        "twice",
        "(('a | 'b) ['c#0[Empty]] -> ['c#0[Empty] & 'd#0[Empty]] 'b & 'e) -> 'a -> ['d] 'e#0",
    );
    assert_public_signature_type_eq(
        &output,
        "compose1",
        "('a ['b] -> ['c] 'd) -> ('e -> ['b] 'a) -> 'e -> ['c] 'd",
    );
    assert_public_signature_type_eq(
        &output,
        "compose2",
        "('a ['b#0[Empty]] -> ['c] 'd) -> ('e -> ['b#0[Empty]] 'a) -> 'e -> ['c#0] 'd#0",
    );
}

#[test]
fn public_type_projection_matches_dump_public_signature_for_contract_type() {
    let entry = write_main(
        "public-type-projection-dump-parity",
        "pub id x = x\npub answer = id 42\nanswer\n",
    );
    let dump = dump_poly_from_entry(&entry).unwrap();
    let build = build_poly_from_sources(collect_local_sources(&entry).unwrap()).unwrap();
    let scheme = public_scheme_for_symbol(&build, "id");

    let public = poly::dump::format_scheme_public(&build.arena.typ, scheme);

    assert_eq!(public.text, dump_public_signature_type(&dump, "id"));
    assert_eq!(public.redactions, 0);
}

#[test]
fn dump_poly_fixture_sub_return_callback_public_signature_keeps_callback_effect() {
    let entry = write_fixture_with_fake_std(
        "dump-poly-sub-return-callback-public-signature",
        "support/fake_std/control_flow_io.yu",
        "regressions/effect/sub_return_callback_public_signature.yu",
    );
    let output = dump_poly_from_entry(entry).unwrap();

    assert_eq!(
        assert_public_signature_type_hides_stack_evidence(&output, "g"),
        "(int -> ['a] any) -> ['a] int",
        "sub-return helper should expose callback effects instead of swallowing them"
    );
    assert_public_signature_type_eq(&output, "run", "int");
}

#[cfg(unix)]
#[test]
fn dump_poly_std_ref_update_public_signature_hides_stack_evidence() {
    let entry = write_main_with_std("dump-poly-std-ref-update-public-type", "1\n");
    let parent_output = dump_poly_from_entry_with_std_in_module(&entry, "std.control.var").unwrap();
    let output = dump_poly_from_entry_with_std_in_module(entry, "std.control.var.ref").unwrap();

    let ref_ty =
        assert_public_signature_type_hides_stack_evidence(&parent_output, "std.control.var.ref");
    assert_eq!(
        ref_ty,
        "{get: () -> ['a] 'b, update_effect: () -> [std::control::var::ref_update 'b; 'c] ()} -> std::control::var::ref('a | 'c, 'b)",
        "ref constructor should expose update_effect as a ref_update residual without private evidence"
    );

    let ty =
        assert_public_signature_type_hides_stack_evidence(&output, "std.control.var.ref.update");
    assert_eq!(
        ty, "std::control::var::ref('a & 'b, 'c) -> ('c -> ['b] 'c) -> ['b, 'a] ()",
        "ref.update should keep ref residual and callback residual in the public signature"
    );
    assert!(
        !ty.contains("std::control::var::ref_update"),
        "ref.update handler evidence should not appear in the public signature:\n{ty}"
    );
}

#[cfg(unix)]
#[test]
fn dump_poly_std_str_ref_mutating_method_public_signatures_are_clean() {
    let entry = write_main_with_std("dump-poly-std-str-ref-mutating-public-type", "1\n");
    let output = dump_poly_from_entry_with_std_in_module(entry, "std.text.str.str").unwrap();

    let replace_once_ty = assert_public_signature_type_hides_stack_evidence(
        &output,
        "std.text.str.str.replace_once!",
    );
    assert_eq!(
        replace_once_ty,
        "std::control::var::ref 'a std::text::str::str -> std::text::str::str -> std::text::str::str -> ['a] ()",
        "ref str replace_once should expose only the receiver residual effect"
    );
    assert!(
        !replace_once_ty.contains("std::control::var::ref_update"),
        "ref str replace_once should not expose ref_update handler evidence:\n{replace_once_ty}"
    );

    let trim_ty =
        assert_public_signature_type_hides_stack_evidence(&output, "std.text.str.str.trim!");
    assert_eq!(
        trim_ty, "std::control::var::ref 'a std::text::str::str -> ['a] ()",
        "ref str trim should expose only the receiver residual effect"
    );
    assert!(
        !trim_ty.contains("std::control::var::ref_update"),
        "ref str trim should not expose ref_update handler evidence:\n{trim_ty}"
    );
}

#[cfg(unix)]
#[test]
fn dump_poly_std_parse_choice_public_signature_hides_stack_evidence() {
    let entry = write_main_with_std("dump-poly-std-parse-choice-public-type", "1\n");
    let output = dump_poly_from_entry_with_std_in_module(entry, "std.text.parse").unwrap();

    assert_eq!(
        assert_public_signature_type_hides_stack_evidence(&output, "std.text.parse.choice"),
        "(() -> [std::text::parse::parse 'a 'b 'c 'd] 'e) -> (() -> [std::text::parse::parse 'a 'b 'c 'd] 'e) -> () -> [std::text::parse::parse 'a 'b 'c 'd] 'e where 'b: std::text::parse::ParseError(item = 'f, pos = 'g)",
        "choice should share the parser effect family between both parser arguments and the result"
    );
}

#[cfg(unix)]
#[test]
fn dump_poly_std_flow_for_in_public_signature_hides_stack_evidence() {
    let entry = write_main_with_std("dump-poly-std-flow-for-in-public-type", "1\n");
    let output = dump_poly_from_entry_with_std_in_module(entry, "std.control.flow.loop").unwrap();

    assert_eq!(
        assert_public_signature_type_hides_stack_evidence(&output, "std.control.flow.loop.for_in"),
        "'a -> ('b -> [std::control::flow::loop; 'c] any) -> ['c] () where 'a: std::data::fold::Fold(item = 'b)",
        "for_in should keep callback loop effect local and expose only the callback residual"
    );
}

#[cfg(unix)]
#[test]
fn dump_poly_std_nondet_once_act_method_uses_deep_handler_effect() {
    let entry = write_main_with_std("dump-poly-std-nondet-once-type", "1\n");
    let output =
        dump_poly_from_entry_with_std_in_module(entry, "std.control.nondet.nondet").unwrap();

    assert_eq!(
        assert_public_signature_type_containing_hides_stack_evidence(&output, "#act-method:once"),
        "'a [std::control::nondet::nondet; 'b] -> ['b] std::data::opt::opt 'a",
        "once act method should expose nondet with an independent residual, not a shallow handler type"
    );
}

#[cfg(unix)]
#[test]
fn dump_poly_std_nondet_list_act_method_uses_deep_handler_effect() {
    let entry = write_main_with_std("dump-poly-std-nondet-list-type", "1\n");
    let output =
        dump_poly_from_entry_with_std_in_module(entry, "std.control.nondet.nondet").unwrap();

    assert_eq!(
        assert_public_signature_type_containing_hides_stack_evidence(&output, "#act-method:list"),
        "'a [std::control::nondet::nondet; 'b] -> ['b] std::data::list::list 'a",
        "list act method should expose nondet with an independent residual, not a shallow handler type"
    );
}

#[cfg(unix)]
#[test]
fn dump_poly_public_contract_spine_modules_hide_private_stack_evidence() {
    let entry = write_main_with_std("dump-poly-public-contract-spine-clean-types", "1\n");
    for module in [
        "std.control.var.ref",
        "std.control.flow.loop",
        "std.control.nondet.nondet",
        "std.text.parse",
    ] {
        let output = dump_poly_from_entry_with_std_in_module(&entry, module).unwrap();
        assert_all_public_signature_types_hide_stack_evidence(&output, module);
    }
}

#[test]
fn run_evidence_source_text_with_embedded_std_runs_poly_variant_list() {
    let output =
        run_evidence_from_source_text_with_embedded_std("playground.yu", "[:a, :b]\n").unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [[a, b]]\n");
}

#[test]
fn run_evidence_source_text_with_embedded_std_indexes_strings_by_grapheme_cluster() {
    let source = "\
my s = \"e\u{301}🇯🇵👨‍👩‍👧‍👦!\"
(
    s.len,
    std::text::str::index_raw s 0,
    std::text::str::index_range_raw s 0 3,
    std::text::str::splice_raw s 1 3 \"X\"
)
";
    let output = run_evidence_from_source_text_with_embedded_std("playground.yu", source).unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(
        output.text,
        "run roots [(4, \"e\\u{301}\", \"e\\u{301}🇯🇵👨\\u{200d}👩\\u{200d}👧\\u{200d}👦\", \"e\\u{301}X!\")]\n"
    );
}

#[test]
fn run_evidence_source_text_with_embedded_std_indexes_string_lines_by_range() {
    let source = "\
my s = \"a👨‍👩‍👧‍👦\\nβ\\n\"
(
    std::text::str::line_count s,
    std::text::str::index_range s (std::text::str::line_range s 1)
)
";
    let output = run_evidence_from_source_text_with_embedded_std("playground.yu", source).unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [(3, \"β\\n\")]\n");
}

#[test]
fn run_evidence_source_text_with_embedded_std_roundtrips_string_bytes() {
    let source = "\
my b = std::text::str::to_bytes \"hé\"
my e = std::text::str::to_bytes \"é\"
my slice = std::text::bytes::index_range b (std::data::range::range 1 3)
(
    std::text::bytes::len b,
    std::text::bytes::index_raw b 0,
    std::text::bytes::to_utf8_lossy slice,
    std::text::bytes::eq slice e,
    std::text::bytes::to_utf8_lossy (std::text::bytes::concat (std::text::str::to_bytes \"h\") e)
)
";
    let output = run_evidence_from_source_text_with_embedded_std("playground.yu", source).unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [(3, 104, \"é\", true, \"hé\")]\n");
}

#[test]
fn run_evidence_source_text_with_embedded_std_reuses_record_default_function() {
    let output = run_evidence_from_source_text_with_embedded_std(
        "playground.yu",
        "my f({x = 1}) = x\n[f {}, f {x: 2}]\n",
    )
    .unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [[1, 2]]\n");
}

#[test]
fn run_evidence_source_text_with_embedded_std_record_default_accepts_float_field() {
    let source = "\
our box {width = 1, height = width} =
    width * height

box {width: 1.2}
";
    let output = run_evidence_from_source_text_with_embedded_std("playground.yu", source).unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [1.44]\n");
}

#[test]
fn run_evidence_fixture_lowers_sub_syntax_return() {
    let entry = write_source_with_fake_std(
        "run-evidence-sub-syntax-return",
        "support/fake_std/control_flow_io.yu",
        "sub:\n  return 1\n",
    );
    let output = run_evidence_from_entry(entry).unwrap();

    assert_eq!(output.file_count, 1);
    assert_eq!(output.text, "run roots [1]\n");
}

#[test]
fn run_evidence_source_text_with_embedded_std_lowers_labeled_sub_syntax_return() {
    let output = run_evidence_from_source_text_with_embedded_std(
        "playground.yu",
        "my x = sub 'outer:\n  'outer.return 1\nx\n",
    )
    .unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [1]\n");
}

#[test]
fn run_evidence_source_text_with_embedded_std_lowers_root_labeled_sub_syntax_return() {
    let output = run_evidence_from_source_text_with_embedded_std(
        "playground.yu",
        "sub 'outer:\n  'outer.return 1\n",
    )
    .unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [1]\n");
}

#[test]
fn run_evidence_fixture_lowers_sub_lambda_return() {
    let entry = write_source_with_fake_std(
        "run-evidence-sub-lambda-return",
        "support/fake_std/control_flow_io.yu",
        "my f = \\sub x -> return x\nf 7\n",
    );
    let output = run_evidence_from_entry(entry).unwrap();

    assert_eq!(output.file_count, 1);
    assert_eq!(output.text, "run roots [7]\n");
}

#[test]
fn run_evidence_source_text_with_embedded_std_lowers_labeled_sub_lambda_return() {
    let output = run_evidence_from_source_text_with_embedded_std(
        "playground.yu",
        "my f = \\sub 'out x -> 'out.return x\nf 7\n",
    )
    .unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [7]\n");
}

#[test]
fn run_evidence_source_text_with_embedded_std_labeled_sub_lambda_handles_inner_return() {
    let output = run_evidence_from_source_text_with_embedded_std(
        "playground.yu",
        "sub 'outer:\n  my f = \\sub 'inner x -> 'inner.return x\n  f 7\n",
    )
    .unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [7]\n");
}

#[test]
fn run_evidence_source_text_with_embedded_std_labeled_sub_lambda_lets_outer_return_escape() {
    let output = run_evidence_from_source_text_with_embedded_std(
        "playground.yu",
        "sub 'outer:\n  my f = \\sub 'inner x -> 'outer.return x\n  f 7\n  'outer.return 1\n",
    )
    .unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [7]\n");
}

#[test]
fn run_evidence_fixture_keeps_sub_syntax_hygiene() {
    let entry = write_source_with_fake_std(
        "run-evidence-sub-syntax-hygiene",
        "support/fake_std/control_flow_io.yu",
        "our g h = sub:\n  h 0\n  return 1\n\nsub:\n  g \\i -> return i\n  return 2\n",
    );
    let output = run_evidence_from_entry(entry).unwrap();

    assert_eq!(output.file_count, 1);
    assert_eq!(output.text, "run roots [0]\n");
}

#[test]
fn run_evidence_fixture_keeps_sub_return_through_for_callback_if() {
    let entry = write_fixture_with_fake_std(
        "run-evidence-sub-return-through-for-callback",
        "support/fake_std/control_flow_io.yu",
        "regressions/effect/sub_return_through_for_callback.yu",
    );
    let output = run_evidence_from_entry(entry).unwrap();

    assert_eq!(output.file_count, 1);
    assert_eq!(output.text, "run roots [0]\n");
}

#[test]
fn run_evidence_source_text_with_embedded_std_keeps_repeated_callback_hygiene() {
    let output = run_with_vm_test_stack(|| {
        let output = run_evidence_from_source_text_with_embedded_std(
            "playground.yu",
            "pub act tick:\n\
             \x20 pub ping: () -> ()\n\
             \n\
             pub strip_tick(action: [tick] _) = catch action:\n\
             \x20 tick::ping(), k -> strip_tick(k ())\n\
             \x20 v -> v\n\
             \n\
             pub count_tick(action: [tick] _) = catch action:\n\
             \x20 tick::ping(), k -> 1 + count_tick(k ())\n\
             \x20 _ -> 0\n\
             \n\
             pub bounce(n: int, f, x) =\n\
             \x20 if n == 0:\n\
             \x20 \x20 x\n\
             \x20 else:\n\
             \x20 \x20 strip_tick: f (f (bounce(n - 1, f, x)))\n\
             \n\
             count_tick:\n\
             \x20 bounce(3, \\x -> {\n\
             \x20 \x20 tick::ping()\n\
             \x20 \x20 x + 1\n\
             \x20 }, 0)\n",
        )
        .unwrap();
        (output.file_count, output.text)
    });

    assert_eq!(output.0, embedded_std_files().len() + 1);
    assert_eq!(output.1, "run roots [6]\n");
}

#[test]
fn dump_mono_fixture_specializes_for_callback_if_before_println() {
    let entry = write_fixture_with_fake_std(
        "dump-mono-for-callback-before-println",
        "support/fake_std/control_flow_io.yu",
        "regressions/effect/for_callback_residual_with_println.yu",
    );
    let output = dump_mono_from_entry(entry).unwrap();

    assert_eq!(output.file_count, 1);
    assert_mono_dump_contains(&output, "std::control::flow::sub(int)");
    assert_mono_dump_contains(&output, ": int -> unit");
}

#[test]
fn dump_poly_fixture_keeps_for_callback_residual_generic() {
    let entry = write_fixture_with_fake_std(
        "dump-poly-for-callback-residual",
        "support/fake_std/control_flow_io.yu",
        "regressions/effect/for_callback_residual_with_println.yu",
    );
    let output = dump_poly_from_entry(entry).unwrap();

    assert_eq!(output.file_count, 1);
    let g = output
        .text
        .lines()
        .find(|line| line.contains(":g: "))
        .expect("g should be dumped");
    assert!(
        g.contains("g: (int -> ['") && g.contains("] any) -> ['") && g.contains("] int = "),
        "g should keep the callback residual generic:\n{g}"
    );
    assert!(
        !g.contains("std::control::flow::loop::redo"),
        "for_in loop redo must not be baked into g's public callback type:\n{g}"
    );
}

#[test]
fn dump_poly_fixture_keeps_forwarded_effectful_parameter_deep() {
    let entry = write_main(
        "dump-poly-forwarded-effectful-parameter",
        &yulang_fixture("regressions/effect/effectful_parameter_forwarding.yu"),
    );
    let output = dump_poly_from_entry(entry).unwrap();

    let h = output
        .text
        .lines()
        .find(|line| line.contains(":h: "))
        .expect("h should be dumped");
    assert!(
        h.contains("[handled; '"),
        "forwarding should keep handled in the result effect:\n{h}"
    );
    assert!(
        !h.contains("& [handled;"),
        "plain forwarding must not become a shallow handler type:\n{h}"
    );
}

#[test]
fn check_poly_source_text_with_embedded_std_reports_type_error() {
    let output =
        check_poly_from_source_text_with_embedded_std("playground.yu", "my x: int = true\n")
            .unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_check_contains(&output, "check-poly-embedded-std\n");
    assert_eq!(
        output
            .diagnostics
            .iter()
            .map(|diagnostic| (diagnostic.label.as_deref(), diagnostic.message.as_str()))
            .collect::<Vec<_>>(),
        vec![(Some("x"), "type mismatch: bool is not int")]
    );
}

#[test]
fn dump_poly_with_std_uses_nearby_prelude() {
    let root = temp_root("dump-poly-with-std");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("lib").join("std")).unwrap();
    fs::write(root.join("main.yu"), "my x = 1\n").unwrap();
    fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
    fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

    let output = dump_poly_from_entry_with_std(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 3);
    assert!(output.text.contains("my d"));
    assert!(output.text.contains(": int = "));
}

#[test]
fn check_poly_std_reports_summary_and_type_errors_without_dumping_defs() {
    let root = temp_root("check-poly-std");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("lib").join("std")).unwrap();
    fs::write(root.join("main.yu"), "my x = 1\n").unwrap();
    fs::write(root.join("lib").join("std.yu"), "mod prelude;\nmod foo;\n").unwrap();
    fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();
    fs::write(
        root.join("lib").join("std").join("foo.yu"),
        "my good x = x\nmy bad: bool = 1\n",
    )
    .unwrap();

    let output = check_poly_from_entry_with_std(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 4);
    assert_check_contains(&output, "check-poly-std\n");
    assert_check_contains(&output, "files: 4\n");
    assert_check_contains(&output, "timing:\n");
    assert_check_contains(&output, "  load.cst_parse: ");
    assert_check_contains(&output, "  load.rowan_nodes: ");
    assert_check_contains(&output, "  load.rowan_tokens: ");
    assert_check_contains(&output, "  infer.type_var_count: ");
    assert_check_contains(&output, "  constraint.epoch: ");
    assert_check_contains(&output, "  infer.row_tail_var_count: ");
    assert_check_contains(&output, "  infer.type_node_count: ");
    assert_check_contains(&output, "  constraint.edge_count: ");
    assert_check_contains(&output, "  constraint.replay_generated: ");
    assert_check_contains(&output, "  constraint.replay_enqueued: ");
    assert_check_contains(&output, "  constraint.replay_accepted: ");
    assert_check_contains(&output, "  constraint.replay_duplicate: ");
    assert_check_contains(&output, "  constraint.replay_trivial: ");
    assert_check_contains(&output, "  constraint.replay_prefiltered: ");
    assert_check_contains(
        &output,
        "  constraint.replay_prefilter_duplicate_exact_key: ",
    );
    assert_check_contains(
        &output,
        "  constraint.replay_prefilter_duplicate_var_var_key: ",
    );
    assert_check_contains(
        &output,
        "  constraint.replay_prefilter_duplicate_terminal_erased: ",
    );
    assert_check_contains(
        &output,
        "  constraint.replay_prefilter_duplicate_row_tail: ",
    );
    assert_check_contains(&output, "  constraint.max_replay_inputs: ");
    assert_check_contains(&output, "  constraint.max_replay_generated: ");
    assert_check_contains(&output, "  constraint.max_replay_enqueued: ");
    assert_check_contains(&output, "  constraint.max_replay_accepted: ");
    assert_check_contains(&output, "  constraint.max_replay_duplicate: ");
    assert_check_contains(&output, "  constraint.max_replay_trivial: ");
    assert_check_contains(&output, "  constraint.max_replay_prefiltered: ");
    assert_check_contains(&output, "  analysis.scc_component_count: ");
    assert_check_contains(
        &output,
        "  analysis.quantify_generalize_max_iterations_per_root: ",
    );
    assert_check_contains(&output, "  analysis.generalize_top_restart_root: ");
    assert_check_contains(
        &output,
        "  analysis.generalize_top_restart_total_restarts: ",
    );
    assert_check_contains(
        &output,
        "  analysis.generalize_top_restart_constraint_epoch_delta: ",
    );
    assert_check_contains(
        &output,
        "  analysis.generalize_top_restart_role_epoch_delta: ",
    );
    assert_check_contains(
        &output,
        "  analysis.generalize_top_restart_merge_restarts: ",
    );
    assert_check_contains(&output, "  analysis.generalize_top_restart_role_restarts: ");
    assert_check_contains(
        &output,
        "  analysis.generalize_top_restart_dominance_role_constraints: ",
    );
    assert_check_contains(
        &output,
        "  analysis.generalize_top_restart_dominance_interval_inputs: ",
    );
    assert_check_contains(
        &output,
        "  analysis.generalize_top_restart_role_resolve_inputs: ",
    );
    assert_check_contains(&output, "  analysis.generalize_compact_shadow_requests: ");
    assert_check_contains(&output, "  analysis.generalize_compact_shadow_hits: ");
    assert_check_contains(&output, "  analysis.generalize_compact_cache_requests: ");
    assert_check_contains(&output, "  analysis.generalize_compact_cache_hits: ");
    assert_check_contains(&output, "  analysis.generalize_role_view_shadow_requests: ");
    assert_check_contains(&output, "  analysis.generalize_role_view_shadow_hits: ");
    assert_check_contains(&output, "  analysis.generalize_dominance_interval_inputs: ");
    assert_check_contains(
        &output,
        "  analysis.generalize_dominance_polarity_occurrences: ",
    );
    assert_check_contains(
        &output,
        "  analysis.generalize_dominance_subtype_constraints: ",
    );
    assert_check_contains(&output, "  analysis.role_demand_count: ");
    assert_check_contains(&output, "  analysis.role_resolve_candidate_scans: ");
    assert_check_contains(&output, "  analysis.role_resolve_candidate_cache_hits: ");
    assert_check_contains(&output, "summary:\n");
    assert_check_contains(&output, "  lowering errors: 1\n");
    assert_check_contains(
        &output,
        "std::foo: values 2 typed 2 missing_schemes 0 bodyless 1",
    );
    assert!(
        !output.text.contains("missing schemes:\n"),
        "failed lowering defs should be closed with poisoned schemes:\n{}",
        output.text
    );
    assert_check_contains(&output, "bodyless declarations:\n");
    assert_check_contains(&output, "std.foo.bad\n");
    assert_eq!(
        output
            .diagnostics
            .iter()
            .map(|diagnostic| (diagnostic.label.as_deref(), diagnostic.message.as_str()))
            .collect::<Vec<_>>(),
        vec![(Some("std.foo.bad"), "type mismatch: int is not bool")]
    );
    assert!(!output.text.contains(" = Let {"));
}

#[cfg(unix)]
#[test]
fn analyze_entry_source_uses_in_memory_root_source() {
    let root = temp_root("analyze-entry-source");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("lib").join("std")).unwrap();
    fs::write(root.join("main.yu"), "my x: int = 1\n").unwrap();
    fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
    fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

    let output = analyze_entry_source_with_std_options(
        root.join("main.yu"),
        "my x: int = true\n",
        &StdSourceOptions {
            std_root: Some(root.join("lib")),
        },
    )
    .unwrap();

    assert_eq!(output.file_count, 3);
    assert_eq!(
        output.diagnostics,
        vec![SourceDiagnostic {
            severity: SourceDiagnosticSeverity::Error,
            code: Some("yulang.type-mismatch".to_string()),
            label: Some("x".to_string()),
            file: Some(Path::default()),
            range: Some(SourceRange {
                start: IMPLICIT_PRELUDE_IMPORT.len() + IMPLICIT_STD_MODULE_DECL.len() + 3,
                end: IMPLICIT_PRELUDE_IMPORT.len() + IMPLICIT_STD_MODULE_DECL.len() + 4,
            }),
            message: "type mismatch: bool is not int".to_string(),
            hint: None,
            related: vec![
                SourceDiagnosticRelated {
                    message: "expected type comes from this type annotation: int".to_string(),
                    file: Path::default(),
                    range: SourceRange {
                        start: IMPLICIT_PRELUDE_IMPORT.len() + IMPLICIT_STD_MODULE_DECL.len() + 6,
                        end: IMPLICIT_PRELUDE_IMPORT.len() + IMPLICIT_STD_MODULE_DECL.len() + 9,
                    },
                    origin: Some(SourceDiagnosticRelatedOrigin::TypeAnnotation),
                },
                SourceDiagnosticRelated {
                    message: "actual type comes from this expression: bool".to_string(),
                    file: Path::default(),
                    range: SourceRange {
                        start: IMPLICIT_PRELUDE_IMPORT.len() + IMPLICIT_STD_MODULE_DECL.len() + 12,
                        end: IMPLICIT_PRELUDE_IMPORT.len() + IMPLICIT_STD_MODULE_DECL.len() + 16,
                    },
                    origin: Some(SourceDiagnosticRelatedOrigin::Expression),
                },
            ],
        }]
    );
}

#[test]
fn analysis_missing_implicit_cast_diagnostic_maps_optional_definition_span() {
    let lowering = implicit_cast_diagnostic_lowering();
    let owner = labeled_def(&lowering.labels, "owner");
    let owner_span = lowering
        .modules
        .def_source_span(owner)
        .expect("owner definition span")
        .clone();
    let error = infer::lowering::BodyLoweringError::Analysis(
        infer::analysis::AnalysisDiagnostic::MissingImplicitCast {
            source: vec!["example".to_string(), "Source".to_string()],
            target: vec!["example".to_string(), "Target".to_string()],
            source_span: Some(owner_span.clone()),
            explanation: Some(infer::analysis::DiagnosticTypeExplanation {
                source: vec!["example".to_string(), "Source".to_string()],
                target: vec!["example".to_string(), "Target".to_string()],
                derivation: infer::analysis::DiagnosticTypeDerivation::OneSidedReplayPair,
                related_sites: vec![
                    infer::analysis::DiagnosticTypeExplanationSite {
                        role: infer::analysis::DiagnosticTypeExplanationSiteRole::InferredExpression,
                        source_span: owner_span.clone(),
                    },
                    infer::analysis::DiagnosticTypeExplanationSite {
                        role: infer::analysis::DiagnosticTypeExplanationSiteRole::RequiredApplicationCallee,
                        source_span: owner_span.clone(),
                    },
                ],
                body_use: None,
            }),
        },
    );

    let diagnostic = source_diagnostic_from_body_lowering_error(
        &error,
        &lowering.modules,
        &lowering.labels,
        None,
        None,
    );

    assert_eq!(
        diagnostic,
        SourceDiagnostic {
            severity: SourceDiagnosticSeverity::Error,
            code: Some("yulang.missing-implicit-cast".to_string()),
            label: None,
            file: Some(owner_span.file.clone()),
            range: Some(owner_span.range),
            message: "cannot use `example::Source` where `example::Target` is required: no implicit cast from `example::Source` to `example::Target`".to_string(),
            hint: Some(
                "declare a `cast` from `example::Source` to `example::Target`, or check whether a different type was intended"
                    .to_string(),
            ),
            related: vec![
                SourceDiagnosticRelated {
                    message: "type `example::Source` is inferred from this argument".to_string(),
                    file: owner_span.file.clone(),
                    range: owner_span.range,
                    origin: Some(SourceDiagnosticRelatedOrigin::Expression),
                },
                SourceDiagnosticRelated {
                    message: "this callee requires an argument compatible with `example::Target`"
                        .to_string(),
                    file: owner_span.file.clone(),
                    range: owner_span.range,
                    origin: Some(SourceDiagnosticRelatedOrigin::Expression),
                },
            ],
        }
    );

    let without_span = infer::lowering::BodyLoweringError::Analysis(
        infer::analysis::AnalysisDiagnostic::MissingImplicitCast {
            source: vec!["example".to_string(), "Source".to_string()],
            target: vec!["example".to_string(), "Target".to_string()],
            source_span: None,
            explanation: None,
        },
    );
    let diagnostic = source_diagnostic_from_body_lowering_error(
        &without_span,
        &lowering.modules,
        &lowering.labels,
        None,
        None,
    );
    assert_eq!(diagnostic.file, None);
    assert_eq!(diagnostic.range, None);
    assert_eq!(
        diagnostic.code.as_deref(),
        Some("yulang.missing-implicit-cast")
    );
    assert_eq!(
        diagnostic.message,
        format_body_lowering_error(&without_span)
    );
    assert!(diagnostic.related.is_empty());
}

#[test]
fn analysis_missing_implicit_cast_renders_body_requirement_after_call_sites() {
    let lowering = implicit_cast_diagnostic_lowering();
    let owner = labeled_def(&lowering.labels, "owner");
    let span = lowering
        .modules
        .def_source_span(owner)
        .expect("owner definition span")
        .clone();
    let error = infer::lowering::BodyLoweringError::Analysis(
        infer::analysis::AnalysisDiagnostic::MissingImplicitCast {
            source: vec!["int".to_string()],
            target: vec!["bool".to_string()],
            source_span: Some(span.clone()),
            explanation: Some(infer::analysis::DiagnosticTypeExplanation {
                source: vec!["int".to_string()],
                target: vec!["bool".to_string()],
                derivation: infer::analysis::DiagnosticTypeDerivation::OneSidedReplayPair,
                related_sites: vec![
                    infer::analysis::DiagnosticTypeExplanationSite {
                        role: infer::analysis::DiagnosticTypeExplanationSiteRole::InferredExpression,
                        source_span: span.clone(),
                    },
                    infer::analysis::DiagnosticTypeExplanationSite {
                        role: infer::analysis::DiagnosticTypeExplanationSiteRole::RequiredApplicationCallee,
                        source_span: span.clone(),
                    },
                ],
                body_use: Some(infer::analysis::DiagnosticTypeExplanationSite {
                    role: infer::analysis::DiagnosticTypeExplanationSiteRole::RequiredByBodyUse(
                        infer::analysis::BodyRequirementDiagnosticKind::BooleanCondition,
                    ),
                    source_span: span,
                }),
            }),
        },
    );
    let diagnostic = source_diagnostic_from_body_lowering_error(
        &error,
        &lowering.modules,
        &lowering.labels,
        None,
        None,
    );
    assert_eq!(
        diagnostic
            .related
            .iter()
            .map(|related| related.message.as_str())
            .collect::<Vec<_>>(),
        vec![
            "type `int` is inferred from this argument",
            "this callee requires an argument compatible with `bool`",
            "this parameter is required to be `bool` because it is used as this condition",
        ]
    );
}

#[test]
fn embedded_std_missing_cast_explains_unannotated_parameter_condition() {
    let output = check_poly_from_source_text_with_embedded_std(
        "playground.yu",
        "my f(x) = if x: 1 else: 2\nf(42)\n",
    )
    .expect("missing casts are reported as diagnostics");
    let [diagnostic] = output.diagnostics.as_slice() else {
        panic!("expected one missing-cast diagnostic: {:#?}", output.diagnostics);
    };
    assert_eq!(
        diagnostic.code.as_deref(),
        Some("yulang.missing-implicit-cast")
    );
    assert_eq!(
        diagnostic
            .related
            .iter()
            .map(|related| related.message.as_str())
            .collect::<Vec<_>>(),
        vec![
            "type `int` is inferred from this argument",
            "this callee requires an argument compatible with `bool`",
            "this parameter is required to be `bool` because it is used as this condition",
        ]
    );
    let diagnostic_source = output
        .diagnostic_source
        .as_ref()
        .expect("root source is available for related ranges");
    let body_range = diagnostic.related[2].range;
    assert_eq!(
        &diagnostic_source.source
            [body_range.start - diagnostic_source.range_offset..body_range.end - diagnostic_source.range_offset],
        "x"
    );
}

#[test]
fn analysis_ambiguous_implicit_cast_diagnostic_maps_two_labeled_candidates() {
    let lowering = implicit_cast_diagnostic_lowering();
    let owner = labeled_def(&lowering.labels, "owner");
    let candidates = [
        labeled_def(&lowering.labels, "cast_one"),
        labeled_def(&lowering.labels, "cast_two"),
    ];
    let owner_span = lowering
        .modules
        .def_source_span(owner)
        .expect("owner definition span")
        .clone();
    let candidate_spans = candidates.map(|candidate| {
        lowering
            .modules
            .def_source_span(candidate)
            .expect("candidate definition span")
            .clone()
    });
    let mut labels = poly::dump::DumpLabels::new();
    labels
        .set_def_label(candidates[0], "example.cast_one")
        .set_def_label(candidates[1], "example.cast_two");
    let error = infer::lowering::BodyLoweringError::Analysis(
        infer::analysis::AnalysisDiagnostic::AmbiguousImplicitCast {
            source: vec!["int".to_string()],
            target: vec!["frac".to_string()],
            candidates: candidates.to_vec(),
            source_span: Some(owner_span.clone()),
        },
    );

    let diagnostic =
        source_diagnostic_from_body_lowering_error(&error, &lowering.modules, &labels, None, None);

    assert_eq!(
        diagnostic,
        SourceDiagnostic {
            severity: SourceDiagnosticSeverity::Error,
            code: Some("yulang.ambiguous-implicit-cast".to_string()),
            label: None,
            file: Some(owner_span.file),
            range: Some(owner_span.range),
            message:
                "implicit cast from `int` to `frac` is ambiguous: 2 visible declarations match"
                    .to_string(),
            hint: Some("declare or import only one matching `cast` for this pair".to_string(),),
            related: vec![
                SourceDiagnosticRelated {
                    message: "matching cast declaration: example.cast_one".to_string(),
                    file: candidate_spans[0].file.clone(),
                    range: candidate_spans[0].range,
                    origin: None,
                },
                SourceDiagnosticRelated {
                    message: "matching cast declaration: example.cast_two".to_string(),
                    file: candidate_spans[1].file.clone(),
                    range: candidate_spans[1].range,
                    origin: None,
                },
            ],
        }
    );
    assert_eq!(diagnostic.message, format_body_lowering_error(&error));
}

#[test]
fn role_impl_associated_type_mismatch_diagnostic_uses_method_label_without_requirement() {
    let modules = empty_diagnostic_modules();
    let error = infer::lowering::BodyLoweringError::RoleImplAssociatedTypeMismatch {
        impl_def: poly::expr::DefId(10),
        method_def: poly::expr::DefId(11),
        role: vec![
            "std".to_string(),
            "data".to_string(),
            "index".to_string(),
            "Index".to_string(),
        ],
        method: "index".to_string(),
        associated: vec![infer::lowering::RoleImplAssociatedDiagnosticSite {
            name: "value".to_string(),
            source: infer::SourceSpan {
                file: path_from_segments(&["role_impl"]),
                range: SourceRange { start: 20, end: 24 },
            },
        }],
        impl_source: infer::SourceSpan {
            file: path_from_segments(&["role_impl"]),
            range: SourceRange { start: 0, end: 40 },
        },
        method_source: infer::SourceSpan {
            file: path_from_segments(&["role_impl"]),
            range: SourceRange { start: 30, end: 40 },
        },
        requirement_source: None,
    };

    let diagnostic = source_diagnostic_from_body_lowering_error(
        &error,
        &modules,
        &poly::dump::DumpLabels::new(),
        Some(poly::expr::DefId(11)),
        Some("d11".to_string()),
    );

    assert_eq!(
        format_body_lowering_error(&error),
        "impl method `index` does not satisfy explicit associated type `value` for role `std::data::index::Index`"
    );
    assert_eq!(
        diagnostic,
        SourceDiagnostic {
            severity: SourceDiagnosticSeverity::Error,
            code: Some("yulang.role-impl-associated-type-mismatch".to_string()),
            label: Some("index".to_string()),
            file: Some(path_from_segments(&["role_impl"])),
            range: Some(SourceRange {
                start: 20,
                end: 24,
            }),
            message: "impl method `index` does not satisfy explicit associated type `value` for role `std::data::index::Index`".to_string(),
            hint: Some(
                "change the associated type assignment or make the method signature and body satisfy it"
                    .to_string(),
            ),
            related: vec![SourceDiagnosticRelated {
                message: "impl method `index` is implemented here".to_string(),
                file: path_from_segments(&["role_impl"]),
                range: SourceRange {
                    start: 30,
                    end: 40,
                },
                origin: Some(SourceDiagnosticRelatedOrigin::Expression),
            }],
        }
    );
}

#[test]
fn role_impl_associated_type_mismatch_diagnostic_maps_multiple_assignments_with_requirement() {
    let modules = empty_diagnostic_modules();
    let error = infer::lowering::BodyLoweringError::RoleImplAssociatedTypeMismatch {
        impl_def: poly::expr::DefId(20),
        method_def: poly::expr::DefId(21),
        role: vec!["example".to_string(), "Pair".to_string()],
        method: "pair".to_string(),
        associated: vec![
            infer::lowering::RoleImplAssociatedDiagnosticSite {
                name: "first".to_string(),
                source: infer::SourceSpan {
                    file: path_from_segments(&["impls"]),
                    range: SourceRange {
                        start: 100,
                        end: 103,
                    },
                },
            },
            infer::lowering::RoleImplAssociatedDiagnosticSite {
                name: "second".to_string(),
                source: infer::SourceSpan {
                    file: path_from_segments(&["impls"]),
                    range: SourceRange {
                        start: 110,
                        end: 114,
                    },
                },
            },
        ],
        impl_source: infer::SourceSpan {
            file: path_from_segments(&["impls"]),
            range: SourceRange {
                start: 80,
                end: 140,
            },
        },
        method_source: infer::SourceSpan {
            file: path_from_segments(&["impls", "methods"]),
            range: SourceRange {
                start: 120,
                end: 140,
            },
        },
        requirement_source: Some(infer::SourceSpan {
            file: path_from_segments(&["roles"]),
            range: SourceRange { start: 50, end: 70 },
        }),
    };

    let diagnostic = source_diagnostic_from_body_lowering_error(
        &error,
        &modules,
        &poly::dump::DumpLabels::new(),
        None,
        None,
    );

    assert_eq!(
        format_body_lowering_error(&error),
        "impl method `pair` does not satisfy explicit associated types `first`, `second` for role `example::Pair`"
    );
    assert_eq!(
        diagnostic,
        SourceDiagnostic {
            severity: SourceDiagnosticSeverity::Error,
            code: Some("yulang.role-impl-associated-type-mismatch".to_string()),
            label: Some("pair".to_string()),
            file: Some(path_from_segments(&["impls"])),
            range: Some(SourceRange {
                start: 100,
                end: 103,
            }),
            message: "impl method `pair` does not satisfy explicit associated types `first`, `second` for role `example::Pair`".to_string(),
            hint: Some(
                "change the associated type assignment or make the method signature and body satisfy it"
                    .to_string(),
            ),
            related: vec![
                SourceDiagnosticRelated {
                    message: "explicit associated type `second` is assigned here".to_string(),
                    file: path_from_segments(&["impls"]),
                    range: SourceRange {
                        start: 110,
                        end: 114,
                    },
                    origin: Some(SourceDiagnosticRelatedOrigin::TypeAnnotation),
                },
                SourceDiagnosticRelated {
                    message: "impl method `pair` is implemented here".to_string(),
                    file: path_from_segments(&["impls", "methods"]),
                    range: SourceRange {
                        start: 120,
                        end: 140,
                    },
                    origin: Some(SourceDiagnosticRelatedOrigin::Expression),
                },
                SourceDiagnosticRelated {
                    message: "role requirement for `pair` is declared here".to_string(),
                    file: path_from_segments(&["roles"]),
                    range: SourceRange { start: 50, end: 70 },
                    origin: Some(SourceDiagnosticRelatedOrigin::TypeAnnotation),
                },
            ],
        }
    );
}

fn empty_diagnostic_modules() -> infer::ModuleTable {
    let loaded = sources::load(vec![sources::SourceFile {
        module_path: Path::default(),
        source: String::new(),
    }]);
    infer::lowering::lower_loaded_files(&loaded)
        .expect("empty diagnostic fixture should lower")
        .modules
}

#[test]
fn analyze_entry_source_reports_unresolved_name_source_range() {
    let root = temp_root("analyze-entry-source-unresolved-range");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("lib").join("std")).unwrap();
    fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
    fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

    let output = analyze_entry_source_with_std_options(
        root.join("main.yu"),
        "my result = missing\n",
        &StdSourceOptions {
            std_root: Some(root.join("lib")),
        },
    )
    .unwrap();

    assert_eq!(
        output.diagnostics,
        vec![SourceDiagnostic {
            severity: SourceDiagnosticSeverity::Error,
            code: Some("yulang.unresolved-value".to_string()),
            label: Some("result".to_string()),
            file: Some(Path::default()),
            range: Some(SourceRange {
                start: IMPLICIT_PRELUDE_IMPORT.len() + IMPLICIT_STD_MODULE_DECL.len() + 12,
                end: IMPLICIT_PRELUDE_IMPORT.len() + IMPLICIT_STD_MODULE_DECL.len() + 19,
            }),
            message: "unresolved value name: missing".to_string(),
            hint: Some(
                "define `missing` before this use, or import the module that provides it"
                    .to_string(),
            ),
            related: Vec::new(),
        }]
    );
}

#[test]
fn hover_entry_source_reports_decl_type() {
    let root = temp_root("hover-entry-source-decl");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("lib").join("std")).unwrap();
    fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
    fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

    let hover = hover_entry_source_with_std_options(
        root.join("main.yu"),
        "my x: int = 1\n",
        3,
        &StdSourceOptions {
            std_root: Some(root.join("lib")),
        },
    )
    .unwrap()
    .unwrap();

    assert_eq!(
        hover,
        SourceHover {
            range: SourceRange {
                start: IMPLICIT_PRELUDE_IMPORT.len() + IMPLICIT_STD_MODULE_DECL.len() + 3,
                end: IMPLICIT_PRELUDE_IMPORT.len() + IMPLICIT_STD_MODULE_DECL.len() + 4,
            },
            contents: "x: int".to_string(),
            documentation: None,
        }
    );
}

#[test]
fn hover_entry_source_reports_ref_target_type() {
    let root = temp_root("hover-entry-source-ref");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("lib").join("std")).unwrap();
    fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
    fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

    let source = "my x: int = 1\nmy y = x\n";
    let ref_offset = source.rfind('x').unwrap();
    let hover = hover_entry_source_with_std_options(
        root.join("main.yu"),
        source,
        ref_offset,
        &StdSourceOptions {
            std_root: Some(root.join("lib")),
        },
    )
    .unwrap()
    .unwrap();

    assert_eq!(
        hover,
        SourceHover {
            range: SourceRange {
                start: IMPLICIT_PRELUDE_IMPORT.len() + IMPLICIT_STD_MODULE_DECL.len() + ref_offset,
                end: IMPLICIT_PRELUDE_IMPORT.len()
                    + IMPLICIT_STD_MODULE_DECL.len()
                    + ref_offset
                    + 1,
            },
            contents: "x: int".to_string(),
            documentation: None,
        }
    );
}

const EFFECT_OPERATION_HOVER_SOURCE: &str =
    "act choose:\n  our pick: int -> bool\nmy result = choose::pick 1\n";

#[test]
fn hover_entry_source_reports_effect_operation_decl_type() {
    let hover = hover_entry_source("main.yu", EFFECT_OPERATION_HOVER_SOURCE, 18)
        .unwrap()
        .unwrap();

    assert_eq!(
        hover,
        SourceHover {
            range: SourceRange { start: 18, end: 22 },
            contents: "pick: int -> [choose] bool".to_string(),
            documentation: None,
        }
    );
    assert_public_type_display_has_no_private_markers(
        &hover.contents,
        "effect operation declaration hover",
    );
}

#[test]
fn hover_entry_source_reports_effect_operation_ref_type() {
    let hover = hover_entry_source("main.yu", EFFECT_OPERATION_HOVER_SOURCE, 56)
        .unwrap()
        .unwrap();

    assert_eq!(
        hover,
        SourceHover {
            range: SourceRange { start: 56, end: 60 },
            contents: "pick: int -> [choose] bool".to_string(),
            documentation: None,
        }
    );
    assert_public_type_display_has_no_private_markers(
        &hover.contents,
        "effect operation reference hover",
    );
}

#[test]
fn definition_entry_source_reports_ref_target() {
    let root = temp_root("definition-entry-source-ref");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("lib").join("std")).unwrap();
    fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
    fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

    let entry = root.join("main.yu");
    let source = "my x: int = 1\nmy y = x\n";
    let decl_offset = source.find('x').unwrap();
    let ref_offset = source.rfind('x').unwrap();
    let definition = definition_entry_source_with_std_options(
        &entry,
        source,
        ref_offset,
        &StdSourceOptions {
            std_root: Some(root.join("lib")),
        },
    )
    .unwrap()
    .unwrap();

    assert_eq!(
        definition,
        SourceDefinition {
            origin: SourceRange {
                start: IMPLICIT_PRELUDE_IMPORT.len() + IMPLICIT_STD_MODULE_DECL.len() + ref_offset,
                end: IMPLICIT_PRELUDE_IMPORT.len()
                    + IMPLICIT_STD_MODULE_DECL.len()
                    + ref_offset
                    + 1,
            },
            target: SourceLocation {
                path: entry,
                range: SourceRange {
                    start: IMPLICIT_PRELUDE_IMPORT.len()
                        + IMPLICIT_STD_MODULE_DECL.len()
                        + decl_offset,
                    end: IMPLICIT_PRELUDE_IMPORT.len()
                        + IMPLICIT_STD_MODULE_DECL.len()
                        + decl_offset
                        + 1,
                },
            },
        }
    );
}

#[test]
fn references_entry_source_reports_ref_targets() {
    let source = "my x = 1\nmy y = x\nmy z = x\n";
    let decl_offset = source.find('x').unwrap();
    let first_ref_offset = source.find("= x").unwrap() + 2;
    let second_ref_offset = source.rfind('x').unwrap();

    let references = references_entry_source("main.yu", source, first_ref_offset, true).unwrap();

    assert_eq!(
        references,
        vec![
            SourceLocation {
                path: PathBuf::from("main.yu"),
                range: SourceRange {
                    start: decl_offset,
                    end: decl_offset + 1,
                },
            },
            SourceLocation {
                path: PathBuf::from("main.yu"),
                range: SourceRange {
                    start: first_ref_offset,
                    end: first_ref_offset + 1,
                },
            },
            SourceLocation {
                path: PathBuf::from("main.yu"),
                range: SourceRange {
                    start: second_ref_offset,
                    end: second_ref_offset + 1,
                },
            },
        ]
    );

    let references_without_decl =
        references_entry_source("main.yu", source, first_ref_offset, false).unwrap();

    assert_eq!(
        references_without_decl,
        vec![
            SourceLocation {
                path: PathBuf::from("main.yu"),
                range: SourceRange {
                    start: first_ref_offset,
                    end: first_ref_offset + 1,
                },
            },
            SourceLocation {
                path: PathBuf::from("main.yu"),
                range: SourceRange {
                    start: second_ref_offset,
                    end: second_ref_offset + 1,
                },
            },
        ]
    );
}

#[test]
fn prepare_rename_entry_source_reports_target_range() {
    let source = "my x = 1\nmy y = x\n";
    let ref_offset = source.rfind('x').unwrap();

    let range = prepare_rename_entry_source("main.yu", source, ref_offset)
        .unwrap()
        .unwrap();

    assert_eq!(
        range,
        SourceRange {
            start: ref_offset,
            end: ref_offset + 1,
        }
    );
}

#[test]
fn rename_entry_source_reports_ref_target_edits() {
    let source = "my x = 1\nmy y = x\nmy z = x\n";
    let decl_offset = source.find('x').unwrap();
    let first_ref_offset = source.find("= x").unwrap() + 2;
    let second_ref_offset = source.rfind('x').unwrap();

    let rename = rename_entry_source("main.yu", source, first_ref_offset, "renamed")
        .unwrap()
        .unwrap();

    assert_eq!(
        rename,
        SourceRename {
            range: SourceRange {
                start: first_ref_offset,
                end: first_ref_offset + 1,
            },
            edits: vec![
                SourceTextEdit {
                    location: SourceLocation {
                        path: PathBuf::from("main.yu"),
                        range: SourceRange {
                            start: decl_offset,
                            end: decl_offset + 1,
                        },
                    },
                    new_text: "renamed".to_string(),
                },
                SourceTextEdit {
                    location: SourceLocation {
                        path: PathBuf::from("main.yu"),
                        range: SourceRange {
                            start: first_ref_offset,
                            end: first_ref_offset + 1,
                        },
                    },
                    new_text: "renamed".to_string(),
                },
                SourceTextEdit {
                    location: SourceLocation {
                        path: PathBuf::from("main.yu"),
                        range: SourceRange {
                            start: second_ref_offset,
                            end: second_ref_offset + 1,
                        },
                    },
                    new_text: "renamed".to_string(),
                },
            ],
        }
    );
}

#[test]
fn rename_entry_source_refuses_invalid_identifier() {
    let source = "my x = 1\nmy y = x\n";
    let ref_offset = source.rfind('x').unwrap();

    let rename = rename_entry_source("main.yu", source, ref_offset, "my").unwrap();

    assert_eq!(rename, None);
}

#[test]
fn hover_entry_source_reports_lambda_arg_type() {
    let source = "my id x = x\n";
    let arg_offset = source.find('x').unwrap();
    let hover = hover_entry_source("main.yu", source, arg_offset)
        .unwrap()
        .unwrap();

    assert_eq!(
        hover.range,
        SourceRange {
            start: arg_offset,
            end: arg_offset + 1,
        }
    );
    assert!(
        hover.contents.starts_with("x: "),
        "expected hover to show lambda arg type, got {:?}",
        hover.contents
    );
}

#[test]
fn hover_entry_source_reports_lambda_arg_ref_type() {
    let source = "my id x = x\n";
    let ref_offset = source.rfind('x').unwrap();
    let hover = hover_entry_source("main.yu", source, ref_offset)
        .unwrap()
        .unwrap();

    assert_eq!(
        hover.range,
        SourceRange {
            start: ref_offset,
            end: ref_offset + 1,
        }
    );
    assert!(
        hover.contents.starts_with("x: "),
        "expected hover to show lambda arg ref type, got {:?}",
        hover.contents
    );
}

#[test]
fn hover_entry_source_uses_nearest_shadowed_lambda_arg_type() {
    let source = "my f = \\x: bool -> (\\x: int -> x) 1\n";
    let ref_offset = source.rfind('x').unwrap();
    let hover = hover_entry_source("main.yu", source, ref_offset)
        .unwrap()
        .unwrap();

    assert_eq!(
        hover.range,
        SourceRange {
            start: ref_offset,
            end: ref_offset + 1,
        }
    );
    assert!(
        hover.contents.starts_with("x: ") && hover.contents.contains("int"),
        "expected hover to use nearest lambda arg type, got {:?}",
        hover.contents
    );
    assert!(
        !hover.contents.contains("bool"),
        "expected hover not to use outer lambda arg type, got {:?}",
        hover.contents
    );
}

#[test]
fn definition_entry_source_reports_lambda_arg_target() {
    let source = "my id x = x\n";
    let arg_offset = source.find('x').unwrap();
    let ref_offset = source.rfind('x').unwrap();
    let definition = definition_entry_source("main.yu", source, ref_offset)
        .unwrap()
        .unwrap();

    assert_eq!(
        definition,
        SourceDefinition {
            origin: SourceRange {
                start: ref_offset,
                end: ref_offset + 1,
            },
            target: SourceLocation {
                path: PathBuf::from("main.yu"),
                range: SourceRange {
                    start: arg_offset,
                    end: arg_offset + 1,
                },
            },
        }
    );
}

#[test]
fn references_entry_source_reports_lambda_arg_refs() {
    let source = "my id x = x\n";
    let arg_offset = source.find('x').unwrap();
    let ref_offset = source.rfind('x').unwrap();

    let references = references_entry_source("main.yu", source, ref_offset, true).unwrap();

    assert_eq!(
        references,
        vec![
            SourceLocation {
                path: PathBuf::from("main.yu"),
                range: SourceRange {
                    start: arg_offset,
                    end: arg_offset + 1,
                },
            },
            SourceLocation {
                path: PathBuf::from("main.yu"),
                range: SourceRange {
                    start: ref_offset,
                    end: ref_offset + 1,
                },
            },
        ]
    );
}

#[test]
fn hover_entry_source_shortens_import_visible_type_paths() {
    let std_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../lib");
    let source = "my keep(x: opt int): opt int = x\n";
    let hover = hover_entry_source_with_std_options(
        "main.yu",
        source,
        source.find("keep").unwrap(),
        &StdSourceOptions {
            std_root: Some(std_root),
        },
    )
    .unwrap()
    .unwrap();

    assert!(
        hover.contents.contains("keep: opt int -> opt int"),
        "expected imported opt path to be shortened, got {:?}",
        hover.contents
    );
    assert!(
        !hover.contents.contains("std::data::opt::opt"),
        "expected hover type to omit absolute opt path, got {:?}",
        hover.contents
    );
}

#[test]
fn hover_entry_source_shortens_import_visible_effect_paths() {
    let std_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../lib");
    let source = "use std::control::nondet::*\nmy run(x: [nondet] int): int = x\n";
    let hover = hover_entry_source_with_std_options(
        "main.yu",
        source,
        source.find("run").unwrap(),
        &StdSourceOptions {
            std_root: Some(std_root),
        },
    )
    .unwrap()
    .unwrap();

    assert!(
        hover.contents.contains("[nondet; "),
        "expected imported nondet effect path to be shortened, got {:?}",
        hover.contents
    );
    assert!(
        !hover.contents.contains("std::control::nondet::nondet"),
        "expected hover type to omit absolute nondet path, got {:?}",
        hover.contents
    );
}

#[test]
fn hover_entry_source_shortens_prelude_visible_effect_paths() {
    let std_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../lib");
    let source = "my run(x: [nondet] int): int = x\n";
    let hover = hover_entry_source_with_std_options(
        "main.yu",
        source,
        source.find("run").unwrap(),
        &StdSourceOptions {
            std_root: Some(std_root),
        },
    )
    .unwrap()
    .unwrap();

    assert!(
        hover.contents.contains("[nondet; "),
        "expected prelude-visible nondet effect path to be shortened, got {:?}",
        hover.contents
    );
    assert!(
        !hover.contents.contains("std::control::nondet::nondet"),
        "expected hover type to omit absolute nondet path, got {:?}",
        hover.contents
    );
}

#[test]
fn hover_entry_source_shortens_selected_method_type_paths() {
    let std_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../lib");
    let source = "use std::control::nondet::*\nmy got = (each [1]).once\n";
    let hover = hover_entry_source_with_std_options(
        "main.yu",
        source,
        source.rfind("once").unwrap(),
        &StdSourceOptions {
            std_root: Some(std_root),
        },
    )
    .unwrap()
    .unwrap();

    assert!(
        hover.contents.contains("once: "),
        "expected hover to show selected once method, got {:?}",
        hover.contents
    );
    assert!(
        !hover.contents.contains("std::control::nondet::nondet"),
        "expected hover type to omit absolute nondet path, got {:?}",
        hover.contents
    );
    assert!(
        !hover.contents.contains("std::data::opt::opt"),
        "expected hover type to omit absolute opt path, got {:?}",
        hover.contents
    );
}

#[test]
fn hover_entry_source_shortens_prelude_visible_selected_method_type_paths() {
    let std_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../lib");
    let source = "my got = (each [1]).once\n";
    let hover = hover_entry_source_with_std_options(
        "main.yu",
        source,
        source.rfind("once").unwrap(),
        &StdSourceOptions {
            std_root: Some(std_root),
        },
    )
    .unwrap()
    .unwrap();

    assert!(
        hover.contents.contains("once: "),
        "expected hover to show selected once method, got {:?}",
        hover.contents
    );
    assert!(
        !hover.contents.contains("std::control::nondet::nondet"),
        "expected hover type to omit absolute nondet path, got {:?}",
        hover.contents
    );
    assert!(
        !hover.contents.contains("std::data::opt::opt"),
        "expected hover type to omit absolute opt path, got {:?}",
        hover.contents
    );
}

#[test]
fn hover_entry_source_public_def_type_does_not_leak_private_markers() {
    let source = yulang_fixture("regressions/effect/public_type_display_order_signatures.yu");
    let hover = hover_entry_source("main.yu", &source, source.find("twice").unwrap())
        .unwrap()
        .unwrap();

    assert!(
        hover.contents.starts_with("twice: "),
        "expected hover to show twice def type, got {:?}",
        hover.contents
    );
    assert_eq!(
        hover.contents,
        concat!(
            "twice: ",
            "(('a | 'b) ['c@∅] -> ['c@∅ & 'd@∅] 'b & 'e) -> 'a -> ['d] 'e@"
        )
    );
    assert_public_type_display_has_no_private_markers(&hover.contents, "hover public def type");
}

#[test]
fn hover_entry_source_local_arg_type_does_not_leak_private_markers() {
    let source = yulang_fixture("regressions/effect/public_type_display_order_signatures.yu");
    let arg_offset = source.find("f x").unwrap();
    let hover = hover_entry_source("main.yu", &source, arg_offset)
        .unwrap()
        .unwrap();

    assert!(
        hover.contents.starts_with("f: "),
        "expected hover to show local arg type, got {:?}",
        hover.contents
    );
    assert_public_type_display_has_no_private_markers(&hover.contents, "hover local arg type");
}

#[test]
fn hover_entry_source_record_select_type_does_not_leak_private_markers() {
    let source = "my r = { f: \\x -> x }\nmy got = r.f\n";
    let field_offset = source.rfind(".f").unwrap() + 1;
    let hover = hover_entry_source("main.yu", source, field_offset)
        .unwrap()
        .unwrap();

    assert!(
        hover.contents.starts_with("f: "),
        "expected hover to show selected record field type, got {:?}",
        hover.contents
    );
    assert_public_type_display_has_no_private_markers(&hover.contents, "hover record select type");
}

#[test]
fn hover_entry_source_large_record_type_is_structurally_truncated() {
    let fields = (0..90)
        .map(|index| format!("field_{index:03}_wide_name: {index}"))
        .collect::<Vec<_>>()
        .join(", ");
    let source = format!("my wide = {{{fields}}}\nwide\n");
    let hover = hover_entry_source("main.yu", &source, source.find("wide").unwrap())
        .unwrap()
        .unwrap();

    assert!(
        hover.contents.contains('…'),
        "expected large hover type to contain structural truncation, got {:?}",
        hover.contents
    );
    assert!(
        hover.contents.chars().count() <= 700,
        "expected large hover type to stay near the public formatter budget, got {} chars:\n{}",
        hover.contents.chars().count(),
        hover.contents
    );
    assert_public_type_display_has_no_private_markers(&hover.contents, "large hover record type");
}

#[test]
fn hover_entry_source_does_not_show_synthetic_var_act_copy_locals() {
    let std_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../lib");
    let source = "role Pick 'container 'key:\n\
                  \x20 type value\n\
                  \x20 our container.pick: 'key -> value\n\
                  \n\
                  struct pair 'left 'right { left: 'left, right: 'right } with:\n\
                  \x20 impl Pick int:\n\
                  \x20   type value = 'left\n\
                  \x20   our p.pick _ = p.left\n\
                  \n\
                  \x20 impl Pick bool:\n\
                  \x20   type value = 'right\n\
                  \x20   our p.pick _ = p.right\n\
                  \n\
                  my p = pair { left: 10, right: false }\n\
                  \n\
                  (p.pick 0, p.pick true)\n";
    let type_var_offset = source.find("type value = 'right").unwrap() + "type value = '".len();
    let hover = hover_entry_source_with_std_options(
        "main.yu",
        source,
        type_var_offset,
        &StdSourceOptions {
            std_root: Some(std_root),
        },
    )
    .unwrap();

    if let Some(hover) = hover {
        assert!(
            !hover.contents.contains("var_ref") && !hover.contents.contains("std.text.parse"),
            "expected hover not to show synthetic var-act copy local, got {:?}",
            hover.contents
        );
    }
}

#[test]
fn hover_entry_source_does_not_expose_synthetic_var_act_paths() {
    let std_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../lib");
    let source = "my f =\n  my $x = 1\n  $x\n";
    let hover = hover_entry_source_with_std_options(
        "main.yu",
        source,
        source.rfind("$x").unwrap(),
        &StdSourceOptions {
            std_root: Some(std_root),
        },
    )
    .unwrap();

    if let Some(hover) = hover {
        assert!(
            !hover.contents.contains('#'),
            "expected hover not to expose synthetic var-act paths, got {:?}",
            hover.contents
        );
    }
}

#[test]
fn hover_entry_source_reports_attached_role_method_selection_type() {
    let source = "role Pick 'container 'key:\n\
                  \x20 type value\n\
                  \x20 our container.pick: 'key -> value\n\
                  \n\
                  struct pair 'left 'right { left: 'left, right: 'right } with:\n\
                  \x20 impl Pick int:\n\
                  \x20   type value = 'left\n\
                  \x20   our p.pick _ = p.left\n\
                  \n\
                  \x20 impl Pick bool:\n\
                  \x20   type value = 'right\n\
                  \x20   our p.pick _ = p.right\n\
                  \n\
                  my p = pair { left: 10, right: false }\n\
                  \n\
                  (p.pick 0, p.pick true)\n";
    let hover = hover_entry_source("main.yu", source, source.rfind("pick true").unwrap())
        .unwrap()
        .unwrap();

    assert!(
        hover.contents.starts_with("pick: "),
        "expected hover to show selected pick call-site type, got {:?}",
        hover.contents
    );
    assert!(
        !hover.contents.contains('#'),
        "expected hover not to expose hidden method labels, got {:?}",
        hover.contents
    );
    assert_public_type_display_has_no_private_markers(
        &hover.contents,
        "hover selected method type",
    );
}

#[test]
fn hover_entry_source_preserves_poly_variant_case_payloads() {
    let std_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../lib");
    let source = "my render option = case option:\n\
                  \x20 :ok msg -> \"[ok] \" + msg\n\
                  \x20 :err code -> \"[err \" + code.show + \"]\"\n\
                  \x20 :pending -> \"...\"\n";
    let hover = hover_entry_source_with_std_options(
        "main.yu",
        source,
        source.find("option").unwrap(),
        &StdSourceOptions {
            std_root: Some(std_root),
        },
    )
    .unwrap()
    .unwrap();

    assert!(
        !hover.contents.contains("ok never") && !hover.contents.contains("err never"),
        "case scrutinee payloads collapsed to never in hover: {:?}",
        hover.contents
    );
}

#[test]
fn dump_poly_with_std_preserves_poly_variant_case_payloads() {
    let entry = write_main_with_std(
        "dump-poly-std-poly-variant-case-payloads",
        "my render option = case option:\n\
         \x20 :ok msg -> \"[ok] \" + msg\n\
         \x20 :err code -> \"[err \" + code.show + \"]\"\n\
         \x20 :pending -> \"...\"\n",
    );

    let output = dump_poly_from_entry_with_std(&entry).unwrap();

    assert!(
        !output.text.contains("ok never") && !output.text.contains("err never"),
        "case scrutinee payloads collapsed to never in dump:\n{}",
        output.text
    );
}

#[test]
fn hover_entry_source_reports_shorthand_record_pattern_type() {
    let source = "my f({x = 1}) = x\n";
    let pattern_offset = source.find('x').unwrap();
    let hover = hover_entry_source("main.yu", source, pattern_offset)
        .unwrap()
        .unwrap();

    assert_eq!(
        hover.range,
        SourceRange {
            start: pattern_offset,
            end: pattern_offset + 1,
        }
    );
    assert!(
        hover.contents.starts_with("x: int"),
        "expected hover to show shorthand record pattern type, got {:?}",
        hover.contents
    );
}

#[test]
fn hover_entry_source_reports_record_field_selection_type() {
    let source = "my p = { x: 1, y: false }\nmy got = p.x\n";
    let field_offset = source.rfind(".x").unwrap() + 1;
    let hover = hover_entry_source("main.yu", source, field_offset)
        .unwrap()
        .unwrap();

    assert_eq!(
        hover.range,
        SourceRange {
            start: field_offset,
            end: field_offset + 1,
        }
    );
    assert_eq!(hover.contents, "x: int");
}

#[test]
fn hover_entry_source_reports_selected_method_type() {
    let source = "type User with:\n  our x.id = x\nmy u: User = 1\nmy got = u.id\n";
    let method_offset = source.rfind("id").unwrap();
    let hover = hover_entry_source("main.yu", source, method_offset)
        .unwrap()
        .unwrap();

    assert_eq!(
        hover.range,
        SourceRange {
            start: method_offset,
            end: method_offset + 2,
        }
    );
    assert_eq!(hover.contents, "id: User");
}

#[test]
fn definition_entry_source_reports_selected_method_target() {
    let source = "type User with:\n  our x.id = x\nmy u: User = 1\nmy got = u.id\n";
    let decl_offset = source.find("id").unwrap();
    let method_offset = source.rfind("id").unwrap();
    let definition = definition_entry_source("main.yu", source, method_offset)
        .unwrap()
        .unwrap();

    assert_eq!(
        definition,
        SourceDefinition {
            origin: SourceRange {
                start: method_offset,
                end: method_offset + 2,
            },
            target: SourceLocation {
                path: PathBuf::from("main.yu"),
                range: SourceRange {
                    start: decl_offset,
                    end: decl_offset + 2,
                },
            },
        }
    );
}

#[test]
fn references_entry_source_reports_selected_method_refs() {
    let source = "type User with:\n  our x.id = x\nmy u: User = 1\nmy a = u.id\nmy b = u.id\n";
    let decl_offset = source.find("id").unwrap();
    let first_method_offset = source.find("u.id").unwrap() + 2;
    let second_method_offset = source.rfind("id").unwrap();

    let references = references_entry_source("main.yu", source, first_method_offset, true).unwrap();

    assert_eq!(
        references,
        vec![
            SourceLocation {
                path: PathBuf::from("main.yu"),
                range: SourceRange {
                    start: decl_offset,
                    end: decl_offset + 2,
                },
            },
            SourceLocation {
                path: PathBuf::from("main.yu"),
                range: SourceRange {
                    start: first_method_offset,
                    end: first_method_offset + 2,
                },
            },
            SourceLocation {
                path: PathBuf::from("main.yu"),
                range: SourceRange {
                    start: second_method_offset,
                    end: second_method_offset + 2,
                },
            },
        ]
    );
}

#[test]
fn rename_entry_source_reports_selected_method_edits() {
    let source = "type User with:\n  our x.id = x\nmy u: User = 1\nmy a = u.id\nmy b = u.id\n";
    let decl_offset = source.find("id").unwrap();
    let first_method_offset = source.find("u.id").unwrap() + 2;
    let second_method_offset = source.rfind("id").unwrap();

    let rename = rename_entry_source("main.yu", source, first_method_offset, "ident")
        .unwrap()
        .unwrap();

    assert_eq!(
        rename,
        SourceRename {
            range: SourceRange {
                start: first_method_offset,
                end: first_method_offset + 2,
            },
            edits: vec![
                SourceTextEdit {
                    location: SourceLocation {
                        path: PathBuf::from("main.yu"),
                        range: SourceRange {
                            start: decl_offset,
                            end: decl_offset + 2,
                        },
                    },
                    new_text: "ident".to_string(),
                },
                SourceTextEdit {
                    location: SourceLocation {
                        path: PathBuf::from("main.yu"),
                        range: SourceRange {
                            start: first_method_offset,
                            end: first_method_offset + 2,
                        },
                    },
                    new_text: "ident".to_string(),
                },
                SourceTextEdit {
                    location: SourceLocation {
                        path: PathBuf::from("main.yu"),
                        range: SourceRange {
                            start: second_method_offset,
                            end: second_method_offset + 2,
                        },
                    },
                    new_text: "ident".to_string(),
                },
            ],
        }
    );
}

#[test]
fn definition_entry_source_with_std_reports_std_method_target() {
    let std_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../lib");
    let entry = std_root.join("std").join("core").join("ops.yu");
    let source = fs::read_to_string(&entry).unwrap();
    let offset = source.find("label.next").unwrap() + "label.".len();
    let definition = definition_entry_source_with_std_options(
        &entry,
        &source,
        offset,
        &StdSourceOptions {
            std_root: Some(std_root.clone()),
        },
    )
    .unwrap()
    .unwrap();
    let target = std_root.join("std").join("control").join("flow.yu");
    let target_source = fs::read_to_string(&target).unwrap();
    let target_offset = target_source.find("a.next").unwrap() + "a.".len();

    assert_eq!(
        definition.target,
        SourceLocation {
            path: target,
            range: SourceRange {
                start: target_offset,
                end: target_offset + "next".len(),
            },
        }
    );
}

#[test]
fn check_poly_std_in_filters_to_requested_module() {
    let root = temp_root("check-poly-std-in");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("lib").join("std")).unwrap();
    fs::write(root.join("main.yu"), "my x = 1\n").unwrap();
    fs::write(
        root.join("lib").join("std.yu"),
        "mod prelude;\nmod foo;\nmod bar;\n",
    )
    .unwrap();
    fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();
    fs::write(
        root.join("lib").join("std").join("foo.yu"),
        "my good x = x\nmy bad: bool = 1\n",
    )
    .unwrap();
    fs::write(
        root.join("lib").join("std").join("bar.yu"),
        "my bad2: bool = 1\n",
    )
    .unwrap();

    let output =
        check_poly_from_entry_with_std_in_module(root.join("main.yu"), "std::foo").unwrap();

    assert_eq!(output.file_count, 5);
    assert_check_contains(&output, "check-poly-std-in std::foo\n");
    assert_check_contains(&output, "  values: 2\n");
    assert_check_contains(&output, "  typed lets: 2\n");
    assert_check_contains(&output, "  missing schemes: 0\n");
    assert_check_contains(&output, "  bodyless declarations: 1\n");
    assert_check_contains(&output, "  lowering errors: 1 local / 2 total\n");
    assert_eq!(
        output
            .diagnostics
            .iter()
            .map(|diagnostic| (diagnostic.label.as_deref(), diagnostic.message.as_str()))
            .collect::<Vec<_>>(),
        vec![(Some("std.foo.bad"), "type mismatch: int is not bool")]
    );
}

#[test]
fn dump_poly_std_in_filters_to_requested_module_and_local_errors() {
    let root = temp_root("dump-poly-std-in");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("lib").join("std")).unwrap();
    fs::write(root.join("main.yu"), "my x = 1\n").unwrap();
    fs::write(
        root.join("lib").join("std.yu"),
        "mod prelude;\nmod foo;\nmod bar;\n",
    )
    .unwrap();
    fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();
    fs::write(
        root.join("lib").join("std").join("foo.yu"),
        "my good x = x\nmy bad: bool = 1\n",
    )
    .unwrap();
    fs::write(
        root.join("lib").join("std").join("bar.yu"),
        "my bad2: bool = 1\n",
    )
    .unwrap();

    let output = dump_poly_from_entry_with_std_in_module(root.join("main.yu"), "std::foo").unwrap();

    assert_eq!(output.file_count, 5);
    assert_dump_contains(&output, "module std::foo\n");
    assert_dump_contains(&output, "values: 2\n");
    assert_dump_contains(&output, "lowering errors: 1 local / 2 total\n");
    assert_dump_contains(&output, "\"std.foo.good\"");
    assert_dump_contains(&output, "\"std.foo.bad\"");
    assert!(!output.text.contains("\"std.bar.bad2\""));
    assert_eq!(
        output.errors,
        vec!["type mismatch: int is not bool".to_string()]
    );
}

#[test]
fn dump_poly_std_in_raw_filters_to_requested_module() {
    let root = temp_root("dump-poly-std-in-raw");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("lib").join("std")).unwrap();
    fs::write(root.join("main.yu"), "my x = 1\n").unwrap();
    fs::write(root.join("lib").join("std.yu"), "mod prelude;\nmod foo;\n").unwrap();
    fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();
    fs::write(root.join("lib").join("std").join("foo.yu"), "my id x = x\n").unwrap();

    let output =
        dump_poly_raw_from_entry_with_std_in_module(root.join("main.yu"), "std.foo").unwrap();

    assert_eq!(output.file_count, 4);
    assert_eq!(output.errors, Vec::<String>::new());
    assert_dump_contains(&output, "module std::foo\n");
    assert_dump_contains(&output, "raw roots [");
    assert_dump_contains(&output, "\"std.foo.id\"");
    assert_dump_contains(&output, "scheme {");
    assert_dump_contains(&output, "exprs {");
    assert!(!output.text.contains("main"));
}

#[test]
fn use_mod_loads_module_file_but_plain_use_does_not() {
    let root = temp_root("use-mod-loads");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(root.join("main.yu"), "use mod math::*\nmy x = 1\n").unwrap();
    fs::write(root.join("plain.yu"), "use math::*\nmy x = 1\n").unwrap();
    fs::write(root.join("math.yu"), "my y = 2\n").unwrap();

    let use_mod = collect_local_sources(root.join("main.yu")).unwrap();
    let plain_use = collect_local_sources(root.join("plain.yu")).unwrap();

    assert_eq!(use_mod.len(), 2);
    assert_eq!(plain_use.len(), 1);
}

#[test]
fn current_realm_use_loads_band_root_file() {
    let root = temp_root("realm-use-loads-band");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("main.yu"),
        "use realm/helper::value\nmy x = value\n",
    )
    .unwrap();
    fs::write(root.join("helper.yu"), "our value = 1\n").unwrap();

    let files = collect_local_sources(root.join("main.yu")).unwrap();
    let modules = files
        .iter()
        .map(|file| file.module_path.clone())
        .collect::<Vec<_>>();

    assert_eq!(files.len(), 2);
    assert!(modules.contains(&Path::default()));
    assert!(modules.contains(&Path {
        segments: vec![Name("helper".into())],
    }));
    let root_file = files
        .iter()
        .find(|file| file.module_path.segments.is_empty())
        .unwrap();
    assert_eq!(root_file.band_path, path_from_segments(&["main"]));
}

#[test]
fn current_realm_entry_band_alias_does_not_load_entry_twice() {
    let root = temp_root("realm-entry-band-alias");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("main.yu"),
        "use realm/main::value as self_value\npub value = 7\nself_value\n",
    )
    .unwrap();

    let files = collect_local_sources(root.join("main.yu")).unwrap();

    assert_eq!(files.len(), 1);
    assert_eq!(files[0].module_path, Path::default());
    assert_eq!(files[0].band_path, path_from_segments(&["main"]));
}

#[test]
fn current_realm_entry_band_alias_resolves_to_root_module() {
    let root = temp_root("realm-entry-band-alias-run");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("main.yu"),
        "use realm/main::value as self_value\npub value = 7\nself_value\n",
    )
    .unwrap();

    let output = run_evidence_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.text, "run roots [7]\n");
}

#[test]
fn current_band_use_in_entry_band_resolves_from_root_module() {
    let root = temp_root("entry-band-current-band");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("main")).unwrap();
    fs::write(
        root.join("main.yu"),
        "mod inner;\nuse band::inner::value\nvalue\n",
    )
    .unwrap();
    fs::write(root.join("main").join("inner.yu"), "our value = 9\n").unwrap();

    let output = run_evidence_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.text, "run roots [9]\n");
}

#[test]
fn current_realm_cache_does_not_redirect_missing_local_band() {
    let root = temp_root("realm-cache-no-redirect");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    let main_path = root.join("main.yu");
    let cached_path = root.join("cached-helper.yu");
    let cache_root = root.join("cache-root");
    let request = alias_import(
        "value",
        &["helper", "value"],
        sources::UsePathRoute::CurrentRealm { band_segments: 1 },
    );
    let main_source = "use realm/helper::value\nvalue\n";
    let cached_source = "pub value = 7\n";
    fs::write(&main_path, main_source).unwrap();
    fs::write(&cached_path, cached_source).unwrap();

    write_current_realm_resolution_cache_entry(
        &cache_root,
        &main_path,
        main_source,
        request,
        &cached_path,
        cached_source,
    );

    let err = collect_local_sources_with_cache(
        &main_path,
        SourceCollectionCache::new(crate::cache::ArtifactCache::new(cache_root)),
    )
    .unwrap_err();

    assert!(matches!(
        err,
        RouteError::RealmBandNotFound { band, .. }
            if band.segments == vec![Name("helper".into())]
    ));

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn current_realm_cache_stale_entry_falls_back_to_local_band() {
    let root = temp_root("realm-cache-stale-fallback");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    let main_path = root.join("main.yu");
    let helper_path = root.join("helper.yu");
    let cache_root = root.join("cache-root");
    let request = alias_import(
        "value",
        &["helper", "value"],
        sources::UsePathRoute::CurrentRealm { band_segments: 1 },
    );
    let main_source = "use realm/helper::value\nvalue\n";
    fs::write(&main_path, main_source).unwrap();
    fs::write(&helper_path, "pub value = 8\n").unwrap();

    write_current_realm_resolution_cache_entry(
        &cache_root,
        &main_path,
        main_source,
        request,
        &helper_path,
        "pub value = 7\n",
    );

    let files = collect_local_sources_with_cache(
        &main_path,
        SourceCollectionCache::new(crate::cache::ArtifactCache::new(cache_root)),
    )
    .unwrap();
    let helper = files
        .iter()
        .find(|file| file.module_path == path_from_segments(&["helper"]))
        .unwrap();

    assert_eq!(helper.source, "pub value = 8\n");

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn installed_local_realm_import_loads_snapshot_band() {
    let root = temp_root("installed-local-realm-import");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    let lib_root = root.join("lib");
    let realm_root = root.join("theme-src");
    fs::create_dir_all(&realm_root).unwrap();
    fs::write(
        realm_root.join("realm.toml"),
        r#"[realm]
name = "theme"
version = "1.0.0"
"#,
    )
    .unwrap();
    fs::write(realm_root.join("colors.yu"), "pub value = 7\n").unwrap();
    let app_root = root.join("app");
    fs::create_dir_all(&app_root).unwrap();
    let main_path = app_root.join("main.yu");
    fs::write(&main_path, "use local/theme/colors::value v1.0.0\nvalue\n").unwrap();

    let (output, files) = crate::stdlib::with_test_user_lib_root(&lib_root, || {
        install_local_realm(&realm_root, None).unwrap();
        (
            run_evidence_from_entry(&main_path).unwrap(),
            collect_local_sources(&main_path).unwrap(),
        )
    });

    assert_eq!(output.text, "run roots [7]\n");
    assert!(files.iter().any(|file| {
        file.module_path == path_from_segments(&["local", "theme", "colors"])
            && file.band_path == path_from_segments(&["local", "theme", "colors"])
            && file.source == "pub value = 7\n"
    }));

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn source_collection_records_resolution_import_metadata() {
    let root = temp_root("resolution-import-metadata");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("main.yu"),
        "use ui/widget::a as item v1.2 with program::ui\nmy x = 1\n",
    )
    .unwrap();

    let files = collect_local_sources(root.join("main.yu")).unwrap();
    let root_file = files
        .iter()
        .find(|file| file.module_path.segments.is_empty())
        .unwrap();

    assert_eq!(
        root_file.resolution_imports,
        vec![sources::UseImport::Alias {
            name: Name("item".into()),
            path: Path {
                segments: vec![Name("ui".into()), Name("widget".into()), Name("a".into())],
            },
            route: sources::UsePathRoute::SlashQualified { prefix_segments: 2 },
            version: Some("v1.2".into()),
            anchor: Some(sources::UseAnchor {
                path: Path {
                    segments: vec![Name("program".into()), Name("ui".into())],
                },
                route: sources::UsePathRoute::Relative,
            }),
        }]
    );
}

#[test]
fn current_band_absolute_use_resolves_from_root_module() {
    let root = temp_root("band-use-root");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("main.yu"),
        "mod helper;\nmod nested;\nmy root = nested::x\n",
    )
    .unwrap();
    fs::write(root.join("helper.yu"), "our value = 1\n").unwrap();
    fs::write(
        root.join("nested.yu"),
        "use band::helper::value\nour x = value\n",
    )
    .unwrap();

    let output =
        build_poly_from_sources(collect_local_sources(root.join("main.yu")).unwrap()).unwrap();

    assert_eq!(output.errors, Vec::<String>::new());
}

#[test]
fn current_realm_pub_use_resolves_band_root_without_mod_decl() {
    let root = temp_root("realm-use-pub-band");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("main.yu"),
        "use realm/helper::value\nmy x = value\n",
    )
    .unwrap();
    fs::write(root.join("helper.yu"), "pub value = 1\n").unwrap();

    let output =
        build_poly_from_sources(collect_local_sources(root.join("main.yu")).unwrap()).unwrap();

    assert_eq!(output.errors, Vec::<String>::new());
}

#[test]
fn current_realm_band_keeps_current_band_imports_inside_band_root() {
    let root = temp_root("realm-use-band-current-band");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("helper")).unwrap();
    fs::write(root.join("main.yu"), "use realm/helper::run\nmy x = run\n").unwrap();
    fs::write(
        root.join("helper.yu"),
        "mod inner;\nuse band::inner::value\npub run = value\n",
    )
    .unwrap();
    fs::write(root.join("helper/inner.yu"), "our value = 1\n").unwrap();

    let output =
        build_poly_from_sources(collect_local_sources(root.join("main.yu")).unwrap()).unwrap();

    assert_eq!(output.errors, Vec::<String>::new());
}

#[test]
fn current_realm_use_does_not_import_our_export() {
    let root = temp_root("realm-use-hides-our");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("main.yu"),
        "use realm/helper::value\nmy x = value\n",
    )
    .unwrap();
    fs::write(root.join("helper.yu"), "our value = 1\n").unwrap();

    let output =
        build_poly_from_sources(collect_local_sources(root.join("main.yu")).unwrap()).unwrap();

    assert!(
        !output.errors.is_empty(),
        "cross-band import should not see our value"
    );
}

#[test]
fn current_realm_use_does_not_make_band_visible_to_bare_paths() {
    let root = temp_root("realm-use-no-bare-band");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("main.yu"),
        "use realm/helper::value\nmy x = helper::value\n",
    )
    .unwrap();
    fs::write(root.join("helper.yu"), "pub value = 1\n").unwrap();

    let output =
        build_poly_from_sources(collect_local_sources(root.join("main.yu")).unwrap()).unwrap();

    assert!(
        !output.errors.is_empty(),
        "current-realm band should not be reachable through bare helper::..."
    );
}

#[test]
fn missing_current_realm_band_reports_band_not_found() {
    let root = temp_root("realm-use-missing-band");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(root.join("main.yu"), "use realm/helper::value\n").unwrap();

    let err = collect_local_sources(root.join("main.yu")).unwrap_err();

    assert!(matches!(
        err,
        RouteError::RealmBandNotFound { band, .. }
            if band.segments == vec![Name("helper".into())]
    ));
}

#[test]
fn current_realm_band_cannot_claim_mod_owned_file() {
    let root = temp_root("realm-use-mod-owned-band");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("main.yu"),
        "mod helper;\nuse realm/helper::value\n",
    )
    .unwrap();
    fs::write(root.join("helper.yu"), "our value = 1\n").unwrap();

    let err = collect_local_sources(root.join("main.yu")).unwrap_err();

    assert!(matches!(
        err,
        RouteError::DuplicateModuleFile {
            first_module,
            first_band,
            second_module,
            second_band,
            ..
        } if first_module.segments == vec![Name("helper".into())]
            && first_band.segments == vec![Name("main".into())]
            && second_module.segments == vec![Name("helper".into())]
            && second_band.segments == vec![Name("helper".into())]
    ));
}

#[test]
fn current_realm_cross_band_cycle_is_rejected() {
    let root = temp_root("realm-use-band-cycle");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(root.join("main.yu"), "use realm/a::value\n").unwrap();
    fs::write(root.join("a.yu"), "use realm/b::value\npub value = 1\n").unwrap();
    fs::write(root.join("b.yu"), "use realm/a::value\npub value = 2\n").unwrap();

    let err = collect_local_sources(root.join("main.yu")).unwrap_err();

    assert!(matches!(
        err,
        RouteError::CrossBandCycle { from, to }
            if from.segments == vec![Name("b".into())]
                && to.segments == vec![Name("a".into())]
    ));
}

#[test]
fn run_evidence_rejects_lowering_errors_in_current_realm_dependency() {
    let root = temp_root("realm-use-dependency-lowering-error");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("helper")).unwrap();
    fs::write(root.join("main.yu"), "use realm/helper::answer\nanswer\n").unwrap();
    fs::write(
        root.join("helper.yu"),
        "mod inner;\nuse band::inner::bonus\npub answer = 40 + bonus\n",
    )
    .unwrap();
    fs::write(root.join("helper").join("inner.yu"), "our bonus = 2\n").unwrap();

    let err = run_evidence_from_entry(root.join("main.yu")).unwrap_err();

    assert!(matches!(
        err,
        RouteError::LoweringDiagnostics { errors }
            if errors.iter().any(|error| error.contains("unresolved value name: #op:infix:+"))
    ));
}

#[test]
fn discover_module_loads_uses_lightweight_module_parse() {
    let requests = discover_module_loads(
        &Path::default(),
        "infix (<+>) 50 50 = add\nmy x = 1 <+> 2\nmod child;\nuse mod util::*\n",
    );

    assert_eq!(
        requests,
        vec![
            ModuleLoadRequest {
                parent: Path::default(),
                name: Name("child".into()),
                kind: sources::ModuleLoadKind::ModDecl,
                visibility: sources::Visibility::Our,
            },
            ModuleLoadRequest {
                parent: Path::default(),
                name: Name("util".into()),
                kind: sources::ModuleLoadKind::UseMod,
                visibility: sources::Visibility::Our,
            },
        ]
    );
}

#[test]
fn source_header_metadata_reads_header_only_current_realm_use() {
    let metadata =
        discover_source_header_metadata(&Path::default(), "use realm/helper::answer\nmy x = 1\n");

    assert_eq!(
        metadata.current_realm_bands,
        vec![path_from_segments(&["helper"])]
    );
    assert_eq!(metadata.resolution_imports.len(), 1);
}

#[test]
fn source_header_metadata_keeps_late_current_realm_use() {
    let metadata =
        discover_source_header_metadata(&Path::default(), "my x = 1\nuse realm/helper::answer\n");

    assert_eq!(
        metadata.current_realm_bands,
        vec![path_from_segments(&["helper"])]
    );
    assert_eq!(metadata.resolution_imports.len(), 1);
}

#[test]
fn reports_ambiguous_module_file() {
    let root = temp_root("ambiguous-module");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("main")).unwrap();
    fs::write(root.join("main.yu"), "mod child;\n").unwrap();
    fs::write(root.join("child.yu"), "my y = 1\n").unwrap();
    fs::write(root.join("main").join("child.yu"), "my y = 2\n").unwrap();

    let err = collect_local_sources(root.join("main.yu")).unwrap_err();

    assert!(matches!(err, RouteError::AmbiguousModuleFile { .. }));
}

#[cfg(unix)]
#[test]
fn reports_same_file_loaded_as_two_modules() {
    let root = temp_root("duplicate-module-file");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(root.join("main.yu"), "mod a;\nmod b;\n").unwrap();
    fs::write(root.join("a.yu"), "my x = 1\n").unwrap();
    std::os::unix::fs::symlink(root.join("a.yu"), root.join("b.yu")).unwrap();

    let err = collect_local_sources(root.join("main.yu")).unwrap_err();

    assert!(matches!(
        err,
        RouteError::DuplicateModuleFile {
            first_module,
            second_module,
            ..
        } if first_module.segments == vec![Name("a".into())]
            && second_module.segments == vec![Name("b".into())]
    ));
}
