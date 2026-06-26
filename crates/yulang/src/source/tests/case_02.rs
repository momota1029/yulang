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
    let restored = build_poly_from_compiled_unit_artifact(output.compiled_unit.clone());
    assert_eq!(restored.errors, output.poly.errors);
    assert_eq!(restored.file_count, output.poly.file_count);
    assert_eq!(restored.arena.defs.len(), output.poly.arena.defs.len());
    assert_eq!(restored.labels, output.poly.labels);
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
    let suffix_files = vec![
        collected("main.yu", &[], "mod local;\nuse local::*\ny\n"),
        collected("local.yu", &["local"], "use ops::*\npub y = x\n"),
    ];

    let output =
        build_poly_from_compiled_unit_prefix_and_collected_sources(prefix, suffix_files).unwrap();
    assert!(output.errors.is_empty(), "{:?}", output.errors);
    assert_eq!(output.file_count, 4);
    let build = build_control_from_poly_output(&output).unwrap();
    let output = run_built_control_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [7]\n");
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
    let output = run_built_control_on_vm_test_stack(build);

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
fn run_control_with_std_specializes_attached_role_impl_methods() {
    let entry = write_main_with_std(
        "run-control-std-attached-role-impl-methods",
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

    let output = run_control_from_entry_with_std(entry).unwrap();

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
fn run_control_source_text_with_embedded_playground_std_runs_arithmetic() {
    let build =
        build_control_from_source_text_with_embedded_playground_std("playground.yu", "1 + 2\n")
            .unwrap();
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_control_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [3]\n");
}

#[test]
fn run_control_source_text_with_embedded_playground_std_runs_mixed_numeric_add() {
    let build =
        build_control_from_source_text_with_embedded_playground_std("playground.yu", "1 + 1.2\n")
            .unwrap();
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_control_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [2.2]\n");
}

#[test]
fn run_control_source_text_with_embedded_playground_std_formats_frac_roots() {
    let source = "\
std::num::frac::new 3 2
std::num::frac::new 4 2
";
    let build =
        build_control_from_source_text_with_embedded_playground_std("playground.yu", source)
            .unwrap();
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_control_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [3/2, 2]\n");
}

#[test]
fn run_control_source_text_with_embedded_playground_std_runs_struct_method_example() {
    let source = "\
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

point { x: 3, y: 4 } .norm2 + 1.12
";
    let build =
        build_control_from_source_text_with_embedded_playground_std("playground.yu", source)
            .unwrap();
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_control_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [26.12]\n");
}

#[test]
fn run_control_source_text_with_embedded_playground_std_runs_local_change_example() {
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
    let output = run_built_control_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [15]\n");
}

#[test]
fn run_control_source_text_with_embedded_playground_std_runs_list_update_example() {
    let source = yulang_fixture("regressions/runtime/list_update.yu");
    let build =
        build_control_from_source_text_with_embedded_playground_std("playground.yu", &source)
            .unwrap();
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_control_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [[2, 6, 4]]\n");
}

#[test]
fn run_control_source_text_with_embedded_playground_std_runs_junction_prelude_example() {
    let source = "if all [1, 2, 3] < any [2, 3, 4]:\n  1\nelse:\n  0\n";
    let build =
        build_control_from_source_text_with_embedded_playground_std("playground.yu", source)
            .unwrap();
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_control_on_vm_test_stack(build);

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
    let loaded_output = run_built_control_on_vm_test_stack(loaded_build);

    let cached_build =
        build_control_from_source_text_with_embedded_playground_std("playground.yu", &source)
            .unwrap();
    assert!(cached_build.errors.is_empty(), "{:?}", cached_build.errors);
    let cached_output = run_built_control_on_vm_test_stack(cached_build);

    assert_eq!(cached_output.0, loaded_output.0);
    assert_eq!(cached_output.1, loaded_output.1);
}

#[test]
fn run_control_source_text_with_embedded_playground_std_runs_sub_return_example() {
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
    let output = run_built_control_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [7]\n");
}

#[test]
fn run_control_source_text_with_embedded_playground_std_runs_nondet_range_guard() {
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
    let output = run_built_control_on_vm_test_stack(build);

    assert_eq!(
        output.0,
        "run roots [[(3, 4, 5), (5, 12, 13), (6, 8, 10), (9, 12, 15)]]\n"
    );
}

#[test]
fn run_control_source_text_with_embedded_playground_std_runs_nondet_once_range() {
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
    let output = run_built_control_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [opt::just((3, 4, 5))]\n");
}

#[test]
fn run_control_source_text_with_embedded_playground_std_replaces_strings() {
    let build = build_control_from_source_text_with_embedded_playground_std(
        "playground.yu",
        r#"("a-b-a".replace_once "a" "x", "a-b-a".replace "a" "x")"#,
    )
    .unwrap();
    assert!(build.file_count < embedded_std_files().len() + 1);
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_control_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [(\"x-b-a\", \"x-b-x\")]\n");
}

#[test]
fn run_control_source_text_with_embedded_std_runs_root_expression() {
    let output =
        run_control_from_source_text_with_embedded_std("playground.yu", "1 + 2\n").unwrap();

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
fn run_control_source_text_with_embedded_std_runs_parse_word_to_end() {
    let build = build_control_from_source_text_with_embedded_std(
        "playground.yu",
        "use std::text::parse::*\n(run_str(\"abc\", 1, 1, word()), run_str(\"abc!\", 1, 1, word()))\n",
    )
    .unwrap();
    assert_eq!(build.file_count, embedded_std_files().len() + 1);
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_control_on_vm_test_stack(build);

    assert_eq!(
        output.0,
        "run roots [(result::ok(\"abc\"), result::ok(\"abc\"))]\n"
    );
}

#[test]
fn run_control_source_text_with_embedded_std_replaces_strings() {
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
    let output = run_built_control_on_vm_test_stack(build);

    assert_eq!(
        output.0,
        "run roots [(\"x-b-a\", \"x-b-x\", \"xa\", \"abc\")]\n"
    );
}

#[test]
fn run_control_source_text_with_embedded_std_edits_parse_matches() {
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
    let output = run_built_control_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [\"hello Yulang from world!\"]\n");
}

#[test]
fn run_control_source_text_with_embedded_std_replaces_plain_rule_literals() {
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
    let output = run_built_control_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [\"hi hi\"]\n");
}

#[test]
fn run_control_source_text_with_embedded_std_edits_capture_rule_literals() {
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
    let output = run_built_control_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [\"alice bob\"]\n");
}

#[test]
fn run_control_source_text_with_embedded_std_edits_capture_rule_literal_once() {
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
    let output = run_built_control_on_vm_test_stack(build);

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
fn run_control_source_text_with_embedded_std_sequences_word_with_suffix() {
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
    let output = run_built_control_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [result::ok(\"alice\")]\n");
}

#[test]
fn run_control_source_text_with_embedded_std_choice_recovers_from_parse_fail() {
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
    let output = run_built_control_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [result::ok(\"fallback\")]\n");
}

#[test]
fn run_control_source_text_with_embedded_std_repeats_parser_until_delimiter() {
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
    let output = run_built_control_on_vm_test_stack(build);

    assert_eq!(
        output.0,
        "run roots [(result::ok([\"a\", \"b\", \"c\"]), result::ok([]), result::ok([\"a\", \"b\", \"c\"]))]\n"
    );
}

#[test]
fn run_control_source_text_with_embedded_std_repeats_parser_until_eof() {
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
    let output = run_built_control_on_vm_test_stack(build);

    assert_eq!(
        output.0,
        "run roots [(result::ok([\"a\", \"b\", \"c\"]), result::ok([]))]\n"
    );
}

#[test]
fn run_control_source_text_with_embedded_std_matches_rule_literals_in_case() {
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
    let output = run_built_control_on_vm_test_stack(build);

    assert_eq!(
        output.0,
        "run roots [(\"alice\", \"miss\", \"abc\", \"hit\", \"miss\")]\n"
    );
}

#[test]
fn run_control_source_text_with_embedded_std_matches_rule_exprs_in_case() {
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
    let output = run_built_control_on_vm_test_stack(build);

    assert_eq!(
        output.0,
        "run roots [(\"alice\", \"miss\", \"hit\", \"miss\", \"alice\", \"admin\", \"miss\", \"bob\")]\n"
    );
}

#[cfg(unix)]
#[test]
fn run_with_std_formats_frac_roots() {
    let (mono, control) = run_with_std_main(
        "run-std-frac-roots",
        "std::num::frac::new 3 2\nstd::num::frac::new 4 2\n",
    );

    assert_eq!(mono.text, "run roots [3/2, 2]\n");
    assert_eq!(control.text, "run roots [3/2, 2]\n");
}

#[test]
fn run_control_source_text_with_embedded_std_imports_prelude_reexports() {
    let output =
        run_control_from_source_text_with_embedded_std("playground.yu", "each(1..3).list\n")
            .unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [[1, 2, 3]]\n");
}

#[test]
fn run_control_source_text_with_embedded_std_runs_junction_tour_example() {
    let output = run_with_vm_test_stack(|| {
        let output = run_control_from_source_text_with_embedded_std(
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
fn run_control_source_text_with_embedded_std_keeps_std_instances_unmarked_between_roots() {
    let output = run_with_vm_test_stack(|| {
        let output = run_control_from_source_text_with_embedded_std(
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
fn run_control_source_text_with_embedded_std_forces_effectful_block_let() {
    let output = run_control_from_source_text_with_embedded_std(
        "playground.yu",
        "{\n  my a = each 1..3\n  (a, 1)\n}.list\n",
    )
    .unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [[(1, 1), (2, 1), (3, 1)]]\n");
}

#[test]
fn run_control_source_text_with_embedded_std_runs_nondet_triples() {
    let output = run_with_vm_test_stack(|| {
        let output = run_control_from_source_text_with_embedded_std(
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
fn run_control_source_text_with_embedded_std_runs_nondet_once_triple() {
    let output = run_with_vm_test_stack(|| {
        let output = run_control_from_source_text_with_embedded_std(
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
    let output = dump_poly_from_entry_with_std_in_module(entry, "std.control.var.ref").unwrap();

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

    let once = output
        .text
        .lines()
        .find(|line| line.starts_with("pub ") && line.contains("#act-method:once"))
        .expect("once act method should be dumped");
    assert!(
        once.contains(" [std::control::nondet::nondet; '"),
        "once act method should expose nondet with an independent residual:\n{once}"
    );
    assert!(
        !once.contains("& [std::control::nondet::nondet;"),
        "once act method is deep/recursive, not shallow:\n{once}"
    );
}

#[cfg(unix)]
#[test]
fn dump_poly_std_nondet_list_act_method_uses_deep_handler_effect() {
    let entry = write_main_with_std("dump-poly-std-nondet-list-type", "1\n");
    let output =
        dump_poly_from_entry_with_std_in_module(entry, "std.control.nondet.nondet").unwrap();

    let list = output
        .text
        .lines()
        .find(|line| line.starts_with("pub ") && line.contains("#act-method:list"))
        .expect("list act method should be dumped");
    assert!(
        list.contains(" [std::control::nondet::nondet; '"),
        "list act method should expose nondet with an independent residual:\n{list}"
    );
    assert!(
        !list.contains("& [std::control::nondet::nondet;"),
        "list act method is deep/recursive, not shallow:\n{list}"
    );
}

#[test]
fn run_control_source_text_with_embedded_std_runs_poly_variant_list() {
    let output =
        run_control_from_source_text_with_embedded_std("playground.yu", "[:a, :b]\n").unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [[a, b]]\n");
}

#[test]
fn run_control_source_text_with_embedded_std_indexes_strings_by_grapheme_cluster() {
    let source = "\
my s = \"e\u{301}🇯🇵👨‍👩‍👧‍👦!\"
(
    s.len,
    std::text::str::index_raw s 0,
    std::text::str::index_range_raw s 0 3,
    std::text::str::splice_raw s 1 3 \"X\"
)
";
    let output = run_control_from_source_text_with_embedded_std("playground.yu", source).unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(
        output.text,
        "run roots [(4, \"e\\u{301}\", \"e\\u{301}🇯🇵👨\\u{200d}👩\\u{200d}👧\\u{200d}👦\", \"e\\u{301}X!\")]\n"
    );
}

#[test]
fn run_control_source_text_with_embedded_std_indexes_string_lines_by_range() {
    let source = "\
my s = \"a👨‍👩‍👧‍👦\\nβ\\n\"
(
    std::text::str::line_count s,
    std::text::str::index_range s (std::text::str::line_range s 1)
)
";
    let output = run_control_from_source_text_with_embedded_std("playground.yu", source).unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [(3, \"β\\n\")]\n");
}

#[test]
fn run_control_source_text_with_embedded_std_roundtrips_string_bytes() {
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
    let output = run_control_from_source_text_with_embedded_std("playground.yu", source).unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [(3, 104, \"é\", true, \"hé\")]\n");
}

#[test]
fn run_control_source_text_with_embedded_std_reuses_record_default_function() {
    let output = run_control_from_source_text_with_embedded_std(
        "playground.yu",
        "my f({x = 1}) = x\n[f {}, f {x: 2}]\n",
    )
    .unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [[1, 2]]\n");
}

#[test]
fn run_control_source_text_with_embedded_std_record_default_accepts_float_field() {
    let source = "\
our box {width = 1, height = width} =
    width * height

box {width: 1.2}
";
    let output = run_control_from_source_text_with_embedded_std("playground.yu", source).unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [1.44]\n");
}

#[test]
fn run_control_fixture_lowers_sub_syntax_return() {
    let entry = write_source_with_fake_std(
        "run-control-sub-syntax-return",
        "support/fake_std/control_flow_io.yu",
        "sub:\n  return 1\n",
    );
    let output = run_control_from_entry(entry).unwrap();

    assert_eq!(output.file_count, 1);
    assert_eq!(output.text, "run roots [1]\n");
}

#[test]
fn run_control_source_text_with_embedded_std_lowers_labeled_sub_syntax_return() {
    let output = run_control_from_source_text_with_embedded_std(
        "playground.yu",
        "my x = sub 'outer:\n  'outer.return 1\nx\n",
    )
    .unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [1]\n");
}

#[test]
fn run_control_source_text_with_embedded_std_lowers_root_labeled_sub_syntax_return() {
    let output = run_control_from_source_text_with_embedded_std(
        "playground.yu",
        "sub 'outer:\n  'outer.return 1\n",
    )
    .unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [1]\n");
}

#[test]
fn run_control_fixture_lowers_sub_lambda_return() {
    let entry = write_source_with_fake_std(
        "run-control-sub-lambda-return",
        "support/fake_std/control_flow_io.yu",
        "my f = \\sub x -> return x\nf 7\n",
    );
    let output = run_control_from_entry(entry).unwrap();

    assert_eq!(output.file_count, 1);
    assert_eq!(output.text, "run roots [7]\n");
}

#[test]
fn run_control_source_text_with_embedded_std_lowers_labeled_sub_lambda_return() {
    let output = run_control_from_source_text_with_embedded_std(
        "playground.yu",
        "my f = \\sub 'out x -> 'out.return x\nf 7\n",
    )
    .unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [7]\n");
}

#[test]
fn run_control_source_text_with_embedded_std_labeled_sub_lambda_handles_inner_return() {
    let output = run_control_from_source_text_with_embedded_std(
        "playground.yu",
        "sub 'outer:\n  my f = \\sub 'inner x -> 'inner.return x\n  f 7\n",
    )
    .unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [7]\n");
}

#[test]
fn run_control_source_text_with_embedded_std_labeled_sub_lambda_lets_outer_return_escape() {
    let output = run_control_from_source_text_with_embedded_std(
        "playground.yu",
        "sub 'outer:\n  my f = \\sub 'inner x -> 'outer.return x\n  f 7\n  'outer.return 1\n",
    )
    .unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [7]\n");
}

#[test]
fn run_control_fixture_keeps_sub_syntax_hygiene() {
    let entry = write_source_with_fake_std(
        "run-control-sub-syntax-hygiene",
        "support/fake_std/control_flow_io.yu",
        "our g h = sub:\n  h 0\n  return 1\n\nsub:\n  g \\i -> return i\n  return 2\n",
    );
    let output = run_control_from_entry(entry).unwrap();

    assert_eq!(output.file_count, 1);
    assert_eq!(output.text, "run roots [0]\n");
}

#[test]
fn run_control_fixture_keeps_sub_return_through_for_callback_if() {
    let entry = write_fixture_with_fake_std(
        "run-control-sub-return-through-for-callback",
        "support/fake_std/control_flow_io.yu",
        "regressions/effect/sub_return_through_for_callback.yu",
    );
    let output = run_control_from_entry(entry).unwrap();

    assert_eq!(output.file_count, 1);
    assert_eq!(output.text, "run roots [0]\n");
}

#[test]
fn run_control_source_text_with_embedded_std_keeps_repeated_callback_hygiene() {
    let output = run_with_vm_test_stack(|| {
        let output = run_control_from_source_text_with_embedded_std(
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
    assert_check_contains(&output, "lowering errors:\n");
    assert_check_contains(&output, "x: type mismatch: bool is not int\n");
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
    assert_check_contains(&output, "lowering errors:\n");
    assert_check_contains(&output, "std.foo.bad: type mismatch: int is not bool\n");
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
            label: Some("x".to_string()),
            range: Some(SourceRange {
                start: IMPLICIT_PRELUDE_IMPORT.len() + IMPLICIT_STD_MODULE_DECL.len() + 3,
                end: IMPLICIT_PRELUDE_IMPORT.len() + IMPLICIT_STD_MODULE_DECL.len() + 4,
            }),
            message: "type mismatch: bool is not int".to_string(),
        }]
    );
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
            label: Some("result".to_string()),
            range: Some(SourceRange {
                start: IMPLICIT_PRELUDE_IMPORT.len() + IMPLICIT_STD_MODULE_DECL.len() + 12,
                end: IMPLICIT_PRELUDE_IMPORT.len() + IMPLICIT_STD_MODULE_DECL.len() + 19,
            }),
            message: "unresolved value name: missing".to_string(),
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
        }
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
        hover.contents.contains("pick: "),
        "expected hover to show selected pick method type, got {:?}",
        hover.contents
    );
    assert!(
        !hover.contents.contains('#'),
        "expected hover not to expose hidden method labels, got {:?}",
        hover.contents
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
    assert!(
        hover.contents.starts_with("User.id: "),
        "expected hover to show selected method, got {:?}",
        hover.contents
    );
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
    assert_check_contains(&output, "std.foo.bad: type mismatch: int is not bool\n");
    assert!(!output.text.contains("std.bar.bad2"));
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

    let output = run_control_from_entry(root.join("main.yu")).unwrap();

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

    let output = run_control_from_entry(root.join("main.yu")).unwrap();

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
fn run_control_rejects_lowering_errors_in_current_realm_dependency() {
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

    let err = run_control_from_entry(root.join("main.yu")).unwrap_err();

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
