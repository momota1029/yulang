use super::*;

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
    let source = "\
{
    my $xs = [
        2
        3
        4
    ]
    &xs[1] = 6
    $xs
}
";
    let build =
        build_control_from_source_text_with_embedded_playground_std("playground.yu", source)
            .unwrap();
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_control_on_vm_test_stack(build);

    assert_eq!(output.0, "run roots [[2, 6, 4]]\n");
}

#[test]
fn typed_playground_std_prefix_matches_loaded_route_for_list_update() {
    let source = "\
{
    my $xs = [
        2
        3
        4
    ]
    &xs[1] = 6
    $xs
}
";
    let loaded =
        load_source_text_with_embedded_playground_std("playground.yu", source.to_string()).unwrap();
    let loaded_poly = build_poly_from_loaded_files(loaded).unwrap();
    let loaded_build = build_control_from_poly_output(&loaded_poly).unwrap();
    assert!(loaded_build.errors.is_empty(), "{:?}", loaded_build.errors);
    let loaded_output = run_built_control_on_vm_test_stack(loaded_build);

    let cached_build =
        build_control_from_source_text_with_embedded_playground_std("playground.yu", source)
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
fn run_control_source_text_with_embedded_std_runs_root_expression() {
    let output =
        run_control_from_source_text_with_embedded_std("playground.yu", "1 + 2\n").unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [3]\n");
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
            },
            ModuleLoadRequest {
                parent: Path::default(),
                name: Name("util".into()),
                kind: sources::ModuleLoadKind::UseMod,
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
