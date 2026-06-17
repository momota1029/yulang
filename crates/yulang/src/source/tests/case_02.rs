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
    let files = collect_source_text_with_embedded_std("playground.yu", "my y = x<..\n".to_string())
        .unwrap()
        .into_iter()
        .map(|file| SourceFile {
            module_path: file.module_path,
            source: file.source,
        })
        .collect::<Vec<_>>();
    let loaded = sources::load(files);
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
    let output = run_built_control_program(&build.program, build.file_count, build.errors).unwrap();

    assert_eq!(output.text, "run roots [3]\n");
}

#[test]
fn run_control_source_text_with_embedded_playground_std_runs_mixed_numeric_add() {
    let build =
        build_control_from_source_text_with_embedded_playground_std("playground.yu", "1 + 1.2\n")
            .unwrap();
    assert!(build.errors.is_empty(), "{:?}", build.errors);
    let output = run_built_control_program(&build.program, build.file_count, build.errors).unwrap();

    assert_eq!(output.text, "run roots [2.2]\n");
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
    let output = run_built_control_program(&build.program, build.file_count, build.errors).unwrap();

    assert_eq!(output.text, "run roots [26.12]\n");
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
    let output = run_built_control_program(&build.program, build.file_count, build.errors).unwrap();

    assert_eq!(output.text, "run roots [15]\n");
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
    let output = run_built_control_program(&build.program, build.file_count, build.errors).unwrap();

    assert_eq!(output.text, "run roots [[2, 6, 4]]\n");
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
    let output = run_built_control_program(&build.program, build.file_count, build.errors).unwrap();

    assert_eq!(output.text, "run roots [7]\n");
}

#[test]
fn run_control_source_text_with_embedded_std_runs_root_expression() {
    let output =
        run_control_from_source_text_with_embedded_std("playground.yu", "1 + 2\n").unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [3]\n");
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
    let output = run_control_from_source_text_with_embedded_std(
        "playground.yu",
        "if all [1, 2, 3] < any [2, 3, 4]:\n  1\nelse:\n  0\n",
    )
    .unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [1]\n");
}

#[test]
fn run_control_source_text_with_embedded_std_keeps_std_instances_unmarked_between_roots() {
    let output = run_control_from_source_text_with_embedded_std(
        "playground.yu",
        "{\n  my a = each 1..3\n  a\n}.list\nif all [1, 2, 3] < any [3, 4, 5]:\n  1\nelse:\n  0\n",
    )
    .unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [[1, 2, 3], 1]\n");
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
    let output = std::thread::Builder::new()
            .stack_size(16 * 1024 * 1024)
            .spawn(|| {
                let output = run_control_from_source_text_with_embedded_std(
                    "playground.yu",
                    "{\n  my a = each 1..15\n  my b = each a..15\n  my c = each b..15\n  guard: a * a + b * b == c * c\n  (a, b, c)\n}.list\n",
                )
                .unwrap();
                (output.file_count, output.text)
            })
            .unwrap()
            .join()
            .unwrap();

    assert_eq!(output.0, embedded_std_files().len() + 1);
    assert_eq!(
        output.1,
        "run roots [[(3, 4, 5), (5, 12, 13), (6, 8, 10), (9, 12, 15)]]\n"
    );
}

#[test]
fn run_control_source_text_with_embedded_std_runs_nondet_once_triple() {
    let output = run_control_from_source_text_with_embedded_std(
            "playground.yu",
            "({\n  my a = each 1..\n  my b = each a<..\n  my c = each b<..\n  guard: a * a + b * b == c * c\n  (a, b, c)\n} .once).show\n",
        )
        .unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [\"just (3, 4, 5)\"]\n");
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

#[test]
fn run_control_source_text_with_embedded_std_runs_poly_variant_list() {
    let output =
        run_control_from_source_text_with_embedded_std("playground.yu", "[:a, :b]\n").unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [[a, b]]\n");
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
fn run_control_source_text_with_embedded_std_lowers_sub_syntax_return() {
    let output =
        run_control_from_source_text_with_embedded_std("playground.yu", "sub:\n  return 1\n")
            .unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
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
fn run_control_source_text_with_embedded_std_lowers_sub_lambda_return() {
    let output = run_control_from_source_text_with_embedded_std(
        "playground.yu",
        "my f = \\sub x -> return x\nf 7\n",
    )
    .unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
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
fn run_control_source_text_with_embedded_std_keeps_sub_syntax_hygiene() {
    let output = run_control_from_source_text_with_embedded_std(
        "playground.yu",
        "our g h = sub:\n  h 0\n  return 1\n\nsub:\n  g \\i -> return i\n  return 2\n",
    )
    .unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [0]\n");
}

#[test]
fn run_control_source_text_with_embedded_std_keeps_sub_return_through_for_callback_if() {
    let output = run_control_from_source_text_with_embedded_std(
            "playground.yu",
            "our g h = sub:\n  for i in 0..3:\n    h i\n  return 1\n\nsub:\n  my b = g \\i -> if i == 0: return i\n  b\n",
        )
        .unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_eq!(output.text, "run roots [0]\n");
}

#[test]
fn dump_mono_source_text_with_embedded_std_specializes_for_callback_if_before_println() {
    let output = dump_mono_from_source_text_with_embedded_std(
            "playground.yu",
            "our g h = sub:\n  for i in 0..3:\n    h i\n  return 1\n\nsub:\n  my b = g \\i -> if i == 0: return i\n  println b.show\n  2\n",
        )
        .unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
    assert_mono_dump_contains(&output, "std::control::flow::sub(int)");
    assert_mono_dump_contains(&output, "std::io::console::out");
}

#[test]
fn dump_poly_source_text_with_embedded_std_keeps_for_callback_residual_generic() {
    let output = dump_poly_from_source_text_with_embedded_std(
            "playground.yu",
            "our g h = sub:\n  for i in 0..3:\n    h i\n  return 1\n\nsub:\n  my b = g \\i -> if i == 0: return i\n  println b.show\n  2\n",
        )
        .unwrap();

    assert_eq!(output.file_count, embedded_std_files().len() + 1);
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
        "std::foo: values 2 typed 1 missing_schemes 1 bodyless 1",
    );
    assert_check_contains(&output, "missing schemes:\n");
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
            message: "type mismatch: bool is not int".to_string(),
        }]
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
    assert_check_contains(&output, "  missing schemes: 1\n");
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
