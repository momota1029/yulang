use super::*;

#[test]
fn dump_poly_reads_mod_files() {
    let root = temp_root("dump-poly-reads-mod");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(root.join("main.yu"), "mod child;\nmy x = 1\n").unwrap();
    fs::write(root.join("child.yu"), "my y = 2\n").unwrap();

    let output = dump_poly_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 2);
    assert_eq!(
        output.text,
        "roots d0:child d1:x\nd0:child mod {\n  my d2:\"child.y\": int = e1:2\n}\nmy d1:x: int = e0:1\n"
    );
}

#[test]
fn dump_poly_without_std_infers_identity_function() {
    let root = temp_root("dump-poly-identity");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(root.join("main.yu"), "my id x = x\n").unwrap();

    let output = dump_poly_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_dump_has_line_starting_with(&output, "my d0:id: 'a -> 'a = ");
    assert!(!output.text.contains("std::"));
}

#[test]
fn dump_mono_without_std_ignores_unused_generic_binding() {
    let root = temp_root("dump-mono-unused-generic");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(root.join("main.yu"), "my id x = x\n").unwrap();

    let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_mono_dump_contains(&output, "mono roots []");
    assert!(!output.text.contains("d0"));
}

#[test]
fn dump_poly_without_std_keeps_root_expression() {
    let root = temp_root("dump-poly-root-expr");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(root.join("main.yu"), "1\n").unwrap();

    let output = dump_poly_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_eq!(output.text, "roots\nroot exprs e0:1\nruntime roots e0:1\n");
}

#[test]
fn dump_mono_without_std_keeps_root_expression() {
    let root = temp_root("dump-mono-root-expr");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(root.join("main.yu"), "1\n").unwrap();

    let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_mono_dump_contains(&output, "mono roots [1]");
}

#[test]
fn dump_mono_without_std_specializes_root_expression_call() {
    let root = temp_root("dump-mono-root-call");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(root.join("main.yu"), "my id x = x\nid(1)\n").unwrap();

    let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_mono_dump_contains(&output, "mono roots [(m0 1)]");
    assert_mono_dump_contains(&output, "m0 = d0 : int -> int");
}

#[test]
fn dump_mono_without_std_lowers_apply_colon_indent_block_argument() {
    let root = temp_root("dump-mono-apply-colon-block-arg");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(root.join("main.yu"), "my id x = x\nid:\n  my x = 1\n  x\n").unwrap();

    let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_mono_dump_contains(&output, "mono roots [(m0 {");
    assert_mono_dump_contains(&output, " = 1;");
    assert_mono_dump_contains(&output, "m0 = d0 : int -> int");
    assert!(!output.text.contains("(m0 ())"), "{}", output.text);
}

#[test]
fn dump_mono_without_std_forces_effectful_root_expression() {
    let root = temp_root("dump-mono-effectful-root");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("main.yu"),
        "act out:\n  our say: int -> unit\nout::say(1)\n",
    )
    .unwrap();

    let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_mono_dump_contains(
        &output,
        "mono roots [force-thunk[thunk[[out], unit] => unit ! [out]]((<effect-op out::say> 1))]",
    );
}

#[test]
fn dump_mono_without_std_passes_argument_effect_through_pure_function() {
    let root = temp_root("dump-mono-pure-function-argument-effect");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("main.yu"),
        "act out:\n  our read: unit -> int\nmy id x = x\nid(out::read(()))\n",
    )
    .unwrap();

    let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_mono_dump_contains(
        &output,
        "mono roots [(m0 force-thunk[thunk[[out], int] => int ! [out]]",
    );
    assert_mono_dump_contains(&output, "m0 = d2 : int -> int");
}

#[test]
fn dump_mono_without_std_rejects_root_case_without_concrete_join() {
    let root = temp_root("dump-mono-root-case-ambiguous");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(root.join("main.yu"), "case true: true -> 1, false -> 2.0\n").unwrap();

    let err = dump_mono_from_entry(root.join("main.yu")).unwrap_err();

    assert!(matches!(
        err,
        RouteError::Specialize(specialize::SpecializeError::ConflictingTypeCandidates { .. })
    ));
}

#[test]
fn dump_mono_without_std_reports_tuple_length_unsatisfied_subtype() {
    let entry = write_main(
        "dump-mono-tuple-length-unsatisfied",
        "my g(x: (int, int)) = x\ng (1, 2, 3)\n",
    );

    let err = dump_mono_from_entry(entry).unwrap_err();

    assert_unsatisfied_subtype_contains(err, "(int, int, int)", "(int, int)");
}

#[test]
fn dump_mono_without_std_reports_missing_record_field_unsatisfied_subtype() {
    let entry = write_main(
        "dump-mono-record-field-unsatisfied",
        "my f {a, b} = a\nf {a: 1}\n",
    );

    let err = dump_mono_from_entry(entry).unwrap_err();

    assert_unsatisfied_subtype_contains(err, "{a: int}", "b:");
}

#[test]
fn dump_mono_without_std_reports_polyvariant_constructor_unsatisfied_subtype() {
    let entry = write_main(
        "dump-mono-polyvariant-constructor-unsatisfied",
        "case :some 1:\n  :none -> 0\n",
    );

    let err = dump_mono_from_entry(entry).unwrap_err();

    assert_unsatisfied_subtype_contains(err, "'none", "'some(int)");
}

#[test]
fn dump_mono_without_std_specializes_root_case_with_direct_cast_join() {
    let root = temp_root("dump-mono-root-case-cast-join");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("main.yu"),
        "cast(x: int): float = 0.0\ncase true: true -> 1, false -> 2.0\n",
    )
    .unwrap();

    let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_mono_dump_contains(&output, "mono roots [case true:");
    assert_mono_dump_contains(&output, "-> (m0 1)");
    assert_mono_dump_contains(&output, "m0 = d0 : int -> float");
    assert!(
        !output.text.contains("coerce[int => float]"),
        "{}",
        output.text
    );
    assert!(!output.text.contains("int | float"), "{}", output.text);
}

#[test]
fn dump_mono_without_std_runs_computed_top_level_binding() {
    let root = temp_root("dump-mono-computed-binding");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(root.join("main.yu"), "my id x = x\nmy a = id(1)\n").unwrap();

    let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_mono_dump_contains(&output, "mono roots [eval m0]");
    assert_mono_dump_contains(&output, "m0 = d1 : int");
    assert_mono_dump_contains(&output, "m1 = d0 : int -> int");
}

#[test]
fn run_control_without_std_evaluates_computed_top_level_binding_without_result() {
    let root = temp_root("run-control-computed-binding-no-result");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(root.join("main.yu"), "my id x = x\nmy a = id(1)\n").unwrap();

    let mono = run_mono_from_entry(root.join("main.yu")).unwrap();
    let control = run_control_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(mono.file_count, 1);
    assert_eq!(mono.values, Vec::<mono_runtime::Value>::new());
    assert_eq!(mono.text, "run roots []\n");
    assert_eq!(control.file_count, 1);
    assert_eq!(control.values, Vec::<control_vm::Value>::new());
    assert_eq!(control.text, mono.text);
}

#[test]
fn dump_mono_without_std_lowers_direct_effect_handler() {
    let root = temp_root("dump-mono-direct-effect-handler");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("main.yu"),
        "act out:\n  our say: int -> unit\n\
             catch out::say(1):\n\
             \x20 out::say msg, k -> k(())\n\
             \x20 value -> value\n",
    )
    .unwrap();

    let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_mono_dump_contains(
        &output,
        "catch force-thunk[thunk[[out], unit] => unit ! [out]]",
    );
    assert_mono_dump_contains(&output, "out::say d");
    assert_mono_dump_contains(&output, "<effect-op out::say>");
    assert_mono_dump_contains(
        &output,
        "force-thunk[thunk[[out], unit] => unit ! [out]]((<effect-op out::say>",
    );
    assert!(!output.text.contains("adapter["), "{}", output.text);
}

#[test]
fn dump_mono_without_std_lowers_generic_direct_effect_handler() {
    let root = temp_root("dump-mono-generic-direct-effect-handler");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("main.yu"),
        "act var 't:\n  our get: unit -> 't\n\
             catch var::get():\n\
             \x20 var::get(), k -> k(1)\n\
             \x20 value -> value\n",
    )
    .unwrap();

    let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_mono_dump_contains(
        &output,
        "catch force-thunk[thunk[[var(int)], int] => int ! [var(int)]]",
    );
    assert_mono_dump_contains(&output, "var::get _");
    assert_mono_dump_contains(&output, "<effect-op var::get>");
    assert_mono_dump_contains(
        &output,
        "force-thunk[thunk[[var(int)], int] => int ! [var(int)]]((<effect-op var::get>",
    );
}

#[test]
fn dump_mono_without_std_lowers_wildcard_stack_handler_annotation() {
    let root = temp_root("dump-mono-wildcard-stack-handler-annotation");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("main.yu"),
        "act signal:\n  our ping: () -> int\n\n\
             my handle(x: [_] int): int = catch x:\n\
             \x20 signal::ping(), k -> k 1\n\
             \x20 v -> v\n\n\
             handle(signal::ping())\n",
    )
    .unwrap();

    let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_mono_dump_contains(&output, "mono roots [(m0 (<effect-op signal::ping> ()))");
    assert_mono_dump_contains(&output, "m0 = d2 : thunk[");
    assert_mono_dump_contains(&output, "marker[signal]");
    assert_mono_dump_contains(&output, " -> int");
    assert!(!output.text.contains("stack("), "{}", output.text);
}

#[test]
fn dump_mono_without_std_lowers_apply_colon_polymorphic_stack_handler_call() {
    let root = temp_root("dump-mono-apply-colon-stack-handler");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("main.yu"),
        "pub act sub 'a:\n\
             \x20 pub return: 'a -> never\n\
             \x20 pub sub(x: [_] 'a): 'a = catch x:\n\
             \x20 \x20 return a, _ -> a\n\
             \x20 \x20 a -> a\n\n\
             sub::sub:\n\
             \x20 sub::return 0\n",
    )
    .unwrap();

    let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_mono_dump_contains(&output, "mono roots [(m0 (<effect-op sub::return> 0))]");
    assert_mono_dump_contains(&output, "m0 = d2 : thunk[[sub(int)], int] -> int");
    assert_mono_dump_contains(&output, "marker[sub]");
    assert_mono_dump_contains(&output, "sub::return d");
}

#[test]
fn run_mono_without_std_runs_root_expression() {
    let root = temp_root("run-mono-root-expr");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(root.join("main.yu"), "1\n").unwrap();

    let output = run_mono_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_eq!(output.values, vec![mono_runtime::Value::Int(1)]);
    assert_eq!(output.text, "run roots [1]\n");
}

#[test]
fn run_mono_without_std_runs_apply_colon_block_argument() {
    let root = temp_root("run-mono-apply-colon-block-arg");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(root.join("main.yu"), "my id x = x\nid:\n  my x = 1\n  x\n").unwrap();

    let output = run_mono_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_eq!(output.values, vec![mono_runtime::Value::Int(1)]);
    assert_eq!(output.text, "run roots [1]\n");
}

#[test]
fn run_control_without_std_runs_apply_colon_block_argument() {
    let root = temp_root("run-control-apply-colon-block-arg");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(root.join("main.yu"), "my id x = x\nid:\n  my x = 1\n  x\n").unwrap();

    let output = run_control_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_eq!(output.values, vec![control_vm::Value::Int(1)]);
    assert_eq!(output.text, "run roots [1]\n");
}

#[test]
fn run_without_std_matches_control_on_record_case_and_handler_smoke() {
    let entry = write_main(
        "run-record-case-handler-smoke",
        "case { width: 1, height: 2 }:\n\
             \x20 { width, height } -> height\n\
             \x20 _ -> 0\n\n\
             enum opt 'a:\n\
             \x20 none\n\
             \x20 some 'a\n\
             act eff:\n\
             \x20 our send: opt int -> int\n\
             catch eff::send(opt::some 1):\n\
             \x20 eff::send(opt::some x), k -> k(x)\n\
             \x20 value -> value\n",
    );

    let mono = run_mono_from_entry(&entry).unwrap();
    let control = run_control_from_entry(&entry).unwrap();

    assert_eq!(mono.text, "run roots [2, 1]\n");
    assert_eq!(control.text, mono.text);
}

#[test]
fn run_without_std_matches_control_on_struct_field_projection() {
    let entry = write_main(
        "run-struct-field-projection",
        "struct User { age: int }\nUser({ age: 1 }).age\n",
    );

    let mono = run_mono_from_entry(&entry).unwrap();
    let control = run_control_from_entry(&entry).unwrap();

    assert_eq!(mono.text, "run roots [1]\n");
    assert_eq!(control.text, mono.text);
}

#[cfg(unix)]
#[test]
fn run_with_std_matches_control_on_core_smoke_suite() {
    let (mono, control) = run_with_std_main(
        "run-std-core-smoke-suite",
        "1 + 2 * 3\n\
             [1, 2, 3].map(\\x -> x + 1).filter(\\x -> x > 2).rev\n\
             \"sum=%{1 + 2}\"\n\
             \"hex=%x{255}\"\n\
             \"debug=%?{[1, 2]}\"\n\
             \"pad=%04{7}\"\n\
             for i in 0..3:\n\
             \x20 if i == 1: std::control::flow::loop::last()\n\
             1\n",
    );

    assert_eq!(
        mono.text,
        "run roots [7, [4, 3], \"sum=3\", \"hex=ff\", \"debug=[1, 2]\", \"pad=0007\", 1]\n"
    );
    assert_eq!(control.text, mono.text);
}

#[cfg(unix)]
#[test]
fn run_with_std_runs_list_view_raw_node() {
    let root = temp_root("run-std-list-view-raw-node");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    symlink_repo_lib(&root);
    fs::write(root.join("main.yu"), "std::data::list::view_raw [1, 2]\n").unwrap();

    let mono = run_mono_from_entry_with_std(root.join("main.yu")).unwrap();
    let control = run_control_from_entry_with_std(root.join("main.yu")).unwrap();

    assert!(mono.text.contains("([1], [2])"), "{}", mono.text);
    assert!(control.text.contains("([1], [2])"), "{}", control.text);
}

#[cfg(unix)]
#[test]
fn dump_mono_with_std_specializes_list_display() {
    let root = temp_root("dump-mono-std-list-display");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    symlink_repo_lib(&root);
    fs::write(root.join("main.yu"), "[1].show\n").unwrap();

    let output = dump_mono_from_entry_with_std(root.join("main.yu")).unwrap();

    assert_mono_dump_contains(&output, "std::data::list::list(int) -> std::text::str::str");
    assert_mono_dump_contains(&output, "std::data::list::list_view(int)");
}

#[cfg(unix)]
#[test]
fn dump_poly_with_std_keeps_computed_local_overloaded_result() {
    let entry = write_main_with_std(
        "dump-poly-std-computed-local-overloaded-result",
        "our add() =\n\
             \x20 my a = 1 + 2\n\
             \x20 a.show\n\
             \x20 a\n\n\
             add()\n",
    );

    let output = dump_poly_from_entry_with_std(entry).unwrap();

    assert_dump_contains(&output, "d1:add: () -> int");
    assert!(
        !output.text.contains("d1:add: () -> never"),
        "{}",
        output.text
    );
}

#[cfg(unix)]
#[test]
fn run_mono_with_std_collects_nondet_each_list() {
    let root = temp_root("run-mono-std-nondet-each-list");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    symlink_repo_lib(&root);
    fs::write(
        root.join("main.yu"),
        "std::control::nondet::each(1..3).list\n",
    )
    .unwrap();

    let output = run_mono_from_entry_with_std(root.join("main.yu")).unwrap();

    assert_eq!(output.text, "run roots [[1, 2, 3]]\n");
}

#[cfg(unix)]
#[test]
fn run_control_with_std_collects_nondet_each_list() {
    let root = temp_root("run-control-std-nondet-each-list");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    symlink_repo_lib(&root);
    fs::write(
        root.join("main.yu"),
        "std::control::nondet::each(1..3).list\n",
    )
    .unwrap();

    let output = run_control_from_entry_with_std(root.join("main.yu")).unwrap();

    assert_eq!(output.text, "run roots [[1, 2, 3]]\n");
}

#[cfg(unix)]
#[test]
fn run_with_std_collects_nondet_sum_list_benchmark() {
    let root = temp_root("run-std-nondet-sum-list-benchmark");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    symlink_repo_lib(&root);
    fs::write(
        root.join("main.yu"),
        "(std::control::nondet::each(1..3) + std::control::nondet::each(1..2)).list\n",
    )
    .unwrap();

    let mono = run_mono_from_entry_with_std(root.join("main.yu")).unwrap();
    let control = run_control_from_entry_with_std(root.join("main.yu")).unwrap();

    assert_eq!(mono.text, "run roots [[2, 3, 3, 4, 4, 5]]\n");
    assert_eq!(control.text, mono.text);
}

#[cfg(unix)]
#[test]
fn run_with_std_handles_effectful_thunk_returned_from_function() {
    let (mono, control) = run_with_std_main(
        "run-std-effectful-function-thunk-handler",
        "pub act out:\n\
             \x20 pub say: str -> ()\n\n\
             our add_and_say() =\n\
             \x20 my a = 1 + 2\n\
             \x20 out::say a.show\n\
             \x20 my b = a + 3\n\
             \x20 out::say b.show\n\
             \x20 a + b\n\n\
             our listen(x: [_] _, log: str): (_, str) = catch x:\n\
             \x20 out::say o, k -> listen(k (), log + o + \"\\n\")\n\
             \x20 v -> (v, log)\n\n\
             listen add_and_say() \"\"\n",
    );

    assert_eq!(mono.text, "run roots [(9, \"3\\n6\\n\")]\n");
    assert_eq!(control.text, mono.text);
}

#[cfg(unix)]
#[test]
fn dump_mono_with_std_specializes_nondet_sum_list_say_benchmark() {
    let root = temp_root("dump-mono-std-nondet-sum-list-say-benchmark");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    symlink_repo_lib(&root);
    fs::write(
        root.join("main.yu"),
        "(std::control::nondet::each(1..3) + std::control::nondet::each(1..2)).list.say\n",
    )
    .unwrap();

    let output = dump_mono_from_entry_with_std(root.join("main.yu")).unwrap();

    assert_mono_dump_contains(
        &output,
        "mono roots [force-thunk[thunk[[std::io::console::out], unit]",
    );
    assert_mono_dump_contains(&output, ".list <method>");
    assert_mono_dump_contains(&output, ".say <method>");
    assert_mono_dump_contains(&output, "<effect-op std::io::console::out::write>");
    assert_mono_dump_contains(&output, "std::control::nondet::nondet");
}

#[cfg(unix)]
#[test]
fn run_with_std_nondet_sum_list_say_reports_unhandled_out() {
    let root = temp_root("run-std-nondet-sum-list-say-unhandled-out");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    symlink_repo_lib(&root);
    fs::write(
        root.join("main.yu"),
        "(std::control::nondet::each(1..3) + std::control::nondet::each(1..2)).list.say\n",
    )
    .unwrap();

    let mono = run_mono_from_entry_with_std(root.join("main.yu"));
    let control = run_control_from_entry_with_std(root.join("main.yu"));

    match mono {
        Err(RouteError::Runtime(mono_runtime::RuntimeError::UnhandledEffect { path })) => {
            assert_eq!(path, vec!["std", "io", "console", "out", "write"]);
        }
        other => panic!("expected mono unhandled out effect, got {other:?}"),
    }
    match control {
        Err(RouteError::Control(control_vm::RunError::Runtime(
            control_vm::RuntimeError::UnhandledEffect { path },
        ))) => {
            assert_eq!(path, vec!["std", "io", "console", "out", "write"]);
        }
        other => panic!("expected control unhandled out effect, got {other:?}"),
    }
}

#[test]
fn run_mono_without_std_runs_polymorphic_stack_handler_call() {
    let root = temp_root("run-mono-stack-handler");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("main.yu"),
        "pub act sub 'a:\n\
             \x20 pub return: 'a -> never\n\
             \x20 pub sub(x: [_] 'a): 'a = catch x:\n\
             \x20 \x20 return a, _ -> a\n\
             \x20 \x20 a -> a\n\n\
             sub::sub:\n\
             \x20 sub::return 0\n",
    )
    .unwrap();

    let output = run_mono_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_eq!(output.values, vec![mono_runtime::Value::Int(0)]);
    assert_eq!(output.text, "run roots [0]\n");
}

#[test]
fn run_mono_without_std_keeps_stack_handler_hygiene() {
    let root = temp_root("run-mono-stack-handler-hygiene");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("main.yu"),
        "pub act sub 'a:\n\
             \x20 pub return: 'a -> never\n\
             \x20 pub sub(x: [_] 'a): 'a = catch x:\n\
             \x20 \x20 return a, _ -> a\n\
             \x20 \x20 a -> a\n\n\
             our g h = sub::sub:\n\
             \x20 h 0\n\
             \x20 sub::return 1\n\n\
             sub::sub:\n\
             \x20 g \\i -> sub::return i\n\
             \x20 sub::return 2\n",
    )
    .unwrap();

    let output = run_mono_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_eq!(output.values, vec![mono_runtime::Value::Int(0)]);
    assert_eq!(output.text, "run roots [0]\n");
}

#[test]
fn run_control_without_std_keeps_stack_handler_hygiene() {
    let root = temp_root("run-control-stack-handler-hygiene");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("main.yu"),
        "pub act sub 'a:\n\
             \x20 pub return: 'a -> never\n\
             \x20 pub sub(x: [_] 'a): 'a = catch x:\n\
             \x20 \x20 return a, _ -> a\n\
             \x20 \x20 a -> a\n\n\
             our g h = sub::sub:\n\
             \x20 h 0\n\
             \x20 sub::return 1\n\n\
             sub::sub:\n\
             \x20 g \\i -> sub::return i\n\
             \x20 sub::return 2\n",
    )
    .unwrap();

    let output = run_control_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_eq!(output.values, vec![control_vm::Value::Int(0)]);
    assert_eq!(output.text, "run roots [0]\n");
}

#[test]
fn dump_mono_without_std_lowers_constructor_payload_effect_handler() {
    let root = temp_root("dump-mono-constructor-payload-effect-handler");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("main.yu"),
        "enum opt 'a:\n  none\n  some 'a\n\
             act eff:\n  our send: opt int -> int\n\
             catch eff::send(opt::some 1):\n\
             \x20 eff::send(opt::some x), k -> k(x)\n\
             \x20 value -> value\n",
    )
    .unwrap();

    let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_mono_dump_contains(&output, "<effect-op eff::send>");
    assert_mono_dump_contains(&output, "eff::send d2 d");
    assert_mono_dump_contains(&output, "force-thunk[thunk[[eff], int] => int ! [eff]]");
}

#[test]
fn dump_mono_without_std_computed_effect_binding_escapes_later_handler() {
    let root = temp_root("dump-mono-computed-effect-escapes-handler");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("main.yu"),
        "act out:\n  our say: int -> unit\n\
             my run = out::say(1)\n\
             my handled = catch run:\n\
             \x20 out::say msg, k -> k(())\n\
             \x20 value -> value\n",
    )
    .unwrap();

    let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_mono_dump_contains(&output, "mono roots [eval m0, eval m1]");
    assert_mono_dump_contains(
        &output,
        "m0 = d2 : unit\n  force-thunk[thunk[[out], unit] => unit ! [out]]((<effect-op out::say> 1))",
    );
    assert_mono_dump_contains(&output, "m1 = d3 : unit\n  catch m0: out::say d");
    assert!(
        !output.text.contains("catch force-thunk"),
        "{}",
        output.text
    );
}

#[test]
fn dump_mono_without_std_binds_constructor_case_payload_type() {
    let root = temp_root("dump-mono-constructor-case-payload");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("main.yu"),
        "enum opt 'a:\n  none\n  some 'a\n\
             my id x = x\n\
             case opt::some 1:\n\
             \x20 opt::some x -> id(x)\n\
             \x20 _ -> 0\n",
    )
    .unwrap();

    let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_mono_dump_contains(
        &output,
        "mono roots [case (<ctor d2 / 1> 1): d2 d6 -> (m0 d6), _ -> 0]",
    );
    assert_mono_dump_contains(&output, "m0 = d3 : int -> int");
}

#[test]
fn dump_mono_without_std_binds_record_case_field_type() {
    let root = temp_root("dump-mono-record-case-field");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("main.yu"),
        "my id x = x\n\
             case { width: 1 }:\n\
             \x20 { width } -> id(width)\n\
             \x20 _ -> 0\n",
    )
    .unwrap();

    let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_mono_dump_contains(
        &output,
        "mono roots [case {width: 1}: {width: d3} -> (m0 d3), _ -> 0]",
    );
    assert_mono_dump_contains(&output, "m0 = d0 : int -> int");
}

#[test]
fn dump_mono_without_std_specializes_record_field_select() {
    let root = temp_root("dump-mono-record-select");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("main.yu"),
        "my id x = x\nid(({ width: 1 }).width)\n",
    )
    .unwrap();

    let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_mono_dump_contains(&output, "mono roots [(m0 {width: 1}.width)]");
    assert_mono_dump_contains(&output, "m0 = d0 : int -> int");
}

#[test]
fn dump_mono_without_std_specializes_record_select_from_case_local() {
    let root = temp_root("dump-mono-record-select-case-local");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("main.yu"),
        "my id x = x\n\
             case { width: 1 }:\n\
             \x20 row -> id(row.width)\n",
    )
    .unwrap();

    let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_mono_dump_contains(&output, "mono roots [case {width: 1}: d3 -> (m0 d3.width)]");
    assert_mono_dump_contains(&output, "m0 = d0 : int -> int");
}

#[test]
fn run_control_without_std_applies_record_pattern_default() {
    let entry = write_main(
        "run-control-record-pattern-default",
        "my f({x = 1}) = x\nf {}\nf {x: 2}\n",
    );

    let output = run_control_from_entry(entry).unwrap();

    assert_eq!(output.file_count, 1);
    assert_eq!(output.text, "run roots [1, 2]\n");
}

#[test]
fn run_control_without_std_record_pattern_default_reads_earlier_field() {
    let entry = write_main(
        "run-control-record-pattern-default-previous-field",
        "my f({x = 1, y = x}) = y\nf {x: 3}\nf {}\n",
    );

    let output = run_control_from_entry(entry).unwrap();

    assert_eq!(output.file_count, 1);
    assert_eq!(output.text, "run roots [3, 1]\n");
}

#[test]
fn run_control_without_std_record_pattern_default_handles_effect() {
    let entry = write_main(
        "run-control-record-pattern-default-effect",
        "act signal:\n\
             \x20 our ping: () -> int\n\n\
             my f({x = signal::ping()}): int = x\n\n\
             catch (f {}):\n\
             \x20 signal::ping(), _ -> 7\n\
             \x20 value -> value\n",
    );

    let mono = run_mono_from_entry(&entry).unwrap();
    let control = run_control_from_entry(entry).unwrap();

    assert_eq!(mono.file_count, 1);
    assert_eq!(mono.values, vec![mono_runtime::Value::Int(7)]);
    assert_eq!(mono.text, "run roots [7]\n");
    assert_eq!(control.file_count, 1);
    assert_eq!(control.text, mono.text);
}
