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
fn dump_mono_without_std_forces_effectful_block_tail() {
    let root = temp_root("dump-mono-effectful-block-tail");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("main.yu"),
        "act out:\n  our say: int -> unit\n{\n  my x = 1\n  out::say(x)\n}\n",
    )
    .unwrap();

    let output = dump_mono_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_mono_dump_contains(&output, "mono roots [{ my ");
    assert_mono_dump_contains(
        &output,
        "; force-thunk[thunk[[out], unit] => unit ! [out]]((<effect-op out::say>",
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
fn run_evidence_without_std_evaluates_computed_top_level_binding_without_result() {
    let root = temp_root("run-evidence-computed-binding-no-result");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(root.join("main.yu"), "my id x = x\nmy a = id(1)\n").unwrap();

    let mono = run_mono_from_entry(root.join("main.yu")).unwrap();
    let evidence = run_evidence_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(mono.file_count, 1);
    assert_eq!(mono.values, Vec::<mono_runtime::Value>::new());
    assert_eq!(mono.text, "run roots []\n");
    assert_eq!(evidence.file_count, 1);
    assert_eq!(evidence.text, mono.text);
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
fn run_evidence_without_std_runs_apply_colon_block_argument() {
    let root = temp_root("run-evidence-apply-colon-block-arg");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(root.join("main.yu"), "my id x = x\nid:\n  my x = 1\n  x\n").unwrap();

    let output = run_evidence_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
    assert_eq!(output.text, "run roots [1]\n");
}

#[test]
fn run_without_std_matches_evidence_on_record_case_and_handler_smoke() {
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
    let evidence = run_evidence_from_entry(&entry).unwrap();

    assert_eq!(mono.text, "run roots [2, 1]\n");
    assert_eq!(evidence.text, mono.text);
}

#[test]
fn run_without_std_matches_evidence_on_struct_field_projection() {
    let entry = write_main(
        "run-struct-field-projection",
        "struct User { age: int }\nUser({ age: 1 }).age\n",
    );

    let mono = run_mono_from_entry(&entry).unwrap();
    let evidence = run_evidence_from_entry(&entry).unwrap();

    assert_eq!(mono.text, "run roots [1]\n");
    assert_eq!(evidence.text, mono.text);
}

#[test]
fn run_without_std_resolves_receiverless_role_method_path() {
    let entry = write_main(
        "run-receiverless-role-method-path",
        "struct User { value: int }\n\
         role Convert 'a:\n\
         \x20 our convert: 'a -> int\n\
         impl User: Convert {\n\
         \x20 our convert u = u.value\n\
         }\n\
         Convert::convert(User { value: 4 })\n",
    );

    let mono = run_mono_from_entry(&entry).unwrap();
    let evidence = run_evidence_from_entry(entry).unwrap();

    assert_eq!(mono.text, "run roots [4]\n");
    assert_eq!(evidence.text, mono.text);
}

#[cfg(unix)]
#[test]
fn run_with_std_matches_evidence_on_core_smoke_suite() {
    let entry = write_main_with_std(
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
    let mono = run_mono_from_entry_with_std(&entry).unwrap();
    let evidence_text = run_with_vm_test_stack({
        let entry = entry.clone();
        move || run_evidence_from_entry_with_std(entry).unwrap().text
    });

    assert_eq!(
        mono.text,
        "run roots [7, [4, 3], \"sum=3\", \"hex=ff\", \"debug=[1, 2]\", \"pad=0007\", 1]\n"
    );
    assert_eq!(evidence_text, mono.text);
}

#[cfg(unix)]
#[test]
fn yumark_nil_text_renders_expected_html_and_markdown_bytes() {
    let entry = write_main_with_std(
        "yumark-nil-text-output",
        concat!(
            "use std::text::yumark::*\n",
            "my empty = '[]\n",
            "my plain = '[hello world]\n",
            "html_tag (render_html_doc empty)\n",
            "render_markdown_doc empty\n",
            "html_tag (render_html_doc plain)\n",
            "render_markdown_doc plain\n",
        ),
    );
    let output = run_mono_from_entry_with_std(&entry).unwrap();

    let expected = "run roots [\"\", \"\", \"<span>hello world</span>\", \"hello world\"]\n";
    assert_eq!(output.text, expected);
}

#[cfg(unix)]
#[test]
fn explicit_yumark_blank_line_builder_remains_visible() {
    let entry = write_main_with_std(
        "yumark-explicit-blank-line-output",
        concat!(
            "use std::text::yumark::*\n",
            "html_tag (render_html_doc (blank_line \"manual-spacer\"))\n",
            "render_markdown_doc (blank_line \"manual-spacer\")\n",
        ),
    );
    let output = run_mono_from_entry_with_std(&entry).unwrap();

    assert_eq!(
        output.text,
        "run roots [\"<br>manual-spacer</br>\", \"manual-spacer\"]\n"
    );
}

#[test]
fn doc_comment_static_renderer_matches_production_markdown_vocabulary() {
    fn render_static_doc(source: &str) -> String {
        let loaded = sources::load(vec![sources::SourceFile {
            module_path: sources::Path::default(),
            source: source.to_string(),
        }]);
        let lower = infer::lowering::lower_loaded_files(&loaded).expect("lower doc fixture");
        let root = lower.modules.root_id();
        let def = lower.modules.value_decls(root, &sources::Name("x".into()))[0].def;
        let doc = lower
            .modules
            .def_doc_comment(def)
            .expect("doc comment should attach to x");
        infer::doc_comment_render::render_doc_comment_markdown(doc)
    }

    let static_renderings = [
        render_static_doc("-- paragraph\nmy x = 1\n"),
        render_static_doc("-- first\n-- second\nmy x = 1\n"),
        render_static_doc("---\n## Heading\n---\nmy x = 1\n"),
        render_static_doc("---\n- first\n- second\n---\nmy x = 1\n"),
        render_static_doc("---\n```text\nalpha\nbeta\n```\n---\nmy x = 1\n"),
        render_static_doc("---\n> quoted\n---\nmy x = 1\n"),
        render_static_doc("---\r\nalpha\r\nbeta\r\n---\r\nmy x = 1\r\n"),
        render_static_doc("--  leading and trailing  \nmy x = 1\n"),
    ];
    let expected = format!(
        "run roots [{}]\n",
        static_renderings
            .iter()
            .map(|rendered| format!("{rendered:?}"))
            .collect::<Vec<_>>()
            .join(", ")
    );
    // Contiguous line docs share one ordinary paragraph literal. Fence and
    // quote use the same public builders emitted by literal lowering.
    let production_source = concat!(
        "use std::text::yumark::*\n",
        "render_markdown_doc ('{paragraph\n})\n",
        "render_markdown_doc ('{first\nsecond\n})\n",
        "render_markdown_doc ('{## Heading\n})\n",
        "render_markdown_doc ('{- first\n- second\n})\n",
        "render_markdown_doc (code_fence \"text\" \"alpha\\nbeta\")\n",
        "render_markdown_doc (quote_block (paragraph (text \"quoted\")))\n",
        "render_markdown_doc ('{alpha\r\nbeta\r\n})\n",
        "render_markdown_doc ('{ leading and trailing\n})\n",
    );
    let production = run_with_vm_test_stack(move || {
        run_evidence_from_source_text_with_embedded_std(
            "<doc-comment-render-parity>",
            production_source,
        )
        .expect("run production Yumark Markdown renderer")
        .text
    });

    assert_eq!(production, expected);
}

#[cfg(unix)]
#[test]
fn yumark_full_static_renders_consistently_with_minimal_and_repository_std() {
    let literal = concat!(
        "'{## Static vocabulary\n",
        "Paragraph with *emphasis* and **strong**.\n",
        "\n",
        "#.\n",
        "- bullet *item*\n",
        "1. numbered **item**\n",
        "```text\n",
        "line one\n",
        "line two\n",
        "```\n",
        "> quoted\n",
        "}\n",
    );
    let entry = write_main_with_std(
        "yumark-full-static-output",
        &format!(
            "use std::text::yumark::*\nmy rich = {literal}html_tag (render_html_doc rich)\nrender_markdown_doc rich\n"
        ),
    );
    let (minimal, repository) = run_with_vm_test_stack(move || {
        let minimal = run_mono_with_minimal_yumark_std(&entry).text;
        let repository = run_mono_from_entry_with_std(&entry).unwrap().text;
        (minimal, repository)
    });

    assert_eq!(minimal, repository);
}

#[cfg(unix)]
#[test]
fn yumark_full_static_construction_does_not_force_interpretation_effects() {
    let entry = write_main_with_std(
        "yumark-full-static-inert",
        concat!(
            "use std::text::str::str\n",
            "use std::text::yumark::{yumark_algebra}\n",
            "act full_static_construction_probe:\n",
            "  our fire: () -> str\n",
            "struct effect_repr {\n",
            "  marker: str,\n",
            "  run: () -> [full_static_construction_probe] str,\n",
            "}\n",
            "my effect_value(): effect_repr = effect_repr {\n",
            "  marker: \"\",\n",
            "  run: \\() -> full_static_construction_probe::fire(),\n",
            "}\n",
            "my effect_nil(): effect_repr = effect_repr {\n",
            "  marker: \"\",\n",
            "  run: \\() -> \"\",\n",
            "}\n",
            "my effect_cons(head: effect_repr, tail: effect_repr): effect_repr = effect_repr {\n",
            "  marker: std::text::str::concat head.marker tail.marker,\n",
            "  run: \\() -> std::text::str::concat (head.run()) (tail.run()),\n",
            "}\n",
            "my effect_text(value: str): effect_repr = effect_value()\n",
            "my effect_paragraph(children: effect_repr): effect_repr = children\n",
            "my effect_heading(marker: str, level: int, children: effect_repr): effect_repr = children\n",
            "my effect_blank_line(marker: str): effect_repr = effect_value()\n",
            "my effect_section_close(marker: str, children: effect_repr): effect_repr = children\n",
            "my effect_list_block(ordered: bool, items: effect_repr): effect_repr = items\n",
            "my effect_list_item(marker: str, children: effect_repr): effect_repr = children\n",
            "my effect_list_item_body(children: effect_repr): effect_repr = children\n",
            "my effect_code_fence(info: str, body: str): effect_repr = effect_value()\n",
            "my effect_quote_block(children: effect_repr): effect_repr = children\n",
            "my effect_emphasis(children: effect_repr): effect_repr = children\n",
            "my effect_strong(children: effect_repr): effect_repr = children\n",
            "my effect_algebra(): yumark_algebra effect_repr = yumark_algebra {\n",
            "  nil: effect_nil,\n",
            "  cons: effect_cons,\n",
            "  text: effect_text,\n",
            "  paragraph: effect_paragraph,\n",
            "  heading: effect_heading,\n",
            "  blank_line: effect_blank_line,\n",
            "  section_close: effect_section_close,\n",
            "  list_block: effect_list_block,\n",
            "  list_item: effect_list_item,\n",
            "  list_item_body: effect_list_item_body,\n",
            "  code_fence: effect_code_fence,\n",
            "  quote_block: effect_quote_block,\n",
            "  emphasis: effect_emphasis,\n",
            "  strong: effect_strong,\n",
            "}\n",
            "my document = '{## Static vocabulary\n",
            "Paragraph with *emphasis* and **strong**.\n",
            "\n",
            "#.\n",
            "- bullet *item*\n",
            "1. numbered **item**\n",
            "```text\n",
            "line one\n",
            "line two\n",
            "```\n",
            "> quoted\n",
            "}\n",
            "my selected = document((), effect_algebra())\n",
            "selected.marker\n",
        ),
    );

    let output_text = run_with_vm_test_stack(move || run_mono_with_minimal_yumark_std(&entry).text);

    assert_eq!(output_text, "run roots [\"\"]\n");
}

#[cfg(unix)]
fn run_mono_with_minimal_yumark_std(entry: &FsPath) -> RunMonoOutput {
    let mut files = collect_local_sources(entry).unwrap();
    let root = entry.parent().expect("Yumark test entry parent");
    let mut push = |segments: &[&str], source: &str| {
        files.push(CollectedSource::new(
            root.join(format!("{}.yu", segments.join("-"))),
            Path {
                segments: segments
                    .iter()
                    .map(|segment| Name((*segment).to_string()))
                    .collect(),
            },
            source.to_string(),
        ));
    };

    push(
        &["std"],
        "pub mod core;\npub mod control;\npub mod int;\npub mod text;\n",
    );
    push(&["std", "core"], "pub mod cmp;\npub mod ops;\n");
    push(
        &["std", "core", "cmp"],
        concat!(
            "use std::text::str::str\n",
            "pub role Eq 'a:\n",
            "  pub a.eq: 'a -> bool\n",
            "impl str: Eq:\n",
            "  our x.eq y = std::text::str::eq x y\n",
        ),
    );
    push(
        &["std", "core", "ops"],
        concat!(
            "use std::core::cmp::*\n",
            "pub infix (==) 3.0.0 3.0.1 = \\x -> \\y -> x.eq y\n",
        ),
    );
    push(&["std", "control"], "pub mod junction;\n");
    push(
        &["std", "control", "junction"],
        concat!(
            "pub act junction:\n",
            "  my or: () -> bool\n",
            "  my and: () -> bool\n",
            "  my ret: bool -> never\n",
            "  pub junction(x: [_] _) = catch x:\n",
            "    or(), k -> case junction(k true):\n",
            "      true -> true\n",
            "      _ -> junction(k false)\n",
            "    and(), k -> case junction(k true):\n",
            "      true -> junction(k false)\n",
            "      _ -> false\n",
            "    ret b, _ -> b\n",
        ),
    );
    push(
        &["std", "int"],
        concat!(
            "use std::text::str::str\n",
            "pub to_string: int -> str = builtin_op::int_to_string\n",
        ),
    );
    push(&["std", "text"], "pub mod str;\npub mod yumark;\n");
    push(
        &["std", "text", "str"],
        concat!(
            "pub type str\n",
            "pub concat: str -> str -> str = builtin_op::string_concat\n",
            "pub eq: str -> str -> bool = builtin_op::string_eq\n",
        ),
    );
    push(
        &["std", "text", "yumark"],
        &format!(
            "use std::core::ops::*\n{}",
            include_str!("../../../../../lib/std/text/yumark.yu")
        ),
    );
    run_mono_from_sources(files).unwrap()
}

#[cfg(unix)]
#[test]
fn yumark_nil_text_construction_does_not_force_interpretation_effects() {
    let entry = write_main_with_std(
        "yumark-nil-text-inert",
        concat!(
            "use std::text::yumark::{yumark_algebra}\n",
            "struct effect_repr {\n",
            "  marker: str,\n",
            "  run: () -> [std::time::clock] str,\n",
            "}\n",
            "my effect_nil(): effect_repr = effect_repr {\n",
            "  marker: \"\",\n",
            "  run: \\() -> \"\",\n",
            "}\n",
            "my effect_cons(head: effect_repr, tail: effect_repr): effect_repr = effect_repr {\n",
            "  marker: std::text::str::concat head.marker tail.marker,\n",
            "  run: \\() -> std::text::str::concat (head.run()) (tail.run()),\n",
            "}\n",
            "my effect_text(value: str): effect_repr = effect_repr {\n",
            "  marker: value,\n",
            "  run: \\() ->\n",
            "    my _ = std::time::clock::now()\n",
            "    value\n",
            "}\n",
            "my effect_paragraph(children: effect_repr): effect_repr = children\n",
            "my effect_heading(marker: str, level: int, children: effect_repr): effect_repr = children\n",
            "my effect_blank_line(marker: str): effect_repr = effect_text(marker)\n",
            "my effect_section_close(marker: str, children: effect_repr): effect_repr = children\n",
            "my effect_list_block(ordered: bool, items: effect_repr): effect_repr = items\n",
            "my effect_list_item(marker: str, children: effect_repr): effect_repr = children\n",
            "my effect_list_item_body(children: effect_repr): effect_repr = children\n",
            "my effect_code_fence(info: str, body: str): effect_repr = effect_text(body)\n",
            "my effect_quote_block(children: effect_repr): effect_repr = children\n",
            "my effect_emphasis(children: effect_repr): effect_repr = children\n",
            "my effect_strong(children: effect_repr): effect_repr = children\n",
            "my effect_algebra(): yumark_algebra effect_repr = yumark_algebra {\n",
            "  nil: effect_nil,\n",
            "  cons: effect_cons,\n",
            "  text: effect_text,\n",
            "  paragraph: effect_paragraph,\n",
            "  heading: effect_heading,\n",
            "  blank_line: effect_blank_line,\n",
            "  section_close: effect_section_close,\n",
            "  list_block: effect_list_block,\n",
            "  list_item: effect_list_item,\n",
            "  list_item_body: effect_list_item_body,\n",
            "  code_fence: effect_code_fence,\n",
            "  quote_block: effect_quote_block,\n",
            "  emphasis: effect_emphasis,\n",
            "  strong: effect_strong,\n",
            "}\n",
            "my document = '[hello world]\n",
            "my selected = document((), effect_algebra())\n",
            "selected.marker\n",
        ),
    );

    let output = run_mono_from_entry_with_std(&entry).unwrap();

    assert_eq!(output.text, "run roots [\"hello world\"]\n");
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
    let evidence = run_evidence_from_entry_with_std(root.join("main.yu")).unwrap();

    assert!(mono.text.contains("([1], [2])"), "{}", mono.text);
    assert!(evidence.text.contains("([1], [2])"), "{}", evidence.text);
}

#[cfg(unix)]
#[test]
fn run_with_std_handles_composed_nested_effect_contracts() {
    let entry = write_main_with_std(
        "run-std-composed-nested-effect-contracts",
        "act flip:\n\
             \x20 our coin: () -> bool\n\
             act amount:\n\
             \x20 our coin: () -> int\n\n\
             our all_paths(action: [flip] _) = catch action:\n\
             \x20 flip::coin(), k -> all_paths(k true) + all_paths(k false)\n\
             \x20 v -> [v]\n\n\
             our total_amount(action: [amount] _) =\n\
             \x20 my loop(n, action: [amount] _) = catch action:\n\
             \x20 \x20 amount::coin(), k -> loop(n, k n)\n\
             \x20 \x20 v -> v\n\
             \x20 [loop(1, action), loop(2, action)]\n\n\
             our compose(f, g: _ -> [_] _, x: [_] _) = f g(x)\n\n\
             compose(total_amount, all_paths):\n\
             \x20 my a = if flip::coin(): amount::coin() else: 0\n\
             \x20 my b = if flip::coin(): amount::coin() * 10 else: 0\n\
             \x20 my c = if flip::coin(): amount::coin() * 100 else: 0\n\
             \x20 a + b + c\n",
    );

    let evidence_text = run_with_vm_test_stack({
        let entry = entry.clone();
        move || run_evidence_from_entry_with_std(entry).unwrap().text
    });

    assert_eq!(
        evidence_text,
        "run roots [[[111, 11, 101, 1, 110, 10, 100, 0], [222, 22, 202, 2, 220, 20, 200, 0]]]\n"
    );
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
fn run_evidence_with_std_collects_nondet_each_list() {
    let root = temp_root("run-evidence-std-nondet-each-list");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    symlink_repo_lib(&root);
    fs::write(
        root.join("main.yu"),
        "std::control::nondet::each(1..3).list\n",
    )
    .unwrap();

    let output = run_evidence_from_entry_with_std(root.join("main.yu")).unwrap();

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
    let evidence_text = run_with_vm_test_stack({
        let entry = root.join("main.yu");
        move || run_evidence_from_entry_with_std(entry).unwrap().text
    });

    assert_eq!(mono.text, "run roots [[2, 3, 3, 4, 4, 5]]\n");
    assert_eq!(evidence_text, mono.text);
}

#[cfg(unix)]
#[test]
fn run_with_std_handles_effectful_thunk_returned_from_function() {
    let (mono, evidence) = run_with_std_main(
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
    assert_eq!(evidence.text, mono.text);
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
fn run_with_std_nondet_sum_list_say_handles_evidence_stdout() {
    let root = temp_root("run-std-nondet-sum-list-say-control-stdout");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    symlink_repo_lib(&root);
    fs::write(
        root.join("main.yu"),
        "(std::control::nondet::each(1..3) + std::control::nondet::each(1..2)).list.say\n",
    )
    .unwrap();

    let mono = run_mono_from_entry_with_std(root.join("main.yu"));
    let evidence = run_with_vm_test_stack({
        let entry = root.join("main.yu");
        move || {
            let output = run_evidence_from_entry_with_std(entry)
                .expect("evidence VM route should handle console out");
            (output.stdout, output.text)
        }
    });

    match mono {
        Err(RouteError::Runtime(mono_runtime::RuntimeError::UnhandledEffect { path })) => {
            assert_eq!(path, vec!["std", "io", "console", "out", "write"]);
        }
        other => panic!("expected mono unhandled out effect, got {other:?}"),
    }
    assert_eq!(evidence.0, "[2, 3, 3, 4, 4, 5]\n");
    assert_eq!(evidence.1, "run roots [()]\n");
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
fn run_evidence_without_std_keeps_stack_handler_hygiene() {
    let root = temp_root("run-evidence-stack-handler-hygiene");
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

    let output = run_evidence_from_entry(root.join("main.yu")).unwrap();

    assert_eq!(output.file_count, 1);
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
fn run_evidence_without_std_applies_record_pattern_default() {
    let entry = write_main(
        "run-evidence-record-pattern-default",
        "my f({x = 1}) = x\nf {}\nf {x: 2}\n",
    );

    let output = run_evidence_from_entry(entry).unwrap();

    assert_eq!(output.file_count, 1);
    assert_eq!(output.text, "run roots [1, 2]\n");
}

#[test]
fn run_evidence_without_std_record_pattern_default_reads_earlier_field() {
    let entry = write_main(
        "run-evidence-record-pattern-default-previous-field",
        "my f({x = 1, y = x}) = y\nf {x: 3}\nf {}\n",
    );

    let output = run_evidence_from_entry(entry).unwrap();

    assert_eq!(output.file_count, 1);
    assert_eq!(output.text, "run roots [3, 1]\n");
}

#[test]
fn run_evidence_without_std_record_pattern_default_handles_effect() {
    let entry = write_main(
        "run-evidence-record-pattern-default-effect",
        "act signal:\n\
             \x20 our ping: () -> int\n\n\
             my f({x = signal::ping()}): int = x\n\n\
             catch (f {}):\n\
             \x20 signal::ping(), _ -> 7\n\
             \x20 value -> value\n",
    );

    let mono = run_mono_from_entry(&entry).unwrap();
    let evidence = run_evidence_from_entry(entry).unwrap();

    assert_eq!(mono.file_count, 1);
    assert_eq!(mono.values, vec![mono_runtime::Value::Int(7)]);
    assert_eq!(mono.text, "run roots [7]\n");
    assert_eq!(evidence.file_count, 1);
    assert_eq!(evidence.text, mono.text);
}
