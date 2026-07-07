use super::*;

mod tests {
    use super::*;

    fn on_test_stack<T>(work: impl FnOnce() -> T + Send + 'static) -> T
    where
        T: Send + 'static,
    {
        std::thread::Builder::new()
            .name("wasm-run-inner-test-stack".to_string())
            .stack_size(16 * 1024 * 1024)
            .spawn(work)
            .unwrap()
            .join()
            .unwrap()
    }

    fn run_inner_on_test_stack(source: &str) -> RunOutput {
        let source = source.to_string();
        on_test_stack(move || run_inner(&source))
    }

    fn assert_public_type_display_has_no_private_markers(ty: &str, context: &str) {
        for marker in ["#", "AllExcept", "stack(", "<:", "\""] {
            assert!(
                !ty.contains(marker),
                "private type marker {marker:?} escaped into {context}:\n{ty}"
            );
        }
    }

    fn playground_showcase_source(en_label: &str) -> &'static str {
        const PLAYGROUND_MAIN_TS: &str = include_str!("../../../web/playground/src/main.ts");
        let label_marker = format!("en: \"{en_label}\"");
        let label_start = PLAYGROUND_MAIN_TS
            .find(&label_marker)
            .unwrap_or_else(|| panic!("missing playground showcase label: {en_label}"));
        let source_marker = "source: `";
        let source_start = label_start
            + PLAYGROUND_MAIN_TS[label_start..]
                .find(source_marker)
                .unwrap_or_else(|| panic!("missing source for playground showcase: {en_label}"))
            + source_marker.len();
        let source_rest = &PLAYGROUND_MAIN_TS[source_start..];
        let source_end = source_rest.find("\n`,").unwrap_or_else(|| {
            panic!("missing source terminator for playground showcase: {en_label}")
        });
        &source_rest[..source_end + 1]
    }

    const PARSER_PATTERN_SHOWCASE: &str = r#"use std::text::parse::*

my route line = case line:
    ~"get :key" -> "GET " + key
    ~"set :key {v = ..}" -> "SET " + key + " = " + v
    rule { id = word } if id.starts_with "a" -> "user " + id
    _ -> "unknown"

route "get color" .say
route "set color deep-blue" .say
route "alice" .say
route "???" .say
"#;

    fn diagnostics_fixture(name: &str) -> &'static str {
        match name {
            "type_annotation_mismatch" => include_str!(
                "../../../tests/yulang/regressions/diagnostics/type_annotation_mismatch.yu"
            ),
            "unresolved_value_name" => include_str!(
                "../../../tests/yulang/regressions/diagnostics/unresolved_value_name.yu"
            ),
            "unresolved_type_name" => include_str!(
                "../../../tests/yulang/regressions/diagnostics/unresolved_type_name.yu"
            ),
            "unsupported_record_type_annotation" => include_str!(
                "../../../tests/yulang/regressions/diagnostics/unsupported_record_type_annotation.yu"
            ),
            "top_level_mutable_binding" => include_str!(
                "../../../tests/yulang/regressions/diagnostics/top_level_mutable_binding.yu"
            ),
            "unclosed_paren" => {
                include_str!("../../../tests/yulang/regressions/diagnostics/unclosed_paren.yu")
            }
            "trailing_operator" => {
                include_str!("../../../tests/yulang/regressions/diagnostics/trailing_operator.yu")
            }
            "rule_lazy_quantifier" => include_str!(
                "../../../tests/yulang/regressions/diagnostics/rule_lazy_quantifier.yu"
            ),
            "case_missing_scrutinee" => include_str!(
                "../../../tests/yulang/regressions/diagnostics/case_missing_scrutinee.yu"
            ),
            "case_missing_arm_pattern" => include_str!(
                "../../../tests/yulang/regressions/diagnostics/case_missing_arm_pattern.yu"
            ),
            "case_missing_arm_body" => include_str!(
                "../../../tests/yulang/regressions/diagnostics/case_missing_arm_body.yu"
            ),
            "catch_missing_scrutinee" => include_str!(
                "../../../tests/yulang/regressions/diagnostics/catch_missing_scrutinee.yu"
            ),
            "catch_raw_brace_scrutinee" => include_str!(
                "../../../tests/yulang/regressions/diagnostics/catch_raw_brace_scrutinee.yu"
            ),
            "catch_missing_arm_pattern" => include_str!(
                "../../../tests/yulang/regressions/diagnostics/catch_missing_arm_pattern.yu"
            ),
            "catch_missing_arm_body" => include_str!(
                "../../../tests/yulang/regressions/diagnostics/catch_missing_arm_body.yu"
            ),
            "missing_index_argument" => include_str!(
                "../../../tests/yulang/regressions/diagnostics/missing_index_argument.yu"
            ),
            "unresolved_method_error" => {
                include_str!("../../../tests/yulang/regressions/runtime/unresolved_method_error.yu")
            }
            "ambiguous_method_error" => {
                include_str!("../../../tests/yulang/regressions/runtime/ambiguous_method_error.yu")
            }
            "not_callable_error" => {
                include_str!("../../../tests/yulang/regressions/runtime/not_callable_error.yu")
            }
            _ => panic!("unknown diagnostics fixture: {name}"),
        }
    }

    #[test]
    fn playground_worker_keeps_session_after_continuation_runs() {
        const PLAYGROUND_MAIN_TS: &str = include_str!("../../../web/playground/src/main.ts");
        const RUN_WORKER_TS: &str = include_str!("../../../web/playground/src/run-worker.ts");

        let retry_tail = PLAYGROUND_MAIN_TS
            .split_once("async function requestRunWithWorkerRetry")
            .expect("playground should keep worker retry entrypoint")
            .1;
        let retry_body = retry_tail
            .split_once("\n}\n\nasync function requestRunOrError")
            .expect("playground worker retry body should stay locally testable")
            .0;

        assert_eq!(
            retry_body.matches("resetRunWorker(").count(),
            1,
            "worker retry should reset only after trap-like failures, not after successful continuation runs:\n{retry_body}"
        );
        assert!(
            !retry_body.contains("vm_continuation_steps")
                && !retry_body.contains("resetWorkerAfterContinuationRun"),
            "successful continuation runs should not trigger worker recycling:\n{retry_body}"
        );
        assert!(
            !RUN_WORKER_TS.contains("clear_std_cache")
                && !RUN_WORKER_TS.contains("cache_cleared")
                && !RUN_WORKER_TS.contains("last_run_cleared_cache"),
            "run-worker should not clear wasm caches after continuation-heavy runs"
        );
    }

    #[test]
    fn playground_docs_links_keep_file_backed_install_and_clean_redirects() {
        const PLAYGROUND_INDEX_HTML: &str = include_str!("../../../web/playground/index.html");
        const PLAYGROUND_MAIN_TS: &str = include_str!("../../../web/playground/src/main.ts");
        const DOCS_EXTERNALIZE_SCRIPT: &str =
            include_str!("../../../web/docs/scripts/externalize-inline-scripts.mjs");

        assert!(
            PLAYGROUND_INDEX_HTML
                .contains(r#"href="/ja/guide/install.html" data-doc-link="install""#),
            "static playground install link should target the generated file-backed docs URL"
        );
        assert!(
            PLAYGROUND_MAIN_TS.contains(r#"install: { href: "/ja/guide/install.html""#),
            "Japanese runtime doc link should keep the file-backed install URL"
        );
        assert!(
            PLAYGROUND_MAIN_TS.contains(r#"install: { href: "/guide/install.html""#),
            "English runtime doc link should keep the file-backed install URL"
        );
        assert!(PLAYGROUND_MAIN_TS.contains("redirectCleanDocsPath();"));
        assert!(PLAYGROUND_MAIN_TS.contains("target = `${pathname}/`;"));
        assert!(PLAYGROUND_MAIN_TS.contains("target = `${pathname}.html`;"));
        assert!(DOCS_EXTERNALIZE_SCRIPT.contains("await createCleanUrlIndexes(webOutDir);"));
        assert!(DOCS_EXTERNALIZE_SCRIPT.contains("filename !== \"404.html\""));
    }

    #[test]
    fn playground_colorizer_keeps_plain_html_fallback() {
        const PLAYGROUND_MAIN_TS: &str = include_str!("../../../web/playground/src/main.ts");

        assert!(
            PLAYGROUND_MAIN_TS.contains("function colorizedSourceHtml(source: string): string")
        );
        assert!(PLAYGROUND_MAIN_TS.contains("try {\n        const output = colorize(source)"));
        assert!(
            PLAYGROUND_MAIN_TS
                .contains("const spans = Array.isArray(output.spans) ? output.spans : [];")
        );
        assert!(PLAYGROUND_MAIN_TS.contains("return highlightSource(source, spans);"));
        assert!(PLAYGROUND_MAIN_TS.contains("reportColorizeFallback(error);"));
        assert!(PLAYGROUND_MAIN_TS.contains("return plainSourceHtml(source);"));
        assert!(PLAYGROUND_MAIN_TS.contains("function plainSourceHtml(source: string): string"));
        assert!(
            PLAYGROUND_MAIN_TS.contains(
                "console.warn(\"Yulang colorizer failed; rendering plain source\", error);"
            )
        );
    }

    fn assert_type_annotation_mismatch_diagnostic(diagnostic: &Diagnostic) {
        assert_eq!(diagnostic.label.as_deref(), Some("x"));
        assert_eq!(diagnostic.code.as_deref(), Some("yulang.type-mismatch"));
        assert_eq!(diagnostic.start, 3);
        assert_eq!(diagnostic.end, 4);
        assert_eq!(diagnostic.message, "type mismatch: bool is not int");
        assert_eq!(diagnostic.hint, None);
        assert_eq!(diagnostic.related.len(), 2);
        assert_eq!(
            diagnostic.related[0].message,
            "expected type comes from this type annotation: int"
        );
        assert_eq!(
            diagnostic.related[0].origin.as_deref(),
            Some("type_annotation")
        );
        assert_eq!(diagnostic.related[0].start, 6);
        assert_eq!(diagnostic.related[0].end, 9);
        assert_eq!(
            diagnostic.related[1].message,
            "actual type comes from this expression: bool"
        );
        assert_eq!(diagnostic.related[1].origin.as_deref(), Some("expression"));
        assert_eq!(diagnostic.related[1].start, 12);
        assert_eq!(diagnostic.related[1].end, 16);
    }

    #[test]
    fn run_inner_uses_no_std_fast_path_for_core_source() {
        clear_std_cache();
        let output = run_inner("my id x = x\nid(42)\n");

        assert!(output.ok, "{output:?}");
        assert_eq!(output.file_count, 1);
        assert_eq!(
            output
                .timings
                .as_ref()
                .map(|timing| timing.used_embedded_std),
            Some(false)
        );
        assert_eq!(
            output.results.first().map(|result| result.value.as_str()),
            Some("42")
        );
        assert_eq!(output.text, "run roots [42]\n");
    }

    #[test]
    fn run_inner_retries_unresolved_core_names_with_embedded_std() {
        clear_std_cache();
        let output = run_inner("1 + 2\n");

        assert!(output.ok, "{output:?}");
        assert_eq!(
            output
                .timings
                .as_ref()
                .map(|timing| timing.used_embedded_std),
            Some(true)
        );
        assert_eq!(
            output.results.first().map(|result| result.value.as_str()),
            Some("3")
        );
        assert_eq!(output.text, "run roots [3]\n");
    }

    #[test]
    fn run_inner_uses_compact_playground_std_for_mixed_numeric_add() {
        clear_std_cache();
        let output = run_inner("1 + 1.2\n");

        assert!(output.ok, "{output:?}");
        assert_eq!(
            output
                .timings
                .as_ref()
                .map(|timing| timing.used_embedded_std),
            Some(true)
        );
        assert_eq!(
            output.results.first().map(|result| result.value.as_str()),
            Some("2.2")
        );
        assert_eq!(output.text, "run roots [2.2]\n");
        assert!(output.file_count < yulang::stdlib::embedded_std_files().len() + 1);
    }

    #[test]
    fn embedded_playground_std_artifact_status_is_valid() {
        let output = embedded_std_status_inner();

        assert!(output.valid, "{output:?}");
        assert_eq!(output.artifacts, 2);
        assert!(output.bytes > 0);
        assert_eq!(output.fallback_reason, None);
    }

    #[test]
    fn run_inner_uses_compact_playground_std_for_struct_method_example() {
        clear_std_cache();
        let output = run_inner(
            "\
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

point { x: 3, y: 4 } .norm2 + 1.12
",
        );

        assert!(output.ok, "{output:?}");
        assert_eq!(
            output
                .timings
                .as_ref()
                .map(|timing| timing.used_embedded_std),
            Some(true)
        );
        assert_eq!(
            output.results.first().map(|result| result.value.as_str()),
            Some("26.12")
        );
        assert_eq!(output.text, "run roots [26.12]\n");
        assert!(output.file_count < yulang::stdlib::embedded_std_files().len() + 1);
    }

    #[test]
    fn run_inner_uses_compact_playground_std_for_list_update_example() {
        clear_std_cache();
        let output = run_inner(
            "\
{
    my $xs = [
        2
        3
        4
    ]
    &xs[1] = 6
    $xs
}
",
        );

        assert!(output.ok, "{output:?}");
        assert_eq!(
            output
                .timings
                .as_ref()
                .map(|timing| timing.used_embedded_std),
            Some(true)
        );
        assert_eq!(
            output.results.first().map(|result| result.value.as_str()),
            Some("[2, 6, 4]")
        );
        assert_eq!(output.text, "run roots [[2, 6, 4]]\n");
        assert!(output.file_count < yulang::stdlib::embedded_std_files().len() + 1);
    }

    #[test]
    fn run_inner_runs_parser_pattern_showcase() {
        clear_std_cache();
        let output = run_inner_on_test_stack(PARSER_PATTERN_SHOWCASE);

        assert!(output.ok, "{output:?}");
        assert_eq!(
            output.stdout,
            "Output 1: GET color\nOutput 2: SET color = deep-blue\nOutput 3: user alice\nOutput 4: unknown\n"
        );
        assert_eq!(output.text, "run roots [(), (), (), ()]\n");
    }

    #[test]
    fn run_inner_runs_config_showcase_from_playground_source() {
        clear_std_cache();
        let output = run_inner_on_test_stack(playground_showcase_source("Config"));

        assert!(output.ok, "{output:?}");
        assert!(output.stdout.contains("8080"), "{output:?}");
        assert!(output.stdout.contains("api"), "{output:?}");
    }

    #[test]
    fn run_inner_uses_embedded_std_only_when_needed() {
        clear_std_cache();
        let output = run_inner("each(1..3).list\n");

        assert!(output.ok, "{output:?}");
        assert_eq!(
            output
                .timings
                .as_ref()
                .map(|timing| timing.used_embedded_std),
            Some(true)
        );
        assert_eq!(output.text, "run roots [[1, 2, 3]]\n");
    }

    #[test]
    fn run_inner_routes_junction_prelude_names_to_embedded_std() {
        clear_std_cache();
        let output =
            run_inner_on_test_stack("if all [1, 2, 3] < any [2, 3, 4]:\n  1\nelse:\n  0\n");

        assert!(output.ok, "{output:?}");
        assert_eq!(
            output
                .timings
                .as_ref()
                .map(|timing| timing.used_embedded_std),
            Some(true)
        );
        assert_eq!(output.text, "run roots [1]\n");
    }

    #[test]
    fn run_inner_results_show_only_last_root_value() {
        clear_std_cache();
        let output = run_inner("1\n2\n3\n");

        assert!(output.ok, "{output:?}");
        assert_eq!(output.results.len(), 1, "{output:?}");
        assert_eq!(
            output.results.first().map(|result| result.value.as_str()),
            Some("3")
        );
        assert_eq!(output.text, "run roots [1, 2, 3]\n");
    }

    #[test]
    fn run_inner_handles_console_out_as_stdout() {
        clear_std_cache();
        let output = run_inner("println \"hello\"\n1 + 2\n");

        assert!(output.ok, "{output:?}");
        assert_eq!(output.stdout, "Output 1: hello\n");
        assert_eq!(output.results.len(), 1, "{output:?}");
        assert_eq!(
            output.results.first().map(|result| result.value.as_str()),
            Some("3")
        );
        assert_eq!(output.text, "run roots [(), 3]\n");
    }

    #[test]
    fn run_inner_print_nth_drives_top_level_nondet_for_stdout() {
        clear_std_cache();
        let output = run_inner("if nondet::branch() { say \"yes\" } else { say \"no\" }\n");

        assert!(output.ok, "{output:?}");
        assert_eq!(output.stdout, "Output 1: yes\nOutput 2: no\n");
        assert!(output.results.is_empty(), "{output:?}");
        assert_eq!(output.text, "run roots []\n");
    }

    #[test]
    fn run_inner_results_empty_when_last_root_print_nth_suppressed() {
        clear_std_cache();
        let output = run_inner("1\nif nondet::branch() { say \"yes\" } else { say \"no\" }\n");

        assert!(output.ok, "{output:?}");
        assert_eq!(output.stdout, "Output 1: yes\nOutput 2: no\n");
        assert!(output.results.is_empty(), "{output:?}");
        assert_eq!(output.text, "run roots [1]\n");
    }

    #[test]
    fn run_inner_results_keep_last_normal_after_print_nth_suppressed_root() {
        clear_std_cache();
        let output = run_inner("if nondet::branch() { say \"yes\" } else { say \"no\" }\n2\n");

        assert!(output.ok, "{output:?}");
        assert_eq!(output.stdout, "Output 1: yes\nOutput 2: no\n");
        assert_eq!(output.results.len(), 1, "{output:?}");
        assert_eq!(
            output.results.first().map(|result| result.value.as_str()),
            Some("2")
        );
        assert_eq!(output.text, "run roots [2]\n");
    }

    #[test]
    fn run_inner_print_nth_drives_each_for_stdout() {
        clear_std_cache();
        let output = run_inner(
            "\
use std::control::nondet::*
{
  my x = each [1, 2, 3]
  say x
}
",
        );

        assert!(output.ok, "{output:?}");
        assert_eq!(
            output.stdout,
            "Output 1: 1\nOutput 2: 2\nOutput 3: 3\n"
        );
        assert!(output.results.is_empty(), "{output:?}");
        assert_eq!(output.text, "run roots []\n");
    }

    #[test]
    fn run_inner_keeps_sub_return_through_for_callback_before_println() {
        clear_std_cache();
        let source = "\
our g h = sub:
    for i in 0..3:
        h i
    return 1

sub:
    my b = g \\i -> if i == 0: return i
    println b.show
    2
";
        let source = source.to_string();
        let (output, full_std_stdout, full_std_text) = on_test_stack(move || {
            let output = run_inner(&source);
            let full_std_output = run_evidence_from_source_text_with_embedded_std(&source).unwrap();
            (output, full_std_output.stdout, full_std_output.text)
        });

        assert_eq!(full_std_stdout, "");
        assert_eq!(full_std_text, "run roots [0]\n");

        assert!(output.ok, "{output:?}");
        assert_eq!(output.stdout, full_std_stdout);
        assert_eq!(
            output.results.first().map(|result| result.value.as_str()),
            Some("0")
        );
        assert_eq!(output.text, full_std_text);
    }

    #[test]
    fn run_inner_runs_nondet_once_triple() {
        clear_std_cache();
        let source = "\
{
    my a = each 1..
    my b = each a<..
    my c = each b<..

    guard: a * a + b * b == c * c

    (a, b, c)
} .once
";
        let source = source.to_string();
        let (output, full_std_text) = on_test_stack(move || {
            let output = run_inner(&source);
            let full_std_output = run_evidence_from_source_text_with_embedded_std(&source).unwrap();
            (output, full_std_output.text)
        });

        assert_eq!(full_std_text, "run roots [just (3, 4, 5)]\n");
        assert!(output.ok, "{output:?}");
        assert_eq!(
            output.results.first().map(|result| result.value.as_str()),
            Some("just (3, 4, 5)")
        );
        assert_eq!(output.text, full_std_text);
    }

    #[test]
    fn display_path_context_uses_shortest_unique_suffixes() {
        let paths = vec![
            vec![
                "std".into(),
                "data".into(),
                "opt".into(),
                "opt".into(),
                "just".into(),
            ],
            vec![
                "std".into(),
                "data".into(),
                "result".into(),
                "result".into(),
                "just".into(),
            ],
        ];
        let index = ShortPathIndex::new(paths.iter());

        assert_eq!(
            index.rewrite(&paths[0]),
            vec!["opt".to_string(), "just".to_string()]
        );
        assert_eq!(
            index.rewrite(&paths[1]),
            vec!["result".to_string(), "just".to_string()]
        );
    }

    #[test]
    fn colorize_inner_reports_token_spans() {
        let output = colorize_inner("// note\nmy x = \"日本語\"\n");

        assert!(output.ok, "{output:?}");
        assert!(output.spans.iter().any(|span| {
            span.kind == HighlightKind::Comment && span.start == 0 && span.end == 7
        }));
        assert!(output.spans.iter().any(|span| {
            span.kind == HighlightKind::Keyword && span.start == 8 && span.end == 10
        }));
        assert!(
            output
                .spans
                .iter()
                .any(|span| { span.kind == HighlightKind::String && span.start >= 15 })
        );
    }

    #[test]
    fn colorize_inner_uses_playground_prelude_ops() {
        let source = "my y = x<..\n";
        let output = colorize_inner(source);

        assert!(output.ok, "{output:?}");
        assert!(output.spans.iter().any(|span| {
            span.kind == HighlightKind::Keyword && &source[span.start..span.end] == "my"
        }));
        assert!(output.spans.iter().any(|span| {
            span.kind == HighlightKind::Operator && &source[span.start..span.end] == "<.."
        }));
        assert!(
            !output
                .spans
                .iter()
                .any(|span| &source[span.start..span.end] == "<")
        );
    }

    #[test]
    fn colorize_inner_uses_editor_semantic_token_kinds() {
        let source = "\
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

my make() = { name: \"origin\" }
point { x: 3, y: 4 } .norm2
";
        let output = colorize_inner(source);

        assert!(output.ok, "{output:?}");
        assert!(output.spans.iter().any(|span| {
            span.kind == HighlightKind::Type && &source[span.start..span.end] == "point"
        }));
        assert!(output.spans.iter().any(|span| {
            span.kind == HighlightKind::Function && &source[span.start..span.end] == "norm2"
        }));
        assert!(!output.spans.iter().any(|span| {
            span.kind == HighlightKind::Property && &source[span.start..span.end] == "norm2"
        }));
        assert!(output.spans.iter().any(|span| {
            span.kind == HighlightKind::Function && &source[span.start..span.end] == "make"
        }));
        assert!(output.spans.iter().any(|span| {
            span.kind == HighlightKind::Property && &source[span.start..span.end] == "name"
        }));
    }

    #[test]
    fn run_inner_caches_repeated_source() {
        clear_std_cache();
        let first = run_inner("my id x = x\nid(42)\n");
        let second = run_inner("my id x = x\nid(42)\n");

        assert!(first.ok, "{first:?}");
        assert!(second.ok, "{second:?}");
        assert_eq!(
            second
                .timings
                .as_ref()
                .map(|timing| timing.source_cache_hits),
            Some(1)
        );
    }

    #[test]
    fn run_inner_reuses_warmed_std_prefix_without_cross_source_leaks() {
        clear_std_cache();
        let warmup = warm_std_cache_inner();
        assert!(warmup.embedded_std_artifacts_valid, "{warmup:?}");

        let cases = [
            ("1 + 2\n", "run roots [3]\n"),
            (playground_showcase_source("Config"), "run roots [(), ()]\n"),
            (PARSER_PATTERN_SHOWCASE, "run roots [(), (), (), ()]\n"),
            ("each(1..3).list\n", "run roots [[1, 2, 3]]\n"),
            (
                "if all [1, 2, 3] < any [2, 3, 4]:\n  1\nelse:\n  0\n",
                "run roots [1]\n",
            ),
        ];

        for (source, expected_text) in cases {
            let output = run_inner_on_test_stack(source);
            assert!(output.ok, "{output:?}");
            assert_eq!(output.text, expected_text);
            assert_eq!(
                output
                    .timings
                    .as_ref()
                    .map(|timing| (timing.source_cache_hits, timing.source_cache_misses)),
                Some((0, 1)),
                "{output:?}"
            );
        }
    }

    #[test]
    fn no_std_vm_boundary_on_ref_list_surface_retries_with_playground_std() {
        let source = "\
{
    my $xs = [1]
    &xs[0] = 2
    $xs
}
";
        let errors = vec![
            "unsupported VM boundary: function adapter {get: unit -> thunk[[&xs], int]}"
                .to_string(),
        ];

        assert!(super::should_retry_with_embedded_std(source, &errors));
    }

    #[test]
    fn run_inner_reports_exported_types() {
        clear_std_cache();
        let output = run_inner(
            "\
our id x = x
my hidden x = x
pub answer = id 42
pub name = id \"Yulang\"
pub pair = (answer, name)

pair
",
        );

        assert!(output.ok, "{output:?}");
        let names = output
            .types
            .iter()
            .map(|item| item.name.as_str())
            .collect::<Vec<_>>();
        assert!(names.contains(&"id"), "{:?}", output.types);
        assert!(names.contains(&"answer"), "{:?}", output.types);
        assert!(names.contains(&"name"), "{:?}", output.types);
        assert!(names.contains(&"pair"), "{:?}", output.types);
        assert!(!names.contains(&"hidden"), "{:?}", output.types);
        assert!(
            output
                .types
                .iter()
                .any(|item| item.name == "id" && item.ty.contains("->"))
        );
        assert!(
            output
                .types
                .iter()
                .any(|item| item.name == "answer" && item.ty.contains("int"))
        );
    }

    #[test]
    fn run_inner_reports_exported_types_for_playground_std_source() {
        clear_std_cache();
        let output = run_inner("pub xs = [1, 2, 3]\nxs\n");

        assert!(output.ok, "{output:?}");
        let xs = output.types.iter().find(|item| item.name == "xs");
        assert_eq!(xs.map(|item| item.ty.as_str()), Some("list int"));
    }

    #[test]
    fn run_inner_exported_types_do_not_leak_private_markers() {
        clear_std_cache();
        let output = run_inner(
            "\
pub apply f x = f x
pub twice f x = f (f x)

pub compose1(f, g: _ -> [_] _, x) = f g(x)
pub compose2(f, g, x) = f g(x)

1
",
        );

        assert!(output.ok, "{output:?}");
        assert!(
            output.types.iter().any(|item| item.name == "twice"),
            "{:?}",
            output.types
        );
        let exported_type = |name: &str| {
            output
                .types
                .iter()
                .find(|item| item.name == name)
                .map(|item| item.ty.as_str())
        };
        assert_eq!(
            exported_type("twice"),
            Some("(('a | 'b) ['c@∅] -> ['c@∅ & 'd@∅] 'b & 'e) -> 'a -> ['d] 'e@")
        );
        assert_eq!(
            exported_type("compose2"),
            Some("('a ['b@∅] -> ['c] 'd) -> ('e -> ['b@∅] 'a) -> 'e -> ['c@] 'd@")
        );
        for item in &output.types {
            assert_public_type_display_has_no_private_markers(
                &item.ty,
                &format!("wasm exported type {}", item.name),
            );
        }
    }

    #[test]
    fn run_inner_returns_structured_lowering_diagnostic() {
        clear_std_cache();
        let output = run_inner(diagnostics_fixture("type_annotation_mismatch"));

        assert!(!output.ok, "{output:?}");
        assert!(output.results.is_empty(), "{output:?}");
        assert!(output.stdout.is_empty(), "{output:?}");
        assert_eq!(output.diagnostics.len(), 1);
        assert_type_annotation_mismatch_diagnostic(&output.diagnostics[0]);
        assert_eq!(output.errors, vec!["type mismatch: bool is not int"]);
    }

    #[test]
    fn run_inner_lowering_diagnostics_match_check_inner() {
        clear_std_cache();
        let source = "\n// keep playground diagnostics on the user source line\nmy x: int = true\n";
        let run_output = run_inner(source);
        let check_output = check_inner(source);

        assert!(!run_output.ok, "{run_output:?}");
        assert!(!check_output.ok, "{check_output:?}");
        assert_eq!(run_output.diagnostics, check_output.diagnostics);
    }

    #[test]
    fn run_inner_runtime_error_stays_message_diagnostic() {
        clear_std_cache();
        let source = diagnostics_fixture("not_callable_error");
        let output = run_inner(source);

        assert!(!output.ok, "{output:?}");
        assert_eq!(output.diagnostics.len(), 1);
        let diagnostic = &output.diagnostics[0];
        assert_eq!(diagnostic.code, None);
        assert_eq!(diagnostic.label, None);
        assert_eq!(diagnostic.hint, None);
        assert_eq!(diagnostic.start, 0);
        assert_eq!(diagnostic.end, source.len());
        assert!(diagnostic.related.is_empty(), "{diagnostic:?}");
        assert!(
            diagnostic
                .message
                .contains("runtime-evidence-run not a function: 1"),
            "{diagnostic:?}"
        );
        assert_eq!(output.errors, vec![diagnostic.message.clone()]);
    }

    #[test]
    fn check_inner_returns_structured_diagnostic() {
        let output = check_inner(diagnostics_fixture("type_annotation_mismatch"));

        assert!(!output.ok, "{output:?}");
        assert_eq!(output.diagnostics.len(), 1);
        assert_eq!(output.diagnostics[0].label.as_deref(), Some("x"));
        assert_eq!(
            output.diagnostics[0].code.as_deref(),
            Some("yulang.type-mismatch")
        );
        assert_eq!(output.diagnostics[0].start, 3);
        assert_eq!(output.diagnostics[0].end, 4);
        assert_eq!(
            output.diagnostics[0].message,
            "type mismatch: bool is not int"
        );
        assert_eq!(output.diagnostics[0].hint, None);
        assert_eq!(output.diagnostics[0].related.len(), 2);
        assert_eq!(
            output.diagnostics[0].related[0].message,
            "expected type comes from this type annotation: int"
        );
        assert_eq!(
            output.diagnostics[0].related[0].origin.as_deref(),
            Some("type_annotation")
        );
        assert_eq!(output.diagnostics[0].related[0].start, 6);
        assert_eq!(output.diagnostics[0].related[0].end, 9);
        assert_eq!(
            output.diagnostics[0].related[1].message,
            "actual type comes from this expression: bool"
        );
        assert_eq!(
            output.diagnostics[0].related[1].origin.as_deref(),
            Some("expression")
        );
        assert_eq!(output.diagnostics[0].related[1].start, 12);
        assert_eq!(output.diagnostics[0].related[1].end, 16);
    }

    #[test]
    fn check_inner_keeps_diagnostic_offsets_after_leading_trivia() {
        let source = "\n// keep playground diagnostics on the user source line\nmy x: int = true\n";
        let output = check_inner(source);

        assert!(!output.ok, "{output:?}");
        assert_eq!(output.diagnostics.len(), 1);
        let diagnostic = &output.diagnostics[0];
        assert_eq!(diagnostic.label.as_deref(), Some("x"));
        assert_eq!(diagnostic.code.as_deref(), Some("yulang.type-mismatch"));
        let label_start = source.find("x:").unwrap();
        assert_eq!(diagnostic.start, label_start);
        assert_eq!(diagnostic.end, label_start + "x".len());
        assert_eq!(diagnostic.message, "type mismatch: bool is not int");
        assert_eq!(diagnostic.related.len(), 2);
        let annotation_start = source.find("int").unwrap();
        assert_eq!(
            diagnostic.related[0].message,
            "expected type comes from this type annotation: int"
        );
        assert_eq!(
            diagnostic.related[0].origin.as_deref(),
            Some("type_annotation")
        );
        assert_eq!(diagnostic.related[0].start, annotation_start);
        assert_eq!(diagnostic.related[0].end, annotation_start + "int".len());
        let expression_start = source.find("true").unwrap();
        assert_eq!(
            diagnostic.related[1].message,
            "actual type comes from this expression: bool"
        );
        assert_eq!(diagnostic.related[1].origin.as_deref(), Some("expression"));
        assert_eq!(diagnostic.related[1].start, expression_start);
        assert_eq!(diagnostic.related[1].end, expression_start + "true".len());
    }

    #[test]
    fn check_inner_keeps_incomplete_source_diagnostics() {
        let source = "my x =\n";
        let output = check_inner(source);

        assert!(!output.ok, "{output:?}");
        assert_eq!(output.diagnostics.len(), 2);
        assert_eq!(output.diagnostics[0].label, None);
        assert_eq!(output.diagnostics[0].code.as_deref(), Some("yulang.syntax"));
        let eof_offset = source.find('\n').unwrap();
        assert_eq!(output.diagnostics[0].start, eof_offset);
        assert_eq!(output.diagnostics[0].end, eof_offset);
        assert_eq!(
            output.diagnostics[0].message,
            "syntax error: unexpected end of input"
        );
        assert_eq!(output.diagnostics[1].label.as_deref(), Some("x"));
        assert_eq!(
            output.diagnostics[1].code.as_deref(),
            Some("yulang.missing-local-binding-body")
        );
        let name_start = source.find('x').unwrap();
        assert_eq!(output.diagnostics[1].start, name_start);
        assert_eq!(output.diagnostics[1].end, name_start + "x".len());
        assert_eq!(
            output.diagnostics[1].message,
            "binding `x` is missing a body expression"
        );
        assert_eq!(
            output.diagnostics[1].hint.as_deref(),
            Some("write a body expression after `=`")
        );
    }

    #[test]
    fn check_inner_returns_diagnostic_code_and_type_name_range() {
        let output = check_inner(diagnostics_fixture("unresolved_type_name"));

        assert!(!output.ok, "{output:?}");
        assert_eq!(output.diagnostics.len(), 1);
        assert_eq!(output.diagnostics[0].severity, DiagnosticSeverity::Error);
        assert_eq!(output.diagnostics[0].label.as_deref(), Some("x"));
        assert_eq!(
            output.diagnostics[0].code.as_deref(),
            Some("yulang.unresolved-type")
        );
        assert_eq!(output.diagnostics[0].start, 6);
        assert_eq!(output.diagnostics[0].end, 18);
        assert_eq!(
            output.diagnostics[0].message,
            "unresolved type name: missing_type"
        );
        assert_eq!(
            output.diagnostics[0].hint.as_deref(),
            Some("define type `missing_type` before this annotation, or import it")
        );
    }

    #[test]
    fn check_inner_returns_diagnostic_code_and_value_name_range() {
        let output = check_inner(diagnostics_fixture("unresolved_value_name"));

        assert!(!output.ok, "{output:?}");
        assert_eq!(output.diagnostics.len(), 1);
        assert_eq!(output.diagnostics[0].severity, DiagnosticSeverity::Error);
        assert_eq!(output.diagnostics[0].label.as_deref(), Some("result"));
        assert_eq!(
            output.diagnostics[0].code.as_deref(),
            Some("yulang.unresolved-value")
        );
        assert_eq!(output.diagnostics[0].start, 12);
        assert_eq!(output.diagnostics[0].end, 19);
        assert_eq!(
            output.diagnostics[0].message,
            "unresolved value name: missing"
        );
        assert_eq!(
            output.diagnostics[0].hint.as_deref(),
            Some("define `missing` before this use, or import the module that provides it")
        );
    }

    #[test]
    fn check_inner_returns_top_level_mutable_binding_code_and_range() {
        let output = check_inner(diagnostics_fixture("top_level_mutable_binding"));

        assert!(!output.ok, "{output:?}");
        assert_eq!(output.diagnostics.len(), 1);
        assert_eq!(output.diagnostics[0].severity, DiagnosticSeverity::Error);
        assert_eq!(output.diagnostics[0].label.as_deref(), Some("$x"));
        assert_eq!(
            output.diagnostics[0].code.as_deref(),
            Some("yulang.top-level-mutable-binding")
        );
        assert_eq!(output.diagnostics[0].start, 3);
        assert_eq!(output.diagnostics[0].end, 5);
        assert_eq!(
            output.diagnostics[0].message,
            "top-level mutable binding $x is not supported; move it into a block or function body"
        );
        assert_eq!(
            output.diagnostics[0].hint.as_deref(),
            Some("move the mutable binding into a block or function body")
        );
    }

    #[test]
    fn check_inner_returns_unsupported_type_syntax_code_and_range() {
        let output = check_inner(diagnostics_fixture("unsupported_record_type_annotation"));

        assert!(!output.ok, "{output:?}");
        assert_eq!(output.diagnostics.len(), 1);
        assert_eq!(output.diagnostics[0].label.as_deref(), Some("x"));
        assert_eq!(
            output.diagnostics[0].code.as_deref(),
            Some("yulang.unsupported-type-syntax")
        );
        assert_eq!(output.diagnostics[0].start, 6);
        assert_eq!(output.diagnostics[0].end, 25);
        assert_eq!(
            output.diagnostics[0].message,
            "unsupported type annotation syntax: TypeRecord"
        );
    }

    #[test]
    fn check_inner_returns_unclosed_paren_syntax_code_and_range() {
        let output = check_inner(diagnostics_fixture("unclosed_paren"));

        assert!(!output.ok, "{output:?}");
        assert_eq!(output.diagnostics.len(), 1);
        assert_eq!(output.diagnostics[0].label, None);
        assert_eq!(output.diagnostics[0].code.as_deref(), Some("yulang.syntax"));
        assert_eq!(output.diagnostics[0].start, 9);
        assert_eq!(output.diagnostics[0].end, 9);
        assert_eq!(
            output.diagnostics[0].message,
            "syntax error: unexpected end of input"
        );
    }

    #[test]
    fn check_inner_returns_trailing_operator_syntax_code_and_range() {
        let output = check_inner(diagnostics_fixture("trailing_operator"));

        assert!(!output.ok, "{output:?}");
        assert_eq!(output.diagnostics.len(), 1);
        assert_eq!(output.diagnostics[0].label, None);
        assert_eq!(output.diagnostics[0].code.as_deref(), Some("yulang.syntax"));
        assert_eq!(output.diagnostics[0].start, 9);
        assert_eq!(output.diagnostics[0].end, 10);
        assert_eq!(
            output.diagnostics[0].message,
            "syntax error: unexpected token"
        );
    }

    #[test]
    fn check_inner_returns_missing_index_argument_code_and_range() {
        let output = check_inner(diagnostics_fixture("missing_index_argument"));

        assert!(!output.ok, "{output:?}");
        assert_eq!(output.diagnostics.len(), 1);
        assert_eq!(output.diagnostics[0].label, None);
        assert_eq!(
            output.diagnostics[0].code.as_deref(),
            Some("yulang.missing-index-argument")
        );
        assert_eq!(output.diagnostics[0].start, 3);
        assert_eq!(output.diagnostics[0].end, 5);
        assert_eq!(
            output.diagnostics[0].message,
            "index expression is missing an argument"
        );
        assert_eq!(
            output.diagnostics[0].hint.as_deref(),
            Some("write an index expression inside the brackets")
        );
    }

    #[test]
    fn check_inner_returns_case_syntax_codes_and_ranges() {
        let cases = [
            (
                "case_missing_scrutinee",
                "yulang.missing-case-scrutinee",
                0,
                4,
                "case expression is missing the value to inspect",
                Some("write `case <expr>:` before the arms"),
            ),
            (
                "case_missing_arm_pattern",
                "yulang.missing-case-arm-pattern",
                10,
                12,
                "case arm is missing a pattern",
                Some("write a pattern before `->`"),
            ),
            (
                "case_missing_arm_body",
                "yulang.missing-case-arm-body",
                12,
                14,
                "case arm is missing a body expression",
                Some("write an expression after `->`"),
            ),
        ];

        for (fixture, code, start, end, message, hint) in cases {
            let output = check_inner(diagnostics_fixture(fixture));

            assert!(!output.ok, "{fixture}: {output:?}");
            assert_eq!(output.diagnostics.len(), 1, "{fixture}");
            let diagnostic = &output.diagnostics[0];
            assert_eq!(diagnostic.severity, DiagnosticSeverity::Error, "{fixture}");
            assert_eq!(diagnostic.label, None, "{fixture}");
            assert_eq!(diagnostic.code.as_deref(), Some(code), "{fixture}");
            assert_eq!(diagnostic.start, start, "{fixture}");
            assert_eq!(diagnostic.end, end, "{fixture}");
            assert_eq!(diagnostic.message, message, "{fixture}");
            assert_eq!(diagnostic.hint.as_deref(), hint, "{fixture}");
            assert!(diagnostic.related.is_empty(), "{fixture}");
        }
    }

    #[test]
    fn check_inner_returns_rule_lazy_quantifier_code_and_range() {
        let output = check_inner(diagnostics_fixture("rule_lazy_quantifier"));

        assert!(!output.ok, "{output:?}");
        assert_eq!(output.diagnostics.len(), 1);
        assert_eq!(output.diagnostics[0].label.as_deref(), Some("p"));
        assert_eq!(
            output.diagnostics[0].code.as_deref(),
            Some("yulang.unsupported-rule-lazy-quantifier")
        );
        assert_eq!(output.diagnostics[0].start, 18);
        assert_eq!(output.diagnostics[0].end, 20);
        assert_eq!(
            output.diagnostics[0].message,
            "rule lazy quantifier `*?` is not supported; rule uses PEG-style greedy repetition"
        );
    }

    #[test]
    fn check_inner_returns_catch_syntax_codes_and_ranges() {
        let cases = [
            (
                "catch_missing_scrutinee",
                "yulang.missing-catch-scrutinee",
                0,
                5,
                "catch expression is missing the computation to handle",
                Some("write `catch <expr>:` before the handler arms"),
            ),
            (
                "catch_raw_brace_scrutinee",
                "yulang.missing-catch-scrutinee",
                0,
                5,
                "catch expression is missing the computation to handle",
                Some("write `catch <expr>:` before the handler arms"),
            ),
            (
                "catch_missing_arm_pattern",
                "yulang.missing-catch-arm-pattern",
                13,
                15,
                "catch arm is missing a value pattern or effect operation",
                Some("write a value pattern or effect operation before `->`"),
            ),
            (
                "catch_missing_arm_body",
                "yulang.missing-catch-arm-body",
                19,
                21,
                "catch arm is missing a body expression",
                Some("write an expression after `->`"),
            ),
        ];

        for (fixture, code, start, end, message, hint) in cases {
            let output = check_inner(diagnostics_fixture(fixture));

            assert!(!output.ok, "{fixture}: {output:?}");
            assert_eq!(output.diagnostics.len(), 1, "{fixture}");
            let diagnostic = &output.diagnostics[0];
            assert_eq!(diagnostic.severity, DiagnosticSeverity::Error, "{fixture}");
            assert_eq!(diagnostic.label, None, "{fixture}");
            assert_eq!(diagnostic.code.as_deref(), Some(code), "{fixture}");
            assert_eq!(diagnostic.start, start, "{fixture}");
            assert_eq!(diagnostic.end, end, "{fixture}");
            assert_eq!(diagnostic.message, message, "{fixture}");
            assert_eq!(diagnostic.hint.as_deref(), hint, "{fixture}");
            assert!(diagnostic.related.is_empty(), "{fixture}");
        }
    }

    #[test]
    fn check_inner_returns_role_method_diagnostic_payloads() {
        let output = check_inner(diagnostics_fixture("unresolved_method_error"));

        assert!(!output.ok, "{output:?}");
        assert_eq!(output.diagnostics.len(), 1);
        let diagnostic = &output.diagnostics[0];
        assert_eq!(diagnostic.severity, DiagnosticSeverity::Error);
        assert_eq!(diagnostic.label.as_deref(), Some("show"));
        assert_eq!(diagnostic.code.as_deref(), Some("yulang.unresolved-method"));
        assert_eq!(diagnostic.start, 10);
        assert_eq!(diagnostic.end, 14);
        assert!(
            diagnostic
                .message
                .contains("no role implementation satisfies this method call"),
            "{diagnostic:?}"
        );
        assert!(
            diagnostic
                .hint
                .as_deref()
                .unwrap_or_default()
                .contains("add or import an impl"),
            "{diagnostic:?}"
        );
        assert!(diagnostic.related.is_empty(), "{diagnostic:?}");

        let output = check_inner(diagnostics_fixture("ambiguous_method_error"));

        assert!(!output.ok, "{output:?}");
        assert_eq!(output.diagnostics.len(), 1);
        let diagnostic = &output.diagnostics[0];
        assert_eq!(diagnostic.severity, DiagnosticSeverity::Error);
        assert_eq!(diagnostic.label.as_deref(), Some("foo"));
        assert_eq!(diagnostic.code.as_deref(), Some("yulang.ambiguous-method"));
        assert_eq!(diagnostic.start, 97);
        assert_eq!(diagnostic.end, 100);
        assert!(
            diagnostic
                .message
                .contains("more than one role implementation satisfies this method call"),
            "{diagnostic:?}"
        );
        assert!(
            diagnostic
                .hint
                .as_deref()
                .unwrap_or_default()
                .contains("make the receiver type more specific"),
            "{diagnostic:?}"
        );
        assert_eq!(diagnostic.related.len(), 2, "{diagnostic:?}");
        assert!(
            diagnostic
                .related
                .iter()
                .all(|item| item.message.contains("matching impl method candidate")),
            "{diagnostic:?}"
        );
        assert!(
            diagnostic
                .related
                .iter()
                .all(|item| item.origin.as_deref() == Some("impl_candidate")),
            "{diagnostic:?}"
        );
    }

    #[test]
    fn dump_poly_inner_reports_lowering_errors() {
        let output = dump_poly_inner("my x: int = true\n");

        assert!(!output.ok, "{output:?}");
        assert!(output.text.contains("my d"));
        assert_eq!(output.errors, vec!["type mismatch: bool is not int"]);
    }
}
