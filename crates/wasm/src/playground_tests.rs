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

    fn diagnostics_fixture(name: &str) -> &'static str {
        match name {
            "type_annotation_mismatch" => include_str!(
                "../../../tests/yulang/regressions/diagnostics/type_annotation_mismatch.yu"
            ),
            "unresolved_type_name" => include_str!(
                "../../../tests/yulang/regressions/diagnostics/unresolved_type_name.yu"
            ),
            "unsupported_record_type_annotation" => include_str!(
                "../../../tests/yulang/regressions/diagnostics/unsupported_record_type_annotation.yu"
            ),
            "unclosed_paren" => {
                include_str!("../../../tests/yulang/regressions/diagnostics/unclosed_paren.yu")
            }
            "rule_lazy_quantifier" => include_str!(
                "../../../tests/yulang/regressions/diagnostics/rule_lazy_quantifier.yu"
            ),
            _ => panic!("unknown diagnostics fixture: {name}"),
        }
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
        assert!(output.file_count < yulang::stdlib::embedded_std_files().len() + 1);
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
    fn run_inner_handles_console_out_as_stdout() {
        clear_std_cache();
        let output = run_inner("println \"hello\"\n1 + 2\n");

        assert!(output.ok, "{output:?}");
        assert_eq!(output.stdout, "hello\n");
        assert_eq!(
            output.results.first().map(|result| result.value.as_str()),
            Some("()")
        );
        assert_eq!(
            output.results.get(1).map(|result| result.value.as_str()),
            Some("3")
        );
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
        assert_eq!(output.diagnostics[0].related.len(), 2);
        assert_eq!(
            output.diagnostics[0].related[0].message,
            "expected type: int"
        );
        assert_eq!(output.diagnostics[0].related[0].start, 6);
        assert_eq!(output.diagnostics[0].related[0].end, 9);
        assert_eq!(
            output.diagnostics[0].related[1].message,
            "actual expression type: bool"
        );
        assert_eq!(output.diagnostics[0].related[1].start, 12);
        assert_eq!(output.diagnostics[0].related[1].end, 16);
    }

    #[test]
    fn check_inner_returns_diagnostic_code_and_type_name_range() {
        let output = check_inner(diagnostics_fixture("unresolved_type_name"));

        assert!(!output.ok, "{output:?}");
        assert_eq!(output.diagnostics.len(), 1);
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
    fn dump_poly_inner_reports_lowering_errors() {
        let output = dump_poly_inner("my x: int = true\n");

        assert!(!output.ok, "{output:?}");
        assert!(output.text.contains("my d"));
        assert_eq!(output.errors, vec!["type mismatch: bool is not int"]);
    }
}
