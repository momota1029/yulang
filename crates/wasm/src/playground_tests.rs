use super::*;

mod tests {
    use super::*;

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
        let output = run_inner("if all [1, 2, 3] < any [2, 3, 4]:\n  1\nelse:\n  0\n");

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
        let output = run_inner(source);
        let full_std_output = run_control_from_source_text_with_embedded_std(source).unwrap();

        assert_eq!(full_std_output.stdout, "");
        assert_eq!(full_std_output.text, "run roots [0]\n");

        assert!(output.ok, "{output:?}");
        assert_eq!(output.stdout, full_std_output.stdout);
        assert_eq!(
            output.results.first().map(|result| result.value.as_str()),
            Some("0")
        );
        assert_eq!(output.text, full_std_output.text);
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
        let output = run_inner(source);
        let full_std_output = run_control_from_source_text_with_embedded_std(source).unwrap();

        assert_eq!(full_std_output.text, "run roots [just (3, 4, 5)]\n");
        assert!(output.ok, "{output:?}");
        assert_eq!(
            output.results.first().map(|result| result.value.as_str()),
            Some("just (3, 4, 5)")
        );
        assert_eq!(output.text, full_std_output.text);
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
        assert!(
            output
                .types
                .iter()
                .any(|item| item.name == "xs" && item.ty.contains("list"))
        );
    }

    #[test]
    fn check_inner_returns_structured_diagnostic() {
        let output = check_inner("my x: int = true\n");

        assert!(!output.ok, "{output:?}");
        assert_eq!(output.diagnostics.len(), 1);
        assert_eq!(output.diagnostics[0].label.as_deref(), Some("x"));
        assert_eq!(
            output.diagnostics[0].message,
            "type mismatch: bool is not int"
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
