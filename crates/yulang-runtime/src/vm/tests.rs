#[cfg(test)]
mod tests {
    use super::super::*;
    use crate::ir::{Binding, Module, Type as RuntimeType};
    use crate::{
        RuntimeResult, lower_core_program, monomorphize_module, monomorphize_module_profiled,
    };
    use std::path::PathBuf;
    use std::thread;
    use yulang_infer::{SourceOptions, export_core_program, lower_virtual_source_with_options};

    #[derive(Debug, Clone, PartialEq, Eq)]
    enum TestValue {
        Int(String),
        Float(String),
        String(String),
        Bool(bool),
        Unit,
        List(Vec<TestValue>),
        Tuple(Vec<TestValue>),
        Record(BTreeMap<String, TestValue>),
        Variant {
            tag: String,
            value: Option<Box<TestValue>>,
        },
    }

    const JUNCTION_SOURCE: &str = r#"if all [1, 2, 3] < any [2,3,4]:
    1
else:
    2
"#;

    const STRUCT_METHOD_SOURCE: &str = r#"struct point { x: int, y: int } with:
    our p.width = p.x

(point { x: 1, y: 2 }).width
"#;

    const ROLE_EFFECT_HANDLER_SOURCE: &str = r#"act undet:
  our bool: () -> bool

role Ask 'a:
  our a.ask: () -> [undet] bool

impl Ask int:
  our x.ask() = undet::bool()

catch 1.ask():
  undet::bool(), k -> k true
"#;

    const ROLE_EFFECT_HELPER_SOURCE: &str = r#"act undet:
  our bool: () -> bool

role Ask 'a:
  our a.ask: () -> [undet] bool

impl Ask int:
  our x.ask() = undet::bool()

my ask x = x.ask()

catch ask 1:
  undet::bool(), k -> k true
"#;

    const FOR_LOOP_LAST_SOURCE: &str = r#"for x in [1, 2, 3]:
    if x == 2:
        last
    else:
        ()
"#;

    const FOR_LOOP_LAST_RANGE_SOURCE: &str = r#"for x in 0..:
    if x == 5:
        last
    else:
        ()
"#;

    const FOR_LOOP_LAST_MIXED_SOURCE: &str = r#"for x in [1, 2, 3]:
    if x == 2:
        last
    else:
        ()

for x in 0..:
    if x == 5:
        last
    else:
        ()
"#;

    const UNDET_EACH_LOGIC_SOURCE: &str = r#"use std::undet::*

(each [1, 2, 3] + each [4, 5, 6]).logic

(each [1, 2, 3] + each [4, 5, 6]).once
"#;

    const RANGE_INFINITE_UNDET_SOURCE: &str = r#"use std::undet::*

({
    my x = each (0..)
    guard (x == 3)
    x
}).once
"#;

    const SHOWCASE_SOURCE: &str = r#"use std::undet::*

struct point { x: int, y: int } with:
    our p.norm2: int = p.x * p.x + p.y * p.y

my inflate({base = 1, extra = base + 1}) = base + extra

inflate { base: 3 }

{
    my $xs = [2, 3, 4]
    &xs[1] = 6
    $xs
}

sub:
    for x in 0..:
        if x == 5: return x
        else: ()
    0

({
    my y = if all [1, 2, 3] < any [2, 3, 4]:
        each [3, 4, 5]
    else:
        2

    point { x: 3, y: y } .norm2
}).once
"#;

    #[test]
    fn vm_runs_source_primitive_int_add_sugar_example() {
        let results = eval_source_with_std("my x = 1 + 2\nx\n");

        assert_eq!(results, vec![TestValue::Int("3".to_string())]);
    }

    #[test]
    fn vm_runs_source_primitive_int_add_example() {
        let results = eval_source_with_std("my x = add 1 2\nx\n");

        assert_eq!(results, vec![TestValue::Int("3".to_string())]);
    }

    #[test]
    fn vm_preserves_large_integer_literal_text() {
        let results = eval_source_with_std("99999999999999999999999\n");

        assert_eq!(
            results,
            vec![TestValue::Int("99999999999999999999999".to_string())]
        );
    }

    #[test]
    fn vm_runs_source_primitive_float_add_example() {
        let results = eval_source_with_std("my x = std::float::add 1.0 2.0\nx\n");

        assert_eq!(results, vec![TestValue::Float("3.0".to_string())]);
    }

    #[test]
    fn vm_runs_source_mixed_numeric_add_with_float_widening() {
        let results = eval_source_with_std("(1 + 2.5, 1.0 + 2, 1 + 2)\n");

        assert_eq!(
            results,
            vec![TestValue::Tuple(vec![
                TestValue::Float("3.5".to_string()),
                TestValue::Float("3.0".to_string()),
                TestValue::Int("3".to_string()),
            ])]
        );
    }

    #[test]
    fn vm_matches_struct_constructor_patterns_as_records() {
        let results = eval_source_with_std(
            r#"struct pair { a: int, b: int }

my get_a (pair { a: x, b: _ }) = x

(
    case (pair { a: 1, b: 2 }):
        pair { a: x, b: y } -> std::int::add x y
        _ -> 0,
    get_a (pair { a: 7, b: 9 })
)
"#,
        );

        assert_eq!(
            results,
            vec![TestValue::Tuple(vec![
                TestValue::Int("3".to_string()),
                TestValue::Int("7".to_string()),
            ])]
        );
    }

    #[test]
    fn vm_matches_string_literal_case_patterns() {
        let results = eval_source_with_std(
            r#"my f s =
    case s:
        "a" -> 1
        "b" -> 2
        _ -> 99

(f "a", f "b", f "x")
"#,
        );

        assert_eq!(
            results,
            vec![TestValue::Tuple(vec![
                TestValue::Int("1".to_string()),
                TestValue::Int("2".to_string()),
                TestValue::Int("99".to_string()),
            ])]
        );
    }

    #[test]
    fn vm_keeps_items_after_doc_comments_inside_literals_and_struct_fields() {
        let results = eval_source_with_std(
            r#"struct point {
    -- x coord
    x: int,
    y: int
}

my r = {
    -- x field
    x: 1,
    y: 2
}

my xs = [
    -- first
    1, 2, 3
]

((point { x: 3, y: 4 }).y, r.y, xs.len)
"#,
        );

        assert_eq!(
            results,
            vec![TestValue::Tuple(vec![
                TestValue::Int("4".to_string()),
                TestValue::Int("2".to_string()),
                TestValue::Int("3".to_string()),
            ])]
        );
    }

    #[test]
    fn vm_runs_for_loop_with_ref_write_body() {
        let results = eval_source_with_std(
            r#"{
    my $sum = 0
    for x in [1, 2, 3, 4, 5]:
        &sum = $sum + x
    $sum
}
"#,
        );

        assert_eq!(results, vec![TestValue::Int("15".to_string())]);
    }

    #[test]
    fn vm_runs_if_branch_with_outer_ref_write_in_block() {
        let results = eval_source_with_std(
            r#"my $i = 0
{
    if true:
        &i = 1
    $i
}
"#,
        );

        assert_eq!(results, vec![TestValue::Int("1".to_string())]);
    }

    #[test]
    fn vm_runs_for_loop_with_console_body() {
        let (results, stdout) = eval_source_with_std_host(
            r#"for i in [1, 2, 3]:
    println (i).show
"#,
        );

        assert_eq!(results, vec![TestValue::Unit]);
        assert_eq!(stdout, "1\n2\n3\n");
    }

    #[test]
    fn vm_runs_lambda_param_string_interpolation() {
        let (results, stdout) = eval_source_with_std_host(
            r#"my f = \x -> {
    println "x is %{x}"
    x + 1
}

f 5
"#,
        );

        assert_eq!(results, vec![TestValue::Int("6".to_string())]);
        assert_eq!(stdout, "x is 5\n");
    }

    #[test]
    fn vm_host_handles_console_output_requests() {
        let (results, stdout) = eval_source_with_std_host("println \"hello\"\n1 + 2\n");

        assert_eq!(
            results,
            vec![TestValue::Unit, TestValue::Int("3".to_string())]
        );
        assert_eq!(stdout, "hello\n");
    }

    #[test]
    fn vm_host_handles_fs_text_requests() {
        let path = temp_test_path("yulang-fs-text");
        let source_path = yulang_string_literal(&path.to_string_lossy());
        let source = format!(
            r#"my path = {source_path}
my before = exists path
my wrote = write_text (path, "hello")
my after = exists path
my file = is_file path
my dir = is_dir path
my text = case read_text path:
    std::opt::opt::nil -> "missing"
    std::opt::opt::just text -> text
(before, wrote, after, file, dir, text)
"#
        );
        let (results, stdout) = eval_source_with_std_host(&source);
        let _ = std::fs::remove_file(&path);

        assert!(stdout.is_empty());
        assert_eq!(
            results,
            vec![TestValue::Tuple(vec![
                TestValue::Bool(false),
                TestValue::Bool(true),
                TestValue::Bool(true),
                TestValue::Bool(true),
                TestValue::Bool(false),
                TestValue::String("hello".to_string()),
            ])]
        );
    }

    #[test]
    fn vm_distinguishes_same_path_error_constructor_and_operation() {
        let results = eval_source_with_std(
            r#"enum fs_err = not_found str | denied str | invalid_path str

act fs_err:
    our not_found: str -> never
    our denied: str -> never
    our invalid_path: str -> never

{
    my err: fs_err = fs_err::not_found "data.txt"
    my value = case err:
        fs_err::not_found path -> "value:" + path
        fs_err::denied path -> "denied:" + path
        fs_err::invalid_path text -> "invalid:" + text
    catch fs_err::not_found "data.txt":
        fs_err::not_found path, _ -> "missing:" + path
        fs_err::denied path, _ -> "denied:" + path
        fs_err::invalid_path text, _ -> "invalid:" + text
}
"#,
        );

        assert_eq!(
            results,
            vec![TestValue::String("missing:data.txt".to_string())]
        );
    }

    #[test]
    fn vm_runs_error_decl_constructor_and_operation() {
        let results = eval_source_with_std(
            r#"error fs_err:
    not_found str
    denied str
    invalid_path str

{
    my err: fs_err = fs_err::not_found "data.txt"
    my value = case err:
        fs_err::not_found path -> "value:" + path
        fs_err::denied path -> "denied:" + path
        fs_err::invalid_path text -> "invalid:" + text
    catch fs_err::not_found "data.txt":
        fs_err::not_found path, _ -> value + "|missing:" + path
        fs_err::denied path, _ -> "denied:" + path
        fs_err::invalid_path text, _ -> "invalid:" + text
}
"#,
        );

        assert_eq!(
            results,
            vec![TestValue::String(
                "value:data.txt|missing:data.txt".to_string()
            )]
        );
    }

    #[test]
    fn vm_handles_std_fs_err_throw_role() {
        let results = eval_source_with_std(
            r#"{
    my err: fs_err = fs_err::not_found "data.txt"
    catch err.throw:
        fs_err::not_found path, _ -> "missing:" + path
        fs_err::denied path, _ -> "denied:" + path
        fs_err::invalid_path text, _ -> "invalid:" + text
}
"#,
        );

        assert_eq!(
            results,
            vec![TestValue::String("missing:data.txt".to_string())]
        );
    }

    #[test]
    fn vm_handles_std_fs_err_fail_prefix() {
        let results = eval_source_with_std(
            r#"catch fail fs_err::invalid_path "bad/path":
    fs_err::not_found path, _ -> "missing:" + path
    fs_err::denied path, _ -> "denied:" + path
    fs_err::invalid_path text, _ -> "invalid:" + text
"#,
        );

        assert_eq!(
            results,
            vec![TestValue::String("invalid:bad/path".to_string())]
        );
    }

    #[test]
    fn vm_handles_std_read_text_or_throw_not_found() {
        let path = temp_test_path("yulang-missing-text");
        let source_path = yulang_string_literal(&path.to_string_lossy());
        let source = format!(
            r#"catch read_text_or_throw {source_path}:
    fs_err::not_found path, _ -> "missing:" + path
    fs_err::denied path, _ -> "denied:" + path
    fs_err::invalid_path text, _ -> "invalid:" + text
"#
        );

        let (results, stdout) = eval_source_with_std_host(&source);

        assert!(stdout.is_empty());
        assert_eq!(
            results,
            vec![TestValue::String(format!(
                "missing:{}",
                path.to_string_lossy()
            ))]
        );
    }

    #[test]
    fn vm_wraps_std_fs_error_as_result() {
        let path = temp_test_path("yulang-wrap-missing-text");
        let source_path = yulang_string_literal(&path.to_string_lossy());
        let source = format!("fs_err::wrap (read_text_or_throw {source_path})\n");

        let (results, stdout) = eval_source_with_std_host(&source);

        assert!(stdout.is_empty());
        assert_eq!(
            results,
            vec![TestValue::Variant {
                tag: "err".to_string(),
                value: Some(Box::new(TestValue::Variant {
                    tag: "not_found".to_string(),
                    value: Some(Box::new(TestValue::String(
                        path.to_string_lossy().to_string()
                    ))),
                })),
            }]
        );
    }

    #[test]
    fn vm_lifts_error_from_variant_with_up_helper() {
        let results = eval_source_with_std(
            r#"error io_a:
    bad_a str

error io_b:
    a from io_a

my run(): int = fail io_a::bad_a "oops"

io_b::wrap: io_b::up: run()
"#,
        );

        assert_eq!(
            results,
            vec![TestValue::Variant {
                tag: "err".to_string(),
                value: Some(Box::new(TestValue::Variant {
                    tag: "a".to_string(),
                    value: Some(Box::new(TestValue::Variant {
                        tag: "bad_a".to_string(),
                        value: Some(Box::new(TestValue::String("oops".to_string()))),
                    })),
                })),
            }]
        );
    }

    #[test]
    fn vm_runs_std_result_helpers() {
        let results = eval_source_with_std(
            r#"(
    std::result::map (result::ok 2) (\x -> x + 3),
    std::result::map (result::err "bad") (\x -> x + 3),
    std::result::and_then (result::ok 2) (\x -> result::ok (x * 4)),
    std::result::and_then (result::err "bad") (\x -> result::ok (x * 4)),
    std::result::unwrap_or (result::ok 7) 0,
    std::result::unwrap_or (result::err "bad") 9
)
"#,
        );

        assert_eq!(
            results,
            vec![TestValue::Tuple(vec![
                TestValue::Variant {
                    tag: "ok".to_string(),
                    value: Some(Box::new(TestValue::Int("5".to_string()))),
                },
                TestValue::Variant {
                    tag: "err".to_string(),
                    value: Some(Box::new(TestValue::String("bad".to_string()))),
                },
                TestValue::Variant {
                    tag: "ok".to_string(),
                    value: Some(Box::new(TestValue::Int("8".to_string()))),
                },
                TestValue::Variant {
                    tag: "err".to_string(),
                    value: Some(Box::new(TestValue::String("bad".to_string()))),
                },
                TestValue::Int("7".to_string()),
                TestValue::Int("9".to_string()),
            ])]
        );
    }

    #[test]
    fn vm_runs_symbol_variant_roots_through_case_function() {
        let results = eval_source_with_std(
            r#"my button option = case option:
    :label text -> "<button>%{text}</button>"
    :disabled -> "<button disabled></button>"

button: :label "send"
button: :disabled
"#,
        );

        assert_eq!(
            results,
            vec![
                TestValue::String("<button>send</button>".to_string()),
                TestValue::String("<button disabled></button>".to_string()),
            ]
        );
    }

    #[test]
    fn vm_runs_source_optional_record_argument_defaults() {
        let results = eval_source_with_std(
            "my area({width = 1, height = 2}) = width * height\n\
             area { width: 3 }\n\
             area {}\n\
             area { width: 3, height: 4 }\n",
        );

        assert_eq!(
            results,
            vec![
                TestValue::Int("6".to_string()),
                TestValue::Int("2".to_string()),
                TestValue::Int("12".to_string())
            ]
        );
    }

    #[test]
    fn vm_runs_source_optional_record_default_can_use_previous_field() {
        let results = eval_source_with_std(
            "my area({width = 2, height = width + 1}) = width * height\n\
             area { width: 3 }\n",
        );

        assert_eq!(results, vec![TestValue::Int("12".to_string())]);
    }

    #[test]
    fn vm_runs_source_optional_record_defaults_left_to_right() {
        let results = eval_source_with_std(
            "my f({a = 1, b = a + 1, c = b + 1}) = (a, b, c)\n\
             f {}\n\
             f { a: 10 }\n\
             f { a: 10, b: 20 }\n",
        );

        assert_eq!(
            results,
            vec![
                TestValue::Tuple(vec![
                    TestValue::Int("1".to_string()),
                    TestValue::Int("2".to_string()),
                    TestValue::Int("3".to_string()),
                ]),
                TestValue::Tuple(vec![
                    TestValue::Int("10".to_string()),
                    TestValue::Int("11".to_string()),
                    TestValue::Int("12".to_string()),
                ]),
                TestValue::Tuple(vec![
                    TestValue::Int("10".to_string()),
                    TestValue::Int("20".to_string()),
                    TestValue::Int("21".to_string()),
                ]),
            ]
        );
    }

    #[test]
    fn vm_runs_source_cast_declarations() {
        let results = eval_source_with_std(
            "struct user_id { raw: int }\n\
             cast(x: user_id): int = x.raw\n\
             cast(x: int): user_id = user_id { raw: x }\n\
             my id: user_id = 7\n\
             my raw: int = id\n\
             raw\n",
        );

        assert_eq!(results, vec![TestValue::Int("7".to_string())]);
    }

    #[test]
    fn vm_selects_cast_by_annotation_target() {
        let results = eval_source_with_std(
            "struct user_id { raw: int }\n\
             struct order_id { raw: int }\n\
             cast(x: int): user_id = user_id { raw: x + 10 }\n\
             cast(x: int): order_id = order_id { raw: x + 20 }\n\
             my user: user_id = 1\n\
             my order: order_id = 1\n\
             [user.raw, order.raw]\n",
        );

        assert_eq!(
            results,
            vec![TestValue::List(vec![
                TestValue::Int("11".to_string()),
                TestValue::Int("21".to_string()),
            ])]
        );
    }

    #[test]
    fn vm_inserts_cast_at_function_argument_boundary() {
        let results = eval_source_with_std(
            "struct user_id { raw: int }\n\
             cast(x: int): user_id = user_id { raw: x + 10 }\n\
             my read(x: user_id) = x.raw\n\
             read 1\n",
        );

        assert_eq!(results, vec![TestValue::Int("11".to_string())]);
    }

    #[test]
    fn vm_inserts_cast_at_if_branch_boundary() {
        let results = eval_source_with_std(
            "struct user_id { raw: int }\n\
             cast(x: int): user_id = user_id { raw: x + 10 }\n\
             my read(x: user_id) = x.raw\n\
             read (if true: 1 else: user_id { raw: 0 })\n",
        );

        assert_eq!(results, vec![TestValue::Int("11".to_string())]);
    }

    #[test]
    fn vm_runs_source_showcase_example() {
        let results = eval_source_with_std(SHOWCASE_SOURCE);

        assert_eq!(
            results,
            vec![
                TestValue::Int("7".to_string()),
                TestValue::List(vec![
                    TestValue::Int("2".to_string()),
                    TestValue::Int("6".to_string()),
                    TestValue::Int("4".to_string()),
                ]),
                TestValue::Int("5".to_string()),
                TestValue::Variant {
                    tag: "just".to_string(),
                    value: Some(Box::new(TestValue::Int("18".to_string()))),
                },
            ]
        );
    }

    #[test]
    fn vm_default_monomorphize_path_uses_principal_elaborate_pipeline() {
        assert!(
            std::env::var_os("YULANG_LEGACY_MONO_FIXPOINT").is_none(),
            "this regression test must run without the legacy monomorphize override"
        );

        let (_, profile) = runtime_module_with_std_profile(SHOWCASE_SOURCE);
        let pass_names = profile
            .passes
            .iter()
            .map(|pass| pass.name)
            .collect::<Vec<_>>();
        assert_eq!(
            pass_names,
            vec![
                "inline-polymorphic-wrappers",
                "principal-elaborate",
                "refresh-closed-schemes",
                "prune-unreachable",
            ]
        );
        assert_eq!(profile.demand_queue_profile().attempted, 0);
    }

    #[test]
    fn vm_runs_source_ref_scalar_assignment_example() {
        let results = eval_source_with_std(
            r#"{
    my $x = 10
    my $y = 20

    &x = $x + 1
    &y = $y + 1

    ($x, $y)
}
"#,
        );

        assert_eq!(
            results,
            vec![TestValue::Tuple(vec![
                TestValue::Int("11".to_string()),
                TestValue::Int("21".to_string()),
            ])]
        );
    }

    #[test]
    fn vm_runs_source_ref_field_assignment_example() {
        let results = eval_source_with_std(
            r#"struct point { x: int, y: int } with:
    our p.norm2: int = p.x * p.x + p.y * p.y
{
    my $p = point { x: 3, y: 2 }
    &p.y = 4
    $p.norm2
}
"#,
        );

        assert_eq!(results, vec![TestValue::Int("25".to_string())]);
    }

    #[test]
    fn vm_runs_source_ref_list_index_assignment_example() {
        let results = eval_source_with_std(
            r#"{
    my $xs = [2, 3, 4]
    &xs[1] = 6
    $xs
}
"#,
        );

        assert_eq!(
            results,
            vec![TestValue::List(vec![
                TestValue::Int("2".to_string()),
                TestValue::Int("6".to_string()),
                TestValue::Int("4".to_string()),
            ])]
        );
    }

    #[test]
    fn vm_runs_source_ref_multiple_scalar_assignment_example() {
        let results = eval_source_with_std(
            r#"{
    my $x = 1
    my $y = 10
    &x = $x + 4
    &y = $y + $x
    ($x, $y)
}
"#,
        );

        assert_eq!(
            results,
            vec![TestValue::Tuple(vec![
                TestValue::Int("5".to_string()),
                TestValue::Int("15".to_string()),
            ])]
        );
    }

    #[test]
    fn vm_runs_source_ref_nested_projection_assignment_example() {
        let results = eval_source_with_std(
            r#"struct point { x: int, y: int }
{
    my $rows = [point { x: 1, y: 2 }, point { x: 3, y: 4 }]
    &rows[1].y = 9
    $rows[1].y
}
"#,
        );

        assert_eq!(results, vec![TestValue::Int("9".to_string())]);
    }

    #[test]
    fn vm_runs_source_bool_and_comparison_examples() {
        let results = eval_source_with_std(
            "my a = not false\n\
             my b = not not true\n\
             my c = true and false\n\
             my d = 1 == 1\n\
             (a, b, c, d)\n",
        );

        assert_eq!(
            results,
            vec![TestValue::Tuple(vec![
                TestValue::Bool(true),
                TestValue::Bool(true),
                TestValue::Bool(false),
                TestValue::Bool(true),
            ])]
        );
    }

    #[test]
    fn vm_runs_lazy_bool_operator_without_evaluating_rhs() {
        let (results, stdout) = eval_source_with_std_host(
            "my bad_and() = std::flow::sub::sub:\n\
             \tprintln \"bad-and\"\n\
             \ttrue\n\
             my bad_or() = std::flow::sub::sub:\n\
             \tprintln \"bad-or\"\n\
             \tfalse\n\
             my a = false and bad_and()\n\
             my b = true or bad_or()\n\
             (a, b)\n",
        );

        assert_eq!(
            results,
            vec![TestValue::Tuple(vec![
                TestValue::Bool(false),
                TestValue::Bool(true),
            ])]
        );
        assert_eq!(stdout, "");
    }

    #[test]
    fn vm_runs_source_if_int_float_join_example() {
        let results = eval_source("my x = if true { 1 } else { 2.0 }\nx\n");

        assert_eq!(results, vec![TestValue::Float("1.0".to_string())]);
    }

    #[test]
    fn vm_runs_source_list_pattern_empty_and_head_spread() {
        let results = eval_source_with_std(
            "my first_or_zero(xs: list int) = case xs:\n  [] -> 0\n  [x, ..rest] -> x\nfirst_or_zero [4, 5, 6]\n",
        );

        assert_eq!(results, vec![TestValue::Int("4".to_string())]);
    }

    #[test]
    fn vm_runs_source_list_pattern_middle_spread_and_suffix() {
        let results = eval_source_with_std(
            "my split(xs: list int) = case xs:\n  [head, ..middle, tail] -> (head, middle, tail)\nsplit [1, 2, 3, 4]\n",
        );

        assert_eq!(
            results,
            vec![TestValue::Tuple(vec![
                TestValue::Int("1".to_string()),
                TestValue::List(vec![
                    TestValue::Int("2".to_string()),
                    TestValue::Int("3".to_string()),
                ]),
                TestValue::Int("4".to_string()),
            ])]
        );
    }

    #[test]
    fn vm_runs_source_list_pattern_tail_spread() {
        let results = eval_source_with_std(
            "my last_or_zero(xs: list int) = case xs:\n  [] -> 0\n  [..init, z] -> z\nlast_or_zero [4, 5, 6]\n",
        );

        assert_eq!(results, vec![TestValue::Int("6".to_string())]);
    }

    #[test]
    fn vm_runs_source_list_pattern_fixed_len_mismatch_falls_through() {
        let results = eval_source_with_std(
            "my exact_or_zero(xs: list int) = case xs:\n  [a, b] -> a\n  _ -> 0\nexact_or_zero [7]\n",
        );

        assert_eq!(results, vec![TestValue::Int("0".to_string())]);
    }

    #[test]
    fn vm_runs_source_nested_list_pattern_wildcards() {
        let results = eval_source_with_std(
            "case [[1, 2], [3, 4]]:\n  [[0, _], _] -> 9\n  [[1, a], [3, b]] -> a + b\n  _ -> 0\n",
        );

        assert_eq!(results, vec![TestValue::Int("6".to_string())]);
    }

    #[test]
    fn vm_runs_source_list_expr_spread() {
        let results = eval_source_with_std("[1, ..[2, 3], 4]\n");

        assert_eq!(
            results,
            vec![TestValue::List(vec![
                TestValue::Int("1".to_string()),
                TestValue::Int("2".to_string()),
                TestValue::Int("3".to_string()),
                TestValue::Int("4".to_string()),
            ])]
        );
    }

    #[test]
    fn vm_runs_source_list_expr_newline_separated_items() {
        let results = eval_source_with_std("[\n    1\n    2\n    3\n    4\n]\n");

        assert_eq!(
            results,
            vec![TestValue::List(vec![
                TestValue::Int("1".to_string()),
                TestValue::Int("2".to_string()),
                TestValue::Int("3".to_string()),
                TestValue::Int("4".to_string()),
            ])]
        );
    }

    #[test]
    fn vm_runs_source_list_expr_keeps_indented_continuation_in_item() {
        let results = eval_source_with_std("[\n    1 +\n        2\n    3\n]\n");

        assert_eq!(
            results,
            vec![TestValue::List(vec![
                TestValue::Int("3".to_string()),
                TestValue::Int("3".to_string()),
            ])]
        );
    }

    #[test]
    fn vm_runs_source_namespaced_apply_colon_indent_block_example() {
        let results = eval_source_with_std("std::sub::sub:\n  my x = 1\n  x\n");

        assert_eq!(results, vec![TestValue::Int("1".to_string())]);
    }

    #[test]
    fn vm_runs_source_list_find_example() {
        let results = eval_source_with_std("[1, 2, 3, 4].find: \\x -> x > 3\n");

        assert_eq!(
            results,
            vec![TestValue::Variant {
                tag: "just".to_string(),
                value: Some(Box::new(TestValue::Int("4".to_string()))),
            }]
        );
    }

    #[test]
    fn vm_runs_source_list_contains_example() {
        let results = eval_source_with_std(
            "my yes = [1, 2, 3, 4].contains 3\n\
             my no = [1, 2, 3, 4].contains 9\n\
             (yes, no)\n",
        );

        assert_eq!(
            results,
            vec![TestValue::Tuple(vec![
                TestValue::Bool(true),
                TestValue::Bool(false),
            ])]
        );
    }

    #[test]
    fn vm_runs_source_string_examples() {
        let results = eval_source_with_std(
            "my a = std::str::concat(\"yu\", \"lang\")\n\
             my b = \"ok\"\n\
             my c = \"a\\nb\\u{21}\"\n\
             my name = \"yu\"\n\
             my d = \"hello %{name}\"\n\
             my e = \"n = %{12}\"\n\
             my f = \"ok = %{true}\"\n\
             my g = std::str::splice \"aあ🙂z\" (range 1 3) \"bc\"\n\
             my h: string = \"alias\"\n\
             my i = id \"ok\"\n\
             my j = \"aあ🙂\"[1]\n\
             my k = \"aあ🙂z\"[range 1 3]\n\
             (a, b, c, d, e, f, g, h, i, j, k)\n",
        );

        assert_eq!(
            results,
            vec![TestValue::Tuple(vec![
                TestValue::String("yulang".to_string()),
                TestValue::String("ok".to_string()),
                TestValue::String("a\nb!".to_string()),
                TestValue::String("hello yu".to_string()),
                TestValue::String("n = 12".to_string()),
                TestValue::String("ok = true".to_string()),
                TestValue::String("abcz".to_string()),
                TestValue::String("alias".to_string()),
                TestValue::String("ok".to_string()),
                TestValue::String("あ".to_string()),
                TestValue::String("あ🙂".to_string()),
            ])]
        );
    }

    #[test]
    fn vm_runs_source_list_index_examples() {
        let results = eval_source_with_std(
            "my a = [10, 20, 30][1]\n\
             my b = [1, 2, 3, 4][range 1 3]\n\
             (a, b)\n",
        );

        assert_eq!(
            results,
            vec![TestValue::Tuple(vec![
                TestValue::Int("20".to_string()),
                TestValue::List(vec![
                    TestValue::Int("2".to_string()),
                    TestValue::Int("3".to_string()),
                ]),
            ])]
        );
    }

    #[test]
    fn vm_runs_source_list_index_through_function_examples() {
        let results = eval_source_with_std(
            "my get1(xs: list int) = xs[1]\n\
             my slice(xs: list int) = xs[inclusive 1 2]\n\
             my xs = [1, 2, 3, 4]\n\
             (get1 xs, slice xs)\n",
        );

        assert_eq!(
            results,
            vec![TestValue::Tuple(vec![
                TestValue::Int("2".to_string()),
                TestValue::List(vec![
                    TestValue::Int("2".to_string()),
                    TestValue::Int("3".to_string()),
                ]),
            ])]
        );
    }

    #[test]
    fn vm_runs_source_list_open_range_index_root_example() {
        let results = eval_source_with_std("my xs: list int = [1, 2, 3, 4]\nxs[2..]\n");

        assert_eq!(
            results,
            vec![TestValue::List(vec![
                TestValue::Int("3".to_string()),
                TestValue::Int("4".to_string()),
            ])]
        );
    }

    #[test]
    fn vm_runs_source_list_range_operator_index_examples() {
        let results = eval_source_with_std(
            "my xs: list int = [1, 2, 3, 4]\n\
             my a = xs[1..2]\n\
             my b = xs[1..<3]\n\
             my c = xs[1<..2]\n\
             my d = xs[1<..<3]\n\
             my e = xs[..2]\n\
             my f = xs[..<2]\n\
             my g = xs[2..]\n\
             my h = xs[1<..]\n\
             (a, b, c, d, e, f, g, h)\n",
        );

        assert_eq!(
            results,
            vec![TestValue::Tuple(vec![
                TestValue::List(vec![
                    TestValue::Int("2".to_string()),
                    TestValue::Int("3".to_string()),
                ]),
                TestValue::List(vec![
                    TestValue::Int("2".to_string()),
                    TestValue::Int("3".to_string()),
                ]),
                TestValue::List(vec![TestValue::Int("3".to_string())]),
                TestValue::List(vec![TestValue::Int("3".to_string())]),
                TestValue::List(vec![
                    TestValue::Int("1".to_string()),
                    TestValue::Int("2".to_string()),
                    TestValue::Int("3".to_string()),
                ]),
                TestValue::List(vec![
                    TestValue::Int("1".to_string()),
                    TestValue::Int("2".to_string()),
                ]),
                TestValue::List(vec![
                    TestValue::Int("3".to_string()),
                    TestValue::Int("4".to_string()),
                ]),
                TestValue::List(vec![
                    TestValue::Int("3".to_string()),
                    TestValue::Int("4".to_string()),
                ]),
            ])]
        );
    }

    #[test]
    fn vm_runs_source_string_range_operator_index_examples() {
        let results = eval_source_with_std(
            "my s = \"abcd\"\n\
             my a = s[1..2]\n\
             my b = s[1..<3]\n\
             my c = s[1<..2]\n\
             my d = s[1<..<3]\n\
             my e = s[..2]\n\
             my f = s[..<2]\n\
             my g = s[2..]\n\
             my h = s[1<..]\n\
             (a, b, c, d, e, f, g, h)\n",
        );

        assert_eq!(
            results,
            vec![TestValue::Tuple(vec![
                TestValue::String("bc".to_string()),
                TestValue::String("bc".to_string()),
                TestValue::String("c".to_string()),
                TestValue::String("c".to_string()),
                TestValue::String("abc".to_string()),
                TestValue::String("ab".to_string()),
                TestValue::String("cd".to_string()),
                TestValue::String("cd".to_string()),
            ])]
        );
    }

    #[test]
    fn vm_runs_source_polymorphic_id_at_multiple_types() {
        let results = eval_source_with_std(
            "my a = id 1\n\
             my b = id true\n\
             my c = id \"ok\"\n\
             (a, b, c)\n",
        );

        assert_eq!(
            results,
            vec![TestValue::Tuple(vec![
                TestValue::Int("1".to_string()),
                TestValue::Bool(true),
                TestValue::String("ok".to_string()),
            ])]
        );
    }

    #[test]
    fn vm_runs_source_polymorphic_compose_binding() {
        let results = eval_source_with_std(
            "my f = compose (\\x -> std::int::add x 1) (\\x -> std::int::mul x 2)\n\
             f 3\n",
        );

        assert_eq!(results, vec![TestValue::Int("7".to_string())]);
    }

    #[test]
    fn vm_runs_source_junction_example() {
        let results = eval_source_with_std(JUNCTION_SOURCE);

        assert_eq!(results, vec![TestValue::Int("1".to_string())]);
    }

    #[test]
    fn vm_runs_source_struct_constructor_and_method_example() {
        let results = eval_source_with_std(STRUCT_METHOD_SOURCE);

        assert_eq!(results, vec![TestValue::Int("1".to_string())]);
    }

    #[test]
    fn vm_runs_source_parenthesized_annotated_method_param() {
        let results = eval_source_with_std(
            "struct point { x: int, y: int } with:\n\
             \t our p.norm2 = p.x * p.x + p.y * p.y\n\
             \n\
             my get_norm (p: point) : int = p.norm2\n\
             get_norm (point { x: 3, y: 4 })\n",
        );

        assert_eq!(results, vec![TestValue::Int("25".to_string())]);
    }

    #[test]
    fn vm_runs_source_catch_value_arm_example() {
        let results = eval_source("my f x = catch x:\n  y -> 7\n\nf 1\n");

        assert_eq!(results, vec![TestValue::Int("7".to_string())]);
    }

    #[test]
    fn vm_runs_source_effectful_role_method_with_handler() {
        let results = eval_source(ROLE_EFFECT_HANDLER_SOURCE);

        assert_eq!(results, vec![TestValue::Bool(true)]);
    }

    #[test]
    fn vm_runs_source_effectful_role_method_through_helper_binding() {
        let results = eval_source(ROLE_EFFECT_HELPER_SOURCE);

        assert_eq!(results, vec![TestValue::Bool(true)]);
    }

    #[test]
    fn vm_runs_source_effect_handler_return_example() {
        let results = eval_source_with_std(
            r#"pub act out:
  pub say: str -> ()

catch out::say "hi":
    out::say msg, _ -> "handled:" + msg
"#,
        );

        assert_eq!(results, vec![TestValue::String("handled:hi".to_string())]);
    }

    #[test]
    fn vm_runs_source_effect_handler_return_and_resume_example() {
        let results = eval_source_with_std(
            r#"pub act out:
  pub say: str -> ()

catch out::say "hi":
    out::say msg, _ -> "handled:" + msg

catch out::say "hi":
    out::say _, k -> k ()
    value -> value
"#,
        );

        assert_eq!(
            results,
            vec![TestValue::String("handled:hi".to_string()), TestValue::Unit,]
        );
    }

    #[test]
    fn vm_hides_unannotated_higher_order_callback_effect_from_local_handler() {
        let results = eval_source_with_std(
            r#"act undet:
  our bool: () -> bool

my shallow(f) = catch f():
  undet::bool(), _ -> true

my outer(x: [_] bool) = catch x:
  undet::bool(), _ -> false

outer(shallow(\() -> undet::bool()))
"#,
        );

        assert_eq!(results, vec![TestValue::Bool(false)]);
    }

    #[test]
    fn vm_keeps_wildcard_higher_order_callback_effect_visible_to_local_handler() {
        let results = eval_source_with_std(
            r#"act undet:
  our bool: () -> bool

my shallow(f: () -> [_] bool) = catch f():
  undet::bool(), _ -> true
  value -> value

shallow(\() -> undet::bool())
"#,
        );

        assert_eq!(results, vec![TestValue::Bool(true)]);
    }

    #[test]
    fn vm_keeps_only_selectively_annotated_thunk_effect_visible_to_local_handler() {
        let results = eval_source_with_std(
            r#"act a:
  our get: () -> int

act b:
  our get: () -> int

my shallow(x: [a] int) = catch x:
  a::get(), _ -> 1
  b::get(), _ -> 2
  value -> value

my outer(x: [_] int) = catch x:
  b::get(), _ -> 20

(
  shallow(a::get()),
  outer(shallow(b::get()))
)
"#,
        );

        assert_eq!(
            results,
            vec![TestValue::Tuple(vec![
                TestValue::Int("1".to_string()),
                TestValue::Int("20".to_string()),
            ])]
        );
    }

    #[test]
    fn vm_rejects_function_value_as_effectful_handler_input() {
        let err = runtime_module_with_std_result(
            r#"pub act out:
  pub say: str -> ()

our prog() =
    out::say "first"
    out::say "second"
    42

our listen(x: [_] _, log: str): (_, str) = catch x:
    out::say o, k -> listen(k (), log + o + "|")
    v -> (v, log)

listen prog ""
"#,
        )
        .unwrap_err();

        assert!(matches!(err, RuntimeError::ExpectedThunk { .. }));
    }

    #[test]
    fn vm_runs_source_for_loop_last_examples() {
        let results = eval_source_with_std(FOR_LOOP_LAST_SOURCE);

        assert_eq!(results, vec![TestValue::Unit]);
    }

    #[test]
    fn vm_runs_source_for_loop_with_unused_item_binding() {
        let results = eval_source_with_std(
            r#"{
    my $count = 0
    for i in [1, 2, 3]:
        &count = $count + 1
    $count
}
"#,
        );

        assert_eq!(results, vec![TestValue::Int("3".to_string())]);
    }

    #[test]
    fn vm_runs_source_for_range_with_unit_body() {
        let results = eval_source_with_std("for x in 0..3: ()\n");

        assert_eq!(results, vec![TestValue::Unit]);
    }

    #[test]
    fn vm_runs_lambda_destructuring_pattern_arguments() {
        let results = eval_source_with_std(
            r#"my f = \(x, y) -> x + y
f (1, 2)
"#,
        );

        assert_eq!(results, vec![TestValue::Int("3".to_string())]);
    }

    #[test]
    fn vm_runs_variant_payload_binding_that_shadows_constructor() {
        let results = eval_source_with_std(
            r#"pub error fs_err:
    not_found str

my read path =
    case path:
        "/missing" -> fail fs_err::not_found path
        _ -> "ok"

my res = fs_err::wrap: read "/missing"
case res:
    result::ok text -> text
    result::err err -> "err"
"#,
        );

        assert_eq!(results, vec![TestValue::String("err".to_string())]);
    }

    #[test]
    fn vm_runs_handler_with_wildcard_result_and_local_ref() {
        let results = eval_source_with_std(
            r#"pub act log:
    pub put: str -> ()

my run(action: [log; _] _): (_, list str) =
    my $entries = []
    my result = catch action:
        log::put msg, k -> k ()
        v -> v
    (result, $entries)

run: log::put "x"
"#,
        );

        assert_eq!(
            results,
            vec![TestValue::Tuple(vec![
                TestValue::Unit,
                TestValue::List(Vec::new())
            ])]
        );
    }

    #[test]
    fn vm_runs_source_for_loop_updates_annotated_ref_in_body() {
        let results = eval_source_with_std(
            r#"{
    my $items : list int = []
    for x in [1, 2, 3]:
        &items = $items + [x]
    $items
}
"#,
        );

        assert_eq!(
            results,
            vec![TestValue::List(vec![
                TestValue::Int("1".to_string()),
                TestValue::Int("2".to_string()),
                TestValue::Int("3".to_string()),
            ])]
        );
    }

    #[test]
    fn vm_runs_source_for_loop_last_range_example() {
        let results = eval_source_with_std(FOR_LOOP_LAST_RANGE_SOURCE);

        assert_eq!(results, vec![TestValue::Unit]);
    }

    #[test]
    fn vm_runs_source_sub_return_from_suffix_range_loop() {
        let results = eval_source_with_std(
            r#"sub:
    for x in 0..:
        if x == 5: return x
        else: ()
    0
"#,
        );

        assert_eq!(results, vec![TestValue::Int("5".to_string())]);
    }

    #[test]
    fn vm_runs_source_sub_return_multiline_expression() {
        let results = eval_source_with_std(
            r#"my f() = sub:
    return
        1 + 2 + 3 + 4

f()
"#,
        );

        assert_eq!(results, vec![TestValue::Int("10".to_string())]);
    }

    #[test]
    fn vm_runs_source_sub_return_nullfix_unit() {
        let results = eval_source_with_std(
            r#"my f() = sub:
    return

f()
"#,
        );

        assert_eq!(results, vec![TestValue::Unit]);
    }

    #[test]
    fn vm_runs_source_labeled_sub_return_examples() {
        let results = eval_source_with_std(
            r#"sub 'outer:
    return 7

sub 'outer:
    'outer.return 42
    0
"#,
        );

        assert_eq!(
            results,
            vec![
                TestValue::Int("7".to_string()),
                TestValue::Int("42".to_string())
            ]
        );
    }

    #[test]
    fn vm_runs_source_helper_sub_return_from_suffix_range_loop() {
        let results = eval_source_with_std(
            r#"my f x = return x
sub:
    for x in 0..:
        if x == 5: f x
        else: ()
    0
"#,
        );

        assert_eq!(results, vec![TestValue::Int("5".to_string())]);
    }

    #[test]
    fn vm_runs_std_undet_once_and_sub_return_roots() {
        let results = eval_source_with_std(
            r#"use std::undet::*

({
    my a = each 1..
    my b = each 1..
    my c = each 1..

    guard: a <= b
    guard: b <= c
    guard: a * a + b * b == c * c

    (a, b, c)
}).once

std::flow::sub::sub:
    for x in 0..:
        if x == 5: std::flow::sub::return x
        else: ()
    0
"#,
        );

        assert_eq!(
            results,
            vec![
                TestValue::Variant {
                    tag: "just".to_string(),
                    value: Some(Box::new(TestValue::Tuple(vec![
                        TestValue::Int("3".to_string()),
                        TestValue::Int("4".to_string()),
                        TestValue::Int("5".to_string()),
                    ]))),
                },
                TestValue::Int("5".to_string()),
            ]
        );
    }

    #[test]
    fn vm_runs_source_for_loop_last_mixed_examples() {
        let results = eval_source_with_std(FOR_LOOP_LAST_MIXED_SOURCE);

        assert_eq!(results, vec![TestValue::Unit, TestValue::Unit]);
    }

    #[test]
    fn vm_runs_local_binding_that_shadows_nullfix_operator() {
        let results = eval_source_with_std(
            r#"my last = 99
last
"#,
        );

        assert_eq!(results, vec![TestValue::Int("99".to_string())]);
    }

    #[test]
    fn runtime_lowers_handler_wildcard_result_join_after_let_bind() {
        runtime_module_with_std_result(
            r#"pub act log:
    pub put: str -> ()

my run_into_strings(action: [log; _] _): (_, list str) =
    my $entries = []
    my result = catch action:
        log::put msg, k ->
            &entries = $entries + [msg]
            k ()
        v -> v
    (result, $entries)

run_into_strings: {
    log::put "first"
    log::put "second"
    42
}
"#,
        )
        .expect("handler wildcard join should lower to runtime IR");
    }

    #[test]
    fn vm_runs_source_labeled_for_loop_control_examples() {
        let results = eval_source_with_std(
            r#"sub:
    for 'outer x in [1, 2, 3]:
        if x == 2:
            last 'outer
        else:
            ()
    return 7
    0
"#,
        );

        assert_eq!(results, vec![TestValue::Int("7".to_string())]);
    }

    #[test]
    fn vm_runs_source_labeled_for_next_inside_sub_callback() {
        let results = eval_source_with_std(
            r#"sub:
    for 'outer x in [1, 2, 3]:
        if x == 1:
            next 'outer
        else:
            return x
    0
"#,
        );

        assert_eq!(results, vec![TestValue::Int("2".to_string())]);
    }

    #[test]
    fn vm_runs_std_undet_each_fold_list_example() {
        let results =
            eval_source_with_std("use std::undet::*\n(each [1, 2, 3] + each [4, 5, 6]).list\n");

        assert_eq!(
            results,
            vec![TestValue::List(vec![
                TestValue::Int("5".to_string()),
                TestValue::Int("6".to_string()),
                TestValue::Int("7".to_string()),
                TestValue::Int("6".to_string()),
                TestValue::Int("7".to_string()),
                TestValue::Int("8".to_string()),
                TestValue::Int("7".to_string()),
                TestValue::Int("8".to_string()),
                TestValue::Int("9".to_string()),
            ])]
        );
    }

    #[test]
    fn vm_runs_std_undet_each_and_once_from_prelude() {
        let results = eval_source_with_std(
            r#"
(each [1, 2, 3] + each [4, 5, 6]).list

{
    my a = each 1..
    guard: a == 3
    a
} .once
"#,
        );

        assert_eq!(
            results,
            vec![
                TestValue::List(vec![
                    TestValue::Int("5".to_string()),
                    TestValue::Int("6".to_string()),
                    TestValue::Int("7".to_string()),
                    TestValue::Int("6".to_string()),
                    TestValue::Int("7".to_string()),
                    TestValue::Int("8".to_string()),
                    TestValue::Int("7".to_string()),
                    TestValue::Int("8".to_string()),
                    TestValue::Int("9".to_string()),
                ]),
                TestValue::Variant {
                    tag: "just".to_string(),
                    value: Some(Box::new(TestValue::Int("3".to_string()))),
                },
            ]
        );
    }

    #[test]
    fn monomorphizes_std_undet_each_with_observed_value_type() {
        let module =
            runtime_module_with_std("use std::undet::*\n(each [1, 2, 3] + each [4, 5, 6]).list\n");
        let each_monos = module
            .bindings
            .iter()
            .filter(|binding| mono_binding_named(binding, "each"))
            .collect::<Vec<_>>();
        assert!(!each_monos.is_empty());
        assert!(
            each_monos
                .iter()
                .any(|binding| function_returns_thunk_value_int(&binding.body.ty))
        );
        assert!(
            !each_monos
                .iter()
                .any(|binding| function_returns_thunk_value_never(&binding.body.ty))
        );

        let sub_monos = module
            .bindings
            .iter()
            .filter(|binding| mono_binding_named(binding, "sub"))
            .collect::<Vec<_>>();
        assert!(!sub_monos.is_empty());
        assert!(
            sub_monos
                .iter()
                .any(|binding| function_accepts_sub_int_thunk(&binding.body.ty))
        );

        let list_monos = module
            .bindings
            .iter()
            .filter(|binding| mono_binding_named(binding, "list"))
            .collect::<Vec<_>>();
        assert!(
            list_monos
                .iter()
                .any(|binding| function_accepts_undet_int_thunk_returns_int_list(&binding.body.ty))
        );
    }

    #[test]
    fn vm_runs_std_undet_each_logic_and_once_example() {
        let results = eval_source_with_std(UNDET_EACH_LOGIC_SOURCE);

        assert_eq!(
            results,
            vec![
                TestValue::List(vec![
                    TestValue::Int("5".to_string()),
                    TestValue::Int("6".to_string()),
                    TestValue::Int("6".to_string()),
                    TestValue::Int("7".to_string()),
                    TestValue::Int("7".to_string()),
                    TestValue::Int("7".to_string()),
                    TestValue::Int("8".to_string()),
                    TestValue::Int("8".to_string()),
                    TestValue::Int("9".to_string()),
                ]),
                TestValue::Variant {
                    tag: "just".to_string(),
                    value: Some(Box::new(TestValue::Int("5".to_string()))),
                },
            ]
        );
    }

    #[test]
    fn vm_runs_std_undet_infinite_range_guard_once_example() {
        let results = eval_source_with_std(RANGE_INFINITE_UNDET_SOURCE);

        assert_eq!(
            results,
            vec![TestValue::Variant {
                tag: "just".to_string(),
                value: Some(Box::new(TestValue::Int("3".to_string()))),
            }]
        );
    }

    #[test]
    fn add_id_does_not_overwrite_live_stack_marker() {
        let stack = guard_stack(&[(0, 1), (1, 2)]);
        let thunk = blocked_thunk(2, effect_type("undet"));
        let request = request(effect_path("io", "read"), Some(1), stack);

        let request = mark_request(request, &thunk);

        assert_eq!(request.blocked_id, Some(1));
    }

    #[test]
    fn add_id_overwrites_marker_outside_current_stack() {
        let stack = guard_stack(&[(0, 1), (1, 2)]);
        let thunk = blocked_thunk(2, effect_type("undet"));
        let request = request(effect_path("io", "read"), Some(99), stack);

        let request = mark_request(request, &thunk);

        assert_eq!(request.blocked_id, Some(2));
    }

    #[test]
    fn add_id_keeps_allowed_effect_unmarked() {
        let stack = guard_stack(&[(0, 1)]);
        let thunk = blocked_thunk(1, effect_type("undet"));
        let request = request(effect_path("undet", "branch"), None, stack);

        let request = mark_request(request, &thunk);

        assert_eq!(request.blocked_id, None);
    }

    #[test]
    fn catch_uses_entry_guard_stack_for_blocked_requests() {
        let module = empty_module();
        let mut vm = VmInterpreter::new(&module);
        let handler_stack = guard_stack(&[(0, 1)]);
        let inner_stack = handler_stack.push(GuardEntry {
            var: EffectIdVar(1),
            id: 2,
        });
        let request = request(effect_path("undet", "branch"), Some(2), inner_stack);
        let arm = handle_value_arm("undet", "branch", VmValue::Int("7".to_string()));

        let result = vm
            .handle_request(
                request,
                0,
                &[arm],
                &Env::new(),
                &handler_stack,
                &RuntimeType::core(named_type("int")),
            )
            .unwrap();

        assert_eq!(result, VmResult::Value(VmValue::Int("7".to_string())));
    }

    #[test]
    fn catch_skips_blocked_request_from_entry_guard_stack() {
        let module = empty_module();
        let mut vm = VmInterpreter::new(&module);
        let handler_stack = guard_stack(&[(0, 1)]);
        let request = request(
            effect_path("undet", "branch"),
            Some(1),
            handler_stack.clone(),
        );
        let arm = handle_value_arm("undet", "branch", VmValue::Int("7".to_string()));

        let result = vm
            .handle_request(
                request,
                0,
                &[arm],
                &Env::new(),
                &handler_stack,
                &RuntimeType::core(named_type("int")),
            )
            .unwrap();

        assert!(matches!(result, VmResult::Request(_)));
    }

    #[test]
    fn cloned_continuation_keeps_persistent_guard_stack() {
        let module = empty_module();
        let mut vm = VmInterpreter::new(&module);
        let parent = guard_stack(&[(0, 1)]);
        let child = parent.push(GuardEntry {
            var: EffectIdVar(1),
            id: 2,
        });
        let continuation = VmContinuation {
            frames: vec![Frame::LocalPushId {
                parent: parent.clone(),
            }],
            guard_stack: child.clone(),
        };
        let cloned = continuation.clone();

        assert_eq!(
            vm.resume(continuation, VmValue::Unit).unwrap(),
            VmResult::Value(VmValue::Unit)
        );
        assert_eq!(
            vm.resume(cloned, VmValue::Unit).unwrap(),
            VmResult::Value(VmValue::Unit)
        );
        assert!(child.contains(2));
        assert!(parent.contains(1));
        assert!(!parent.contains(2));
    }

    #[test]
    fn vm_applies_migrated_float_list_and_string_primitives() {
        assert_eq!(
            apply_primitive(
                typed_ir::PrimitiveOp::FloatAdd,
                &[
                    VmValue::Float("1.0".to_string()),
                    VmValue::Float("2.0".to_string())
                ],
            ),
            Ok(VmValue::Float("3.0".to_string()))
        );
        let range = apply_primitive(
            typed_ir::PrimitiveOp::ListIndexRange,
            &[
                VmValue::List(ListTree::from_items(vec![
                    Rc::new(VmValue::Int("1".to_string())),
                    Rc::new(VmValue::Int("2".to_string())),
                    Rc::new(VmValue::Int("3".to_string())),
                    Rc::new(VmValue::Int("4".to_string())),
                ])),
                range_value(1, 3),
            ],
        );
        let Ok(VmValue::List(range)) = range else {
            panic!("expected list range, got {range:?}");
        };
        assert_eq!(
            range
                .to_vec()
                .into_iter()
                .map(|value| (*value).clone())
                .collect::<Vec<_>>(),
            vec![VmValue::Int("2".to_string()), VmValue::Int("3".to_string())]
        );
        assert_eq!(
            apply_primitive(
                typed_ir::PrimitiveOp::StringIndexRange,
                &[
                    VmValue::String(StringTree::from_str("aあ🙂z")),
                    range_value(1, 3),
                ],
            ),
            Ok(VmValue::String(StringTree::from_str("あ🙂")))
        );
        assert_eq!(
            apply_primitive(
                typed_ir::PrimitiveOp::StringSplice,
                &[
                    VmValue::String(StringTree::from_str("aあ🙂z")),
                    range_value(1, 3),
                    VmValue::String(StringTree::from_str("bc")),
                ],
            ),
            Ok(VmValue::String(StringTree::from_str("abcz")))
        );
    }

    fn empty_module() -> Module {
        Module {
            path: typed_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: Vec::new(),
            roots: Vec::new(),
            role_impls: Vec::new(),
        }
    }

    fn blocked_thunk(guard_id: u64, allowed: typed_ir::Type) -> VmThunk {
        VmThunk {
            body: ThunkBody::Value(VmValue::Unit),
            env: Env::new(),
            guard_stack: GuardStack::default(),
            blocked: vec![BlockedEffect {
                guard_id,
                allowed,
                active: false,
            }],
        }
    }

    fn request(
        effect: typed_ir::Path,
        blocked_id: Option<u64>,
        guard_stack: GuardStack,
    ) -> VmRequest {
        VmRequest {
            effect,
            payload: VmValue::Unit,
            continuation: VmContinuation::new(guard_stack),
            blocked_id,
        }
    }

    fn handle_value_arm(effect: &str, op: &str, value: VmValue) -> HandleArm {
        HandleArm {
            effect: effect_path(effect, op),
            payload: Pattern::Wildcard {
                ty: RuntimeType::core(named_type("unit")),
            },
            resume: None,
            guard: None,
            body: value_expr(value),
        }
    }

    fn value_expr(value: VmValue) -> Expr {
        match value {
            VmValue::Int(value) => Expr::typed(
                ExprKind::Lit(typed_ir::Lit::Int(value)),
                RuntimeType::core(named_type("int")),
            ),
            VmValue::Unit => Expr::typed(
                ExprKind::Lit(typed_ir::Lit::Unit),
                RuntimeType::core(named_type("unit")),
            ),
            other => panic!("unsupported test arm value: {other:?}"),
        }
    }

    fn guard_stack(entries: &[(usize, u64)]) -> GuardStack {
        entries
            .iter()
            .fold(GuardStack::default(), |stack, (var, id)| {
                stack.push(GuardEntry {
                    var: EffectIdVar(*var),
                    id: *id,
                })
            })
    }

    fn effect_type(name: &str) -> typed_ir::Type {
        named_type(name)
    }

    fn named_type(name: &str) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: typed_ir::Path::from_name(typed_ir::Name(name.to_string())),
            args: Vec::new(),
        }
    }

    fn effect_path(effect: &str, op: &str) -> typed_ir::Path {
        typed_ir::Path::new(vec![
            typed_ir::Name(effect.to_string()),
            typed_ir::Name(op.to_string()),
        ])
    }

    fn range_value(start: i64, end: i64) -> VmValue {
        VmValue::Variant {
            tag: typed_ir::Name("within".to_string()),
            value: Some(Box::new(VmValue::Tuple(vec![
                VmValue::Variant {
                    tag: typed_ir::Name("included".to_string()),
                    value: Some(Box::new(VmValue::Int(start.to_string()))),
                },
                VmValue::Variant {
                    tag: typed_ir::Name("excluded".to_string()),
                    value: Some(Box::new(VmValue::Int(end.to_string()))),
                },
            ]))),
        }
    }

    fn eval_source(src: &str) -> Vec<TestValue> {
        let mut lowered =
            lower_virtual_source_with_options(src, None, SourceOptions::default()).unwrap();
        let program = export_core_program(&mut lowered.state);
        let module = lower_core_program(program)
            .and_then(monomorphize_module)
            .expect("lowered runtime module");
        let module = compile_vm_module(module).expect("compiled runtime VM module");
        test_values(module.eval_roots().expect("vm results"))
    }

    fn eval_source_with_std(src: &str) -> Vec<TestValue> {
        let src = src.to_string();
        run_with_large_stack(move || eval_source_with_std_inner(&src))
    }

    fn eval_source_with_std_host(src: &str) -> (Vec<TestValue>, String) {
        let src = src.to_string();
        run_with_large_stack(move || {
            let module = runtime_module_with_std_inner(&src);
            let module = compile_vm_module(module).expect("compiled runtime VM module");
            let output =
                crate::eval_roots_with_basic_host(&module).expect("vm results with host output");
            (test_values(output.results), output.stdout)
        })
    }

    fn eval_source_with_std_inner(src: &str) -> Vec<TestValue> {
        let module = runtime_module_with_std_inner(src);
        let module = compile_vm_module(module).expect("compiled runtime VM module");
        test_values(module.eval_roots().expect("vm results"))
    }

    fn runtime_module_with_std(src: &str) -> Module {
        let src = src.to_string();
        run_with_large_stack(move || runtime_module_with_std_inner(&src))
    }

    fn runtime_module_with_std_result(src: &str) -> RuntimeResult<Module> {
        let src = src.to_string();
        run_with_large_stack(move || runtime_module_with_std_result_inner(&src))
    }

    fn runtime_module_with_std_profile(
        src: &str,
    ) -> (Module, crate::monomorphize::MonomorphizeProfile) {
        let src = src.to_string();
        run_with_large_stack(move || runtime_module_with_std_profile_inner(&src))
    }

    fn runtime_module_with_std_inner(src: &str) -> Module {
        runtime_module_with_std_profile_inner(src).0
    }

    fn runtime_module_with_std_result_inner(src: &str) -> RuntimeResult<Module> {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            src,
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let program = export_core_program(&mut lowered.state);
        lower_core_program(program).and_then(monomorphize_module)
    }

    fn runtime_module_with_std_profile_inner(
        src: &str,
    ) -> (Module, crate::monomorphize::MonomorphizeProfile) {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            src,
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let program = export_core_program(&mut lowered.state);
        let module = lower_core_program(program).expect("lowered runtime module");
        monomorphize_module_profiled(module).expect("monomorphized runtime module")
    }

    fn mono_binding_named(binding: &Binding, base: &str) -> bool {
        binding.name.segments.last().is_some_and(|name| {
            name.0.strip_prefix(base).is_some_and(|suffix| {
                suffix.starts_with("__mono") || suffix.starts_with("__ddmono")
            })
        })
    }

    fn function_returns_thunk_value_int(ty: &RuntimeType) -> bool {
        let RuntimeType::Fun { ret, .. } = ty else {
            return false;
        };
        matches!(ret.as_ref(), RuntimeType::Thunk { value, .. } if is_int_hir_type(value))
    }

    fn function_returns_thunk_value_never(ty: &RuntimeType) -> bool {
        let RuntimeType::Fun { ret, .. } = ty else {
            return false;
        };
        matches!(
            ret.as_ref(),
            RuntimeType::Thunk {
                value,
                ..
            } if matches!(value.as_ref(), RuntimeType::Core(typed_ir::Type::Never))
        )
    }

    fn function_accepts_sub_int_thunk(ty: &RuntimeType) -> bool {
        let RuntimeType::Fun { param, ret } = ty else {
            return false;
        };
        let RuntimeType::Thunk { effect, .. } = param.as_ref() else {
            return false;
        };
        returns_int_value(ret) && effect_contains_sub_int(effect)
    }

    fn function_accepts_undet_int_thunk_returns_int_list(ty: &RuntimeType) -> bool {
        let RuntimeType::Fun { param, ret } = ty else {
            return false;
        };
        let RuntimeType::Thunk { effect, value } = param.as_ref() else {
            return false;
        };
        is_int_hir_type(value)
            && effect_contains_named(effect, "undet")
            && is_int_list_hir_type(ret)
    }

    fn is_int_hir_type(ty: &RuntimeType) -> bool {
        matches!(ty, RuntimeType::Core(ty) if is_int_core_type(ty))
    }

    fn returns_int_value(ty: &RuntimeType) -> bool {
        is_int_hir_type(ty)
            || matches!(ty, RuntimeType::Thunk { value, .. } if is_int_hir_type(value))
    }

    fn is_int_list_hir_type(ty: &RuntimeType) -> bool {
        matches!(
            ty,
            RuntimeType::Core(typed_ir::Type::Named { path, args })
                if path.segments.last().is_some_and(|name| name.0 == "list")
                    && matches!(args.as_slice(), [typed_ir::TypeArg::Type(item)] if is_int_core_type(item))
        )
    }

    fn is_int_core_type(ty: &typed_ir::Type) -> bool {
        matches!(ty, typed_ir::Type::Named { path, args } if args.is_empty() && path.segments.last().is_some_and(|name| name.0 == "int"))
    }

    fn effect_contains_sub_int(ty: &typed_ir::Type) -> bool {
        match ty {
            typed_ir::Type::Named { path, args } => {
                path.segments.last().is_some_and(|name| name.0 == "sub")
                    && matches!(args.as_slice(), [typed_ir::TypeArg::Type(arg)] if is_int_core_type(arg))
            }
            typed_ir::Type::Row { items, tail } => {
                items.iter().any(effect_contains_sub_int) || effect_contains_sub_int(tail)
            }
            typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => {
                items.iter().any(effect_contains_sub_int)
            }
            typed_ir::Type::Recursive { body, .. } => effect_contains_sub_int(body),
            _ => false,
        }
    }

    fn effect_contains_named(ty: &typed_ir::Type, expected: &str) -> bool {
        match ty {
            typed_ir::Type::Named { path, .. } => {
                path.segments.last().is_some_and(|name| name.0 == expected)
            }
            typed_ir::Type::Row { items, tail } => {
                items
                    .iter()
                    .any(|item| effect_contains_named(item, expected))
                    || effect_contains_named(tail, expected)
            }
            typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => items
                .iter()
                .any(|item| effect_contains_named(item, expected)),
            typed_ir::Type::Recursive { body, .. } => effect_contains_named(body, expected),
            _ => false,
        }
    }

    fn test_values(results: Vec<VmResult>) -> Vec<TestValue> {
        results
            .into_iter()
            .map(|result| match result {
                VmResult::Value(value) => test_value(value),
                VmResult::Request(request) => panic!("unexpected request: {:?}", request.effect),
            })
            .collect()
    }

    fn test_value(value: VmValue) -> TestValue {
        match value {
            VmValue::Int(value) => TestValue::Int(value),
            VmValue::Float(value) => TestValue::Float(value),
            VmValue::String(value) => TestValue::String(value.to_flat_string()),
            VmValue::Bool(value) => TestValue::Bool(value),
            VmValue::Unit => TestValue::Unit,
            VmValue::List(items) => TestValue::List(
                items
                    .to_vec()
                    .into_iter()
                    .map(|value| test_value((*value).clone()))
                    .collect(),
            ),
            VmValue::Tuple(items) => TestValue::Tuple(items.into_iter().map(test_value).collect()),
            VmValue::Record(fields) => TestValue::Record(
                fields
                    .into_iter()
                    .map(|(name, value)| (name.0, test_value(value)))
                    .collect(),
            ),
            VmValue::Variant { tag, value } => TestValue::Variant {
                tag: tag.0,
                value: value.map(|value| Box::new(test_value(*value))),
            },
            other => panic!("unsupported test value: {other:?}"),
        }
    }

    fn run_with_large_stack<T>(f: impl FnOnce() -> T + Send + 'static) -> T
    where
        T: Send + 'static,
    {
        thread::Builder::new()
            .stack_size(128 * 1024 * 1024)
            .spawn(f)
            .expect("spawn large-stack runtime VM test thread")
            .join()
            .unwrap()
    }

    fn temp_test_path(prefix: &str) -> PathBuf {
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system time after epoch")
            .as_nanos();
        std::env::temp_dir().join(format!("{prefix}-{nanos}.txt"))
    }

    fn yulang_string_literal(value: &str) -> String {
        let mut out = String::from("\"");
        for ch in value.chars() {
            match ch {
                '\\' => out.push_str("\\\\"),
                '"' => out.push_str("\\\""),
                '\n' => out.push_str("\\n"),
                '\r' => out.push_str("\\r"),
                '\t' => out.push_str("\\t"),
                ch => out.push(ch),
            }
        }
        out.push('"');
        out
    }
}
