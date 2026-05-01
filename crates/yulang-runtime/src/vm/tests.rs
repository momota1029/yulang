#[cfg(test)]
mod tests {
    use super::super::*;
    use crate::ir::{Binding, Module, Type as RuntimeType};
    use crate::{lower_core_program, monomorphize_module};
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
    fn vm_runs_source_primitive_float_add_example() {
        let results = eval_source_with_std("my x = std::float::add 1.0 2.0\nx\n");

        assert_eq!(results, vec![TestValue::Float("3.0".to_string())]);
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
    fn vm_runs_source_for_loop_last_examples() {
        let results = eval_source_with_std(FOR_LOOP_LAST_SOURCE);

        assert_eq!(results, vec![TestValue::Unit]);
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
            .handle_request(request, 0, &[arm], &Env::new(), &handler_stack)
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
            .handle_request(request, 0, &[arm], &Env::new(), &handler_stack)
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
                core_ir::PrimitiveOp::FloatAdd,
                &[
                    VmValue::Float("1.0".to_string()),
                    VmValue::Float("2.0".to_string())
                ],
            ),
            Ok(VmValue::Float("3.0".to_string()))
        );
        assert_eq!(
            apply_primitive(
                core_ir::PrimitiveOp::ListIndexRange,
                &[
                    VmValue::List(ListTree::from_items(vec![
                        VmValue::Int("1".to_string()),
                        VmValue::Int("2".to_string()),
                        VmValue::Int("3".to_string()),
                        VmValue::Int("4".to_string()),
                    ])),
                    range_value(1, 3),
                ],
            ),
            Ok(VmValue::List(ListTree::from_items(vec![
                VmValue::Int("2".to_string()),
                VmValue::Int("3".to_string()),
            ])))
        );
        assert_eq!(
            apply_primitive(
                core_ir::PrimitiveOp::StringIndexRange,
                &[
                    VmValue::String(StringTree::from_str("aあ🙂z")),
                    range_value(1, 3),
                ],
            ),
            Ok(VmValue::String(StringTree::from_str("あ🙂")))
        );
        assert_eq!(
            apply_primitive(
                core_ir::PrimitiveOp::StringSplice,
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
            path: core_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: Vec::new(),
            roots: Vec::new(),
        }
    }

    fn blocked_thunk(guard_id: u64, allowed: core_ir::Type) -> VmThunk {
        VmThunk {
            body: ThunkBody::Value(VmValue::Unit),
            env: Env::new(),
            guard_stack: GuardStack::default(),
            blocked: vec![BlockedEffect { guard_id, allowed }],
        }
    }

    fn request(
        effect: core_ir::Path,
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
                ExprKind::Lit(core_ir::Lit::Int(value)),
                RuntimeType::core(named_type("int")),
            ),
            VmValue::Unit => Expr::typed(
                ExprKind::Lit(core_ir::Lit::Unit),
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

    fn effect_type(name: &str) -> core_ir::Type {
        named_type(name)
    }

    fn named_type(name: &str) -> core_ir::Type {
        core_ir::Type::Named {
            path: core_ir::Path::from_name(core_ir::Name(name.to_string())),
            args: Vec::new(),
        }
    }

    fn effect_path(effect: &str, op: &str) -> core_ir::Path {
        core_ir::Path::new(vec![
            core_ir::Name(effect.to_string()),
            core_ir::Name(op.to_string()),
        ])
    }

    fn range_value(start: i64, end: i64) -> VmValue {
        VmValue::Variant {
            tag: core_ir::Name("within".to_string()),
            value: Some(Box::new(VmValue::Tuple(vec![
                VmValue::Variant {
                    tag: core_ir::Name("included".to_string()),
                    value: Some(Box::new(VmValue::Int(start.to_string()))),
                },
                VmValue::Variant {
                    tag: core_ir::Name("excluded".to_string()),
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
        run_with_large_stack(move || {
            let module = runtime_module_with_std_inner(&src);
            let module = compile_vm_module(module).expect("compiled runtime VM module");
            test_values(module.eval_roots().expect("vm results"))
        })
    }

    fn runtime_module_with_std(src: &str) -> Module {
        let src = src.to_string();
        run_with_large_stack(move || runtime_module_with_std_inner(&src))
    }

    fn runtime_module_with_std_inner(src: &str) -> Module {
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
        lower_core_program(program)
            .and_then(monomorphize_module)
            .expect("lowered runtime module")
    }

    fn mono_binding_named(binding: &Binding, base: &str) -> bool {
        binding.name.segments.last().is_some_and(|name| {
            name.0
                .strip_prefix(base)
                .is_some_and(|suffix| suffix.starts_with("__mono"))
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
            } if matches!(value.as_ref(), RuntimeType::Core(core_ir::Type::Never))
        )
    }

    fn function_accepts_sub_int_thunk(ty: &RuntimeType) -> bool {
        let RuntimeType::Fun { param, .. } = ty else {
            return false;
        };
        let RuntimeType::Thunk { effect, value } = param.as_ref() else {
            return false;
        };
        is_int_hir_type(value) && effect_contains_sub_int(effect)
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

    fn is_int_list_hir_type(ty: &RuntimeType) -> bool {
        matches!(
            ty,
            RuntimeType::Core(core_ir::Type::Named { path, args })
                if path.segments.last().is_some_and(|name| name.0 == "list")
                    && matches!(args.as_slice(), [core_ir::TypeArg::Type(item)] if is_int_core_type(item))
        )
    }

    fn is_int_core_type(ty: &core_ir::Type) -> bool {
        matches!(ty, core_ir::Type::Named { path, args } if args.is_empty() && path.segments.last().is_some_and(|name| name.0 == "int"))
    }

    fn effect_contains_sub_int(ty: &core_ir::Type) -> bool {
        match ty {
            core_ir::Type::Named { path, args } => {
                path.segments.last().is_some_and(|name| name.0 == "sub")
                    && matches!(args.as_slice(), [core_ir::TypeArg::Type(arg)] if is_int_core_type(arg))
            }
            core_ir::Type::Row { items, tail } => {
                items.iter().any(effect_contains_sub_int) || effect_contains_sub_int(tail)
            }
            core_ir::Type::Union(items) | core_ir::Type::Inter(items) => {
                items.iter().any(effect_contains_sub_int)
            }
            core_ir::Type::Recursive { body, .. } => effect_contains_sub_int(body),
            _ => false,
        }
    }

    fn effect_contains_named(ty: &core_ir::Type, expected: &str) -> bool {
        match ty {
            core_ir::Type::Named { path, .. } => {
                path.segments.last().is_some_and(|name| name.0 == expected)
            }
            core_ir::Type::Row { items, tail } => {
                items
                    .iter()
                    .any(|item| effect_contains_named(item, expected))
                    || effect_contains_named(tail, expected)
            }
            core_ir::Type::Union(items) | core_ir::Type::Inter(items) => items
                .iter()
                .any(|item| effect_contains_named(item, expected)),
            core_ir::Type::Recursive { body, .. } => effect_contains_named(body, expected),
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
            VmValue::List(items) => {
                TestValue::List(items.to_vec().into_iter().map(test_value).collect())
            }
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
}
