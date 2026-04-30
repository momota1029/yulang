use std::fs;
use std::path::PathBuf;
use std::thread;
use std::time::{SystemTime, UNIX_EPOCH};

use super::*;
use crate::display::dump::render_compact_results;

fn run_with_large_stack<T>(f: impl FnOnce() -> T + Send + 'static) -> T
where
    T: Send + 'static,
{
    thread::Builder::new()
        .stack_size(32 * 1024 * 1024)
        .spawn(f)
        .expect("spawn large-stack test thread")
        .join()
        .unwrap()
}

fn normalize_runtime_scheme_vars(text: &str) -> String {
    let letters = b"abcdefghijklmnopqrstuvwxyz";
    let bytes = text.as_bytes();
    let mut out = String::with_capacity(text.len());
    let mut i = 0;
    let mut names = std::collections::HashMap::<String, char>::new();
    let mut next = 0usize;
    while i < bytes.len() {
        let byte = bytes[i];
        let prev_ok =
            i == 0 || !((bytes[i - 1] as char).is_ascii_alphanumeric() || bytes[i - 1] == b'_');
        if byte == b't' && prev_ok {
            let mut j = i + 1;
            while j < bytes.len() && (bytes[j] as char).is_ascii_digit() {
                j += 1;
            }
            if j > i + 1 {
                let key = &text[i..j];
                let mapped = *names.entry(key.to_string()).or_insert_with(|| {
                    let idx = next;
                    next += 1;
                    letters.get(idx).copied().unwrap_or(b'z') as char
                });
                out.push(mapped);
                i = j;
                continue;
            }
        }
        out.push(byte as char);
        i += 1;
    }
    out
}

const PAT_RECORD_DEFAULT_SOURCE: &str = r#"act cfg:
    our read: { flag: bool, width: int } -> int

my header_sum { width = 1, height = 1 } =
    (width, height)

my named_header { width: local_width } =
    local_width

my named_default_header { width: local_width = 1 } =
    local_width

my named_mix { width: local_width = 1, height } =
    (local_width, height)

my nested_header { size: { width = 1, height } } =
    (width, height)

my nested_named { cfg: { width: local_width = 1 } } =
    local_width

my case_width x = case x:
    { width = 1 } -> width

my case_nested x = case x:
    { size: { width = 1, height } } -> (width, height)

my case_guard x = case x:
    { flag = true, width = 1 } if flag -> width
    _ -> 0

my catch_value x = catch x:
    { width = 1 } -> width

my catch_nested_value x = catch x:
    { size: { width = 1, height } } -> (width, height)

my catch_read x = catch x:
    cfg::read { width = 1 }, k -> width

my catch_read_guard x = catch x:
    cfg::read { flag = true, width = 1 }, k if flag -> width
"#;

const PAT_RECORD_SPREAD_SOURCE: &str = r#"my head_width { ..rest, width = 1 } =
    width

my tail_width { width = 1, ..rest } =
    width

my head_rest { ..rest, width = 1 } =
    rest

my tail_rest { width = 1, ..rest } =
    rest

my case_head x = case x:
    { ..rest, width = 1 } -> width

my case_tail x = case x:
    { width = 1, ..rest } -> width
"#;

const ROLE_OVERLAP_SOURCE: &str = r#"role Pick 'container 'key:
  type value
  our container.pick: 'key -> value

impl Pick 'a bool:
  type value = int

impl Pick int bool:
  type value = string

my concrete_wins = 1.pick true

role Lookup 'container 'key:
  type value
  our container.lookup: 'key -> value

impl Lookup 'a int:
  type value = bool

impl Lookup (list 'a) int:
  type value = 'a

my generic_wins(xs: list string) = xs.lookup 0

role Fetch 'container 'key:
  type value
  our container.fetch: 'key -> value

impl Fetch int 'a:
  type value = string

impl Fetch 'a bool:
  type value = int

my ambiguous = 1.fetch true
"#;

#[test]
fn lowers_imported_operator_syntax_from_source_loader() {
    let root = temp_root("tir-operator-syntax");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("main.yu"),
        "mod ops\nuse ops::*\nmy y = 1 %% true\n",
    )
    .unwrap();
    fs::write(
        root.join("ops.yu"),
        "pub infix (%%) 50 51 = \\x -> \\y -> x\n",
    )
    .unwrap();

    let mut lowered =
        lower_entry_with_options(root.join("main.yu"), SourceOptions::default()).unwrap();
    let rendered = render_compact_results(&mut lowered.state);
    let y = rendered
        .iter()
        .find(|(name, _)| name == "y")
        .expect("y should be rendered");

    assert_eq!(y.1, "int");

    let _ = fs::remove_dir_all(root);
}
#[test]
fn lowers_implicit_prelude_from_source_loader() {
    let root = temp_root("tir-implicit-prelude");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("std")).unwrap();
    fs::write(root.join("main.yu"), "my y = id 1\n").unwrap();
    fs::write(root.join("std").join("prelude.yu"), "pub id x = x\n").unwrap();

    let mut lowered = lower_entry_with_options(
        root.join("main.yu"),
        SourceOptions {
            std_root: Some(root.join("std")),
            implicit_prelude: true,
            search_paths: Vec::new(),
        },
    )
    .unwrap();
    lowered.state.finalize_compact_results();
    let mut paths = crate::export::paths::collect_canonical_binding_paths(&lowered.state)
        .into_iter()
        .map(|(def, path)| (path, def))
        .collect::<Vec<_>>();
    paths.sort_by(|(lhs_path, lhs_def), (rhs_path, rhs_def)| {
        let lhs_key = lhs_path
            .segments
            .iter()
            .map(|name| name.0.as_str())
            .collect::<Vec<_>>();
        let rhs_key = rhs_path
            .segments
            .iter()
            .map(|name| name.0.as_str())
            .collect::<Vec<_>>();
        lhs_key
            .cmp(&rhs_key)
            .then_with(|| lhs_def.0.cmp(&rhs_def.0))
    });
    let rendered = crate::display::dump::collect_compact_results_for_paths(&lowered.state, &paths);
    let y = rendered
        .iter()
        .find(|(name, _)| name == "y")
        .expect("y should be rendered");

    assert_eq!(y.1, "int");
    assert!(
        lowered
            .diagnostic_source
            .starts_with("use std::prelude::*\n")
    );

    let _ = fs::remove_dir_all(root);
}

#[test]
fn lowers_implicit_prelude_primitive_binding_from_source_loader() {
    let root = temp_root("tir-implicit-primitive-binding");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("std")).unwrap();
    fs::write(root.join("main.yu"), "my y = add 1 2\n").unwrap();
    fs::write(
        root.join("std").join("prelude.yu"),
        include_str!("../../../../lib/std/prelude.yu"),
    )
    .unwrap();

    let mut lowered = lower_entry_with_options(
        root.join("main.yu"),
        SourceOptions {
            std_root: Some(root.join("std")),
            implicit_prelude: true,
            search_paths: Vec::new(),
        },
    )
    .unwrap();
    lowered.state.finalize_compact_results();
    let rendered = crate::display::dump::collect_compact_results_for_paths(
        &lowered.state,
        &lowered.state.ctx.collect_all_binding_paths(),
    );
    let y = rendered
        .iter()
        .find(|(name, _)| name == "y")
        .expect("y should be rendered");

    assert_eq!(y.1, "int");

    let _ = fs::remove_dir_all(root);
}

#[test]
fn lowers_pipeline_as_first_argument_to_rhs_spine() {
    let root = temp_root("tir-pipeline-first-argument");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("std")).unwrap();
    fs::write(root.join("main.yu"), "my y = 1 | add 2\n").unwrap();
    fs::write(
        root.join("std").join("prelude.yu"),
        include_str!("../../../../lib/std/prelude.yu"),
    )
    .unwrap();

    let mut lowered = lower_entry_with_options(
        root.join("main.yu"),
        SourceOptions {
            std_root: Some(root.join("std")),
            implicit_prelude: true,
            search_paths: Vec::new(),
        },
    )
    .unwrap();
    let program = crate::export_core_program(&mut lowered.state);
    let y = program
        .program
        .bindings
        .iter()
        .find(|binding| binding.name.segments.last().map(|name| name.0.as_str()) == Some("y"))
        .expect("y should be exported");

    match &y.body {
        yulang_core_ir::Expr::Apply { callee, arg, .. } => {
            assert_eq!(
                arg.as_ref(),
                &yulang_core_ir::Expr::Lit(yulang_core_ir::Lit::Int("2".to_string()))
            );
            match callee.as_ref() {
                yulang_core_ir::Expr::Apply { callee, arg, .. } => {
                    assert_eq!(
                        arg.as_ref(),
                        &yulang_core_ir::Expr::Lit(yulang_core_ir::Lit::Int("1".to_string()))
                    );
                    match callee.as_ref() {
                        yulang_core_ir::Expr::Var(path) => {
                            let rendered = path
                                .segments
                                .iter()
                                .map(|segment| segment.0.as_str())
                                .collect::<Vec<_>>()
                                .join("::");
                            assert_eq!(rendered, "std::int::add");
                        }
                        other => panic!("expected pipeline callee, got {other:?}"),
                    }
                }
                other => panic!("expected first pipeline application, got {other:?}"),
            }
        }
        other => panic!("expected pipeline application body, got {other:?}"),
    }

    let _ = fs::remove_dir_all(root);
}

#[test]
fn lowers_builtin_arithmetic_syntax_from_implicit_prelude() {
    let root = temp_root("tir-implicit-arithmetic-syntax");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("std")).unwrap();
    fs::write(root.join("main.yu"), "my y = 1 + 2\n").unwrap();
    fs::write(
        root.join("std").join("prelude.yu"),
        include_str!("../../../../lib/std/prelude.yu"),
    )
    .unwrap();

    let mut lowered = lower_entry_with_options(
        root.join("main.yu"),
        SourceOptions {
            std_root: Some(root.join("std")),
            implicit_prelude: true,
            search_paths: Vec::new(),
        },
    )
    .unwrap();
    let rendered = render_compact_results(&mut lowered.state);
    let y = rendered
        .iter()
        .find(|(name, _)| name == "y")
        .expect("y should be rendered");

    assert_eq!(y.1, "int");

    let _ = fs::remove_dir_all(root);
}

#[test]
fn lowers_mixed_float_arithmetic_syntax_from_implicit_prelude() {
    let root = temp_root("tir-implicit-mixed-float-arithmetic-syntax");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("std")).unwrap();
    fs::write(root.join("main.yu"), "my y = 1.0 + 2\n").unwrap();
    fs::write(
        root.join("std").join("prelude.yu"),
        include_str!("../../../../lib/std/prelude.yu"),
    )
    .unwrap();

    let mut lowered = lower_entry_with_options(
        root.join("main.yu"),
        SourceOptions {
            std_root: Some(root.join("std")),
            implicit_prelude: true,
            search_paths: Vec::new(),
        },
    )
    .unwrap();
    let rendered = render_compact_results(&mut lowered.state);
    let y = rendered
        .iter()
        .find(|(name, _)| name == "y")
        .expect("y should be rendered");

    assert_eq!(y.1, "float");

    let _ = fs::remove_dir_all(root);
}

#[test]
fn lowers_builtin_float_primitive_from_source_loader() {
    let root = temp_root("tir-implicit-float-primitive");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("std")).unwrap();
    fs::write(root.join("main.yu"), "my y = std::float::add 1.0 2.0\n").unwrap();
    fs::write(
        root.join("std").join("prelude.yu"),
        include_str!("../../../../lib/std/prelude.yu"),
    )
    .unwrap();

    let mut lowered = lower_entry_with_options(
        root.join("main.yu"),
        SourceOptions {
            std_root: Some(root.join("std")),
            implicit_prelude: true,
            search_paths: Vec::new(),
        },
    )
    .unwrap();
    let rendered = render_compact_results(&mut lowered.state);
    let y = rendered
        .iter()
        .find(|(name, _)| name == "y")
        .expect("y should be rendered");

    assert_eq!(y.1, "float");

    let _ = fs::remove_dir_all(root);
}

#[test]
fn lowers_builtin_not_syntax_from_implicit_prelude() {
    let root = temp_root("tir-implicit-not-syntax");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("std")).unwrap();
    fs::write(root.join("main.yu"), "my x = not false\n").unwrap();
    fs::write(
        root.join("std").join("prelude.yu"),
        include_str!("../../../../lib/std/prelude.yu"),
    )
    .unwrap();

    let mut lowered = lower_entry_with_options(
        root.join("main.yu"),
        SourceOptions {
            std_root: Some(root.join("std")),
            implicit_prelude: true,
            search_paths: Vec::new(),
        },
    )
    .unwrap();
    let rendered = render_compact_results(&mut lowered.state);
    let x = rendered
        .iter()
        .find(|(name, _)| name == "x")
        .expect("x should be rendered");

    assert_eq!(x.1, "bool");

    let _ = fs::remove_dir_all(root);
}

#[test]
fn lowers_list_len_helper_from_implicit_prelude() {
    let root = temp_root("tir-implicit-list-len-helper");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("std")).unwrap();
    fs::write(root.join("main.yu"), "my size(xs: list int) = len xs\n").unwrap();
    fs::write(
        root.join("std").join("prelude.yu"),
        include_str!("../../../../lib/std/prelude.yu"),
    )
    .unwrap();

    let mut lowered = lower_entry_with_options(
        root.join("main.yu"),
        SourceOptions {
            std_root: Some(root.join("std")),
            implicit_prelude: true,
            search_paths: Vec::new(),
        },
    )
    .unwrap();
    let rendered = render_compact_results(&mut lowered.state);
    let size = rendered
        .iter()
        .find(|(name, _)| name == "size")
        .expect("size should be rendered");

    assert_eq!(
        size.1,
        "Len<std::list::list<int> | α> => (α & std::list::list<int>) -> int"
    );

    let _ = fs::remove_dir_all(root);
}

#[test]
fn lowers_list_view_raw_from_source_loader() {
    let root = temp_root("tir-list-view-raw");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("std")).unwrap();
    fs::write(
        root.join("main.yu"),
        "my inspect(xs: list int) = std::list::view_raw xs\n",
    )
    .unwrap();
    fs::write(
        root.join("std").join("prelude.yu"),
        include_str!("../../../../lib/std/prelude.yu"),
    )
    .unwrap();

    let mut lowered = lower_entry_with_options(
        root.join("main.yu"),
        SourceOptions {
            std_root: Some(root.join("std")),
            implicit_prelude: true,
            search_paths: Vec::new(),
        },
    )
    .unwrap();
    let rendered = render_compact_results(&mut lowered.state);
    let inspect = rendered
        .iter()
        .find(|(name, _)| name == "inspect")
        .expect("inspect should be rendered");

    assert_eq!(
        inspect.1,
        "std::list::list<int> -> std::list::list_view<int>"
    );

    let _ = fs::remove_dir_all(root);
}

#[test]
fn lowers_list_literal_from_source_loader() {
    let root = temp_root("tir-list-literal");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("std")).unwrap();
    fs::write(root.join("main.yu"), "my xs = [1, 2, 3]\n").unwrap();
    fs::write(
        root.join("std").join("prelude.yu"),
        include_str!("../../../../lib/std/prelude.yu"),
    )
    .unwrap();

    let mut lowered = lower_entry_with_options(
        root.join("main.yu"),
        SourceOptions {
            std_root: Some(root.join("std")),
            implicit_prelude: true,
            search_paths: Vec::new(),
        },
    )
    .unwrap();
    let rendered = render_compact_results(&mut lowered.state);
    let xs = rendered
        .iter()
        .find(|(name, _)| name == "xs")
        .expect("xs should be rendered");

    assert_eq!(xs.1, "std::list::list<int | α>");

    let _ = fs::remove_dir_all(root);
}

#[test]
fn lowers_list_index_from_implicit_prelude() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my first(xs: list int) = xs.index 0\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        let first = rendered
            .iter()
            .find(|(name, _)| name == "first")
            .expect("first should be rendered");

        assert_eq!(first.1, "std::list::list<int> -> int");
    });
}

#[test]
fn lowers_list_bracket_index_from_implicit_prelude() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my first(xs: list int) = xs[0]\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        let first = rendered
            .iter()
            .find(|(name, _)| name == "first")
            .expect("first should be rendered");

        assert_eq!(first.1, "std::list::list<int> -> int");
    });
}

#[test]
fn lowers_list_bracket_range_from_implicit_prelude() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my slice(xs: list int) = xs[range 1 3]\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        let slice = rendered
            .iter()
            .find(|(name, _)| name == "slice")
            .expect("slice should be rendered");

        assert_eq!(slice.1, "std::list::list<int> -> std::list::list<int>");
    });
}

#[test]
fn lowers_list_bracket_inclusive_range_from_implicit_prelude() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my slice(xs: list int) = xs[inclusive 1 2]\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        let slice = rendered
            .iter()
            .find(|(name, _)| name == "slice")
            .expect("slice should be rendered");

        assert_eq!(slice.1, "std::list::list<int> -> std::list::list<int>");
    });
}

#[test]
fn lowers_list_bracket_open_range_operator_from_implicit_prelude() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my slice(xs: list int) = xs[2..]\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        let slice = rendered
            .iter()
            .find(|(name, _)| name == "slice")
            .expect("slice should be rendered");

        assert_eq!(slice.1, "std::list::list<int> -> std::list::list<int>");
    });
}

#[test]
fn lowers_list_bracket_range_operator_forms_from_implicit_prelude() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my xs: list int = [1, 2, 3, 4]\n\
             my a = xs[1..2]\n\
             my b = xs[1..<3]\n\
             my c = xs[1<..2]\n\
             my d = xs[1<..<3]\n\
             my e = xs[..2]\n\
             my f = xs[..<2]\n\
             my g = xs[2..]\n\
             my h = xs[1<..]\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        for name in ["a", "b", "c", "d", "e", "f", "g", "h"] {
            let item = rendered
                .iter()
                .find(|(rendered_name, _)| rendered_name == name)
                .unwrap_or_else(|| panic!("{name} should be rendered"));
            assert_eq!(item.1, "std::list::list<int>");
        }
    });
}

#[test]
fn lowers_range_operator_forms_from_implicit_prelude() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my a = ..\n\
             my b = ..5\n\
             my c = ..<5\n\
             my d = 4..\n\
             my e = 4<..\n\
             my f = 1..2\n\
             my g = 1..<2\n\
             my h = 1<..2\n\
             my i = 1<..<2\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        for name in ["a", "b", "c", "d", "e", "f", "g", "h", "i"] {
            let item = rendered
                .iter()
                .find(|(rendered_name, _)| rendered_name == name)
                .unwrap_or_else(|| panic!("{name} should be rendered"));
            assert_eq!(item.1, "std::range::range");
        }
    });
}

#[test]
fn lowers_list_merge_from_implicit_prelude() {
    let root = temp_root("tir-implicit-list-merge");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("std")).unwrap();
    fs::write(
        root.join("main.yu"),
        "my joined(xs: list int, ys: list int) = merge xs ys\n",
    )
    .unwrap();
    fs::write(
        root.join("std").join("prelude.yu"),
        include_str!("../../../../lib/std/prelude.yu"),
    )
    .unwrap();

    let mut lowered = lower_entry_with_options(
        root.join("main.yu"),
        SourceOptions {
            std_root: Some(root.join("std")),
            implicit_prelude: true,
            search_paths: Vec::new(),
        },
    )
    .unwrap();
    let rendered = render_compact_results(&mut lowered.state);
    let joined = rendered
        .iter()
        .find(|(name, _)| name == "joined")
        .expect("joined should be rendered");

    assert_eq!(
        joined.1,
        "std::list::list<int> -> std::list::list<int> -> std::list::list<int>"
    );

    let _ = fs::remove_dir_all(root);
}

#[test]
fn lowers_list_index_range_raw_from_source_loader() {
    let root = temp_root("tir-list-index-range-raw");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("std")).unwrap();
    fs::write(
        root.join("main.yu"),
        "my slice(xs: list int) = std::list::index_range_raw xs 1 3\n",
    )
    .unwrap();
    fs::write(
        root.join("std").join("prelude.yu"),
        include_str!("../../../../lib/std/prelude.yu"),
    )
    .unwrap();

    let mut lowered = lower_entry_with_options(
        root.join("main.yu"),
        SourceOptions {
            std_root: Some(root.join("std")),
            implicit_prelude: true,
            search_paths: Vec::new(),
        },
    )
    .unwrap();
    let rendered = render_compact_results(&mut lowered.state);
    let slice = rendered
        .iter()
        .find(|(name, _)| name == "slice")
        .expect("slice should be rendered");

    assert_eq!(slice.1, "std::list::list<int> -> std::list::list<int>");

    let _ = fs::remove_dir_all(root);
}

#[test]
fn lowers_list_splice_raw_from_source_loader() {
    let root = temp_root("tir-list-splice-raw");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("std")).unwrap();
    fs::write(
        root.join("main.yu"),
        "my replace(xs: list int, ys: list int) = std::list::splice_raw xs 1 3 ys\n",
    )
    .unwrap();
    fs::write(
        root.join("std").join("prelude.yu"),
        include_str!("../../../../lib/std/prelude.yu"),
    )
    .unwrap();

    let mut lowered = lower_entry_with_options(
        root.join("main.yu"),
        SourceOptions {
            std_root: Some(root.join("std")),
            implicit_prelude: true,
            search_paths: Vec::new(),
        },
    )
    .unwrap();
    let rendered = render_compact_results(&mut lowered.state);
    let replace = rendered
        .iter()
        .find(|(name, _)| name == "replace")
        .expect("replace should be rendered");

    assert_eq!(
        replace.1,
        "std::list::list<int> -> std::list::list<int> -> std::list::list<int>"
    );

    let _ = fs::remove_dir_all(root);
}

#[test]
fn lowers_list_splice_from_source_loader() {
    let root = temp_root("tir-list-splice");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("std")).unwrap();
    fs::write(
        root.join("main.yu"),
        "my replace(xs: list int, ys: list int) = std::list::splice xs (range 1 3) ys\n",
    )
    .unwrap();
    fs::write(
        root.join("std").join("prelude.yu"),
        include_str!("../../../../lib/std/prelude.yu"),
    )
    .unwrap();

    let mut lowered = lower_entry_with_options(
        root.join("main.yu"),
        SourceOptions {
            std_root: Some(root.join("std")),
            implicit_prelude: true,
            search_paths: Vec::new(),
        },
    )
    .unwrap();
    let rendered = render_compact_results(&mut lowered.state);
    let replace = rendered
        .iter()
        .find(|(name, _)| name == "replace")
        .expect("replace should be rendered");

    assert_eq!(
        replace.1,
        "std::list::list<int> -> std::list::list<int> -> std::list::list<int>"
    );

    let _ = fs::remove_dir_all(root);
}

#[test]
fn keeps_builtin_list_primitives_generic_in_rendered_results() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my empty_list() = empty()\nmy singleton_list(x: int) = singleton x\nmy size(xs: list int) = len xs\nmy joined(xs: list int, ys: list int) = merge xs ys\nmy inspect(xs: list int) = std::list::view_raw xs\nmy first(xs: list int) = xs.index 0\nmy slice(xs: list int) = xs[range 0 1]\nmy slice_raw(xs: list int) = std::list::index_range_raw xs 0 1\nmy replace(xs: list int, ys: list int) = std::list::splice xs (range 0 1) ys\nmy replace_raw(xs: list int, ys: list int) = std::list::splice_raw xs 0 1 ys\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let program = crate::export_core_program(&mut lowered.state);
        let rendered = program
            .program
            .bindings
            .iter()
            .map(|binding| {
                (
                    binding
                        .name
                        .segments
                        .iter()
                        .map(|segment| segment.0.clone())
                        .collect::<Vec<_>>()
                        .join("::"),
                    crate::display::dump::format_runtime_export_scheme(&binding.scheme),
                )
            })
            .collect::<Vec<_>>();
        let find_rendered = |candidates: &[&str]| {
            rendered
                .iter()
                .find(|(name, _)| candidates.iter().any(|candidate| name == candidate))
                .map(|(_, scheme)| normalize_runtime_scheme_vars(scheme))
                .unwrap_or_else(|| panic!("expected one of {:?} to be rendered", candidates))
        };
        let list_len = find_rendered(&["std::list::len", "len"]);
        let list_empty = find_rendered(&["std::list::empty", "empty"]);
        let list_singleton = find_rendered(&["std::list::singleton", "singleton"]);
        let list_view = find_rendered(&["std::list::view_raw", "view_raw"]);
        let list_merge = find_rendered(&["std::list::merge", "merge"]);
        let list_index = find_rendered(&["std::list::index_raw", "index_raw"]);
        let list_index_range = find_rendered(&["std::list::index_range", "index_range"]);
        let list_index_range_raw =
            find_rendered(&["std::list::index_range_raw", "index_range_raw"]);
        let list_splice = find_rendered(&["std::list::splice"]);
        let list_splice_raw = find_rendered(&["std::list::splice_raw", "splice_raw"]);

        assert_eq!(list_empty, "unit -> std::list::list<a>");
        assert_eq!(list_singleton, "a -> std::list::list<a>");
        assert_eq!(list_len, "std::list::list<a> -> int");
        assert_eq!(
            list_merge,
            "std::list::list<a> -> std::list::list<a> -> std::list::list<a>"
        );
        assert_eq!(list_view, "std::list::list<a> -> std::list::list_view<a>");
        assert_eq!(list_index, "std::list::list<a> -> int -> a");
        assert_eq!(
            list_index_range,
            "std::list::list<a> -> std::range::range -> std::list::list<a>"
        );
        assert_eq!(
            list_index_range_raw,
            "std::list::list<a> -> int -> int -> std::list::list<a>"
        );
        assert_eq!(
            list_splice,
            "std::list::list<a> -> std::range::range -> std::list::list<a> -> std::list::list<a>"
        );
        assert_eq!(
            list_splice_raw,
            "std::list::list<a> -> int -> int -> std::list::list<a> -> std::list::list<a>"
        );
    });
}

#[test]
fn prelude_reexport_does_not_overwrite_list_len_primitive_body() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my size(xs: list int) = std::list::len xs\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let program = crate::export_core_program(&mut lowered.state);
        let list_len = program
            .program
            .bindings
            .iter()
            .find(|binding| {
                binding.name.segments
                    == [
                        yulang_core_ir::Name("std".to_string()),
                        yulang_core_ir::Name("list".to_string()),
                        yulang_core_ir::Name("len".to_string()),
                    ]
            })
            .expect("std::list::len should be exported");

        assert!(matches!(
            list_len.body,
            yulang_core_ir::Expr::PrimitiveOp(yulang_core_ir::PrimitiveOp::ListLen)
        ));
    });
}

#[test]
fn lowers_nested_not_syntax_from_implicit_prelude() {
    let root = temp_root("tir-implicit-nested-not-syntax");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("std")).unwrap();
    fs::write(root.join("main.yu"), "my x = not not true\n").unwrap();
    fs::write(
        root.join("std").join("prelude.yu"),
        include_str!("../../../../lib/std/prelude.yu"),
    )
    .unwrap();

    let mut lowered = lower_entry_with_options(
        root.join("main.yu"),
        SourceOptions {
            std_root: Some(root.join("std")),
            implicit_prelude: true,
            search_paths: Vec::new(),
        },
    )
    .unwrap();
    let rendered = render_compact_results(&mut lowered.state);
    let x = rendered
        .iter()
        .find(|(name, _)| name == "x")
        .expect("x should be rendered");

    assert_eq!(x.1, "bool");

    let _ = fs::remove_dir_all(root);
}

#[test]
fn lowers_boolean_short_circuit_syntax_from_implicit_prelude() {
    let root = temp_root("tir-implicit-bool-short-circuit");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("std")).unwrap();
    fs::write(root.join("main.yu"), "my x = true and false\n").unwrap();
    fs::write(
        root.join("std").join("prelude.yu"),
        include_str!("../../../../lib/std/prelude.yu"),
    )
    .unwrap();

    let mut lowered = lower_entry_with_options(
        root.join("main.yu"),
        SourceOptions {
            std_root: Some(root.join("std")),
            implicit_prelude: true,
            search_paths: Vec::new(),
        },
    )
    .unwrap();
    let rendered = render_compact_results(&mut lowered.state);
    let x = rendered
        .iter()
        .find(|(name, _)| name == "x")
        .expect("x should be rendered");

    assert_eq!(x.1, "bool");

    let _ = fs::remove_dir_all(root);
}

#[test]
fn lowers_builtin_eq_syntax_from_implicit_prelude() {
    let root = temp_root("tir-implicit-eq-syntax");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("std")).unwrap();
    fs::write(root.join("main.yu"), "my x = 1 == 1\n").unwrap();
    fs::write(
        root.join("std").join("prelude.yu"),
        include_str!("../../../../lib/std/prelude.yu"),
    )
    .unwrap();

    let mut lowered = lower_entry_with_options(
        root.join("main.yu"),
        SourceOptions {
            std_root: Some(root.join("std")),
            implicit_prelude: true,
            search_paths: Vec::new(),
        },
    )
    .unwrap();
    let rendered = render_compact_results(&mut lowered.state);
    let x = rendered
        .iter()
        .find(|(name, _)| name == "x")
        .expect("x should be rendered");

    assert_eq!(x.1, "bool");

    let _ = fs::remove_dir_all(root);
}

#[test]
fn lowers_mixed_float_comparison_syntax_from_implicit_prelude() {
    let root = temp_root("tir-implicit-mixed-float-comparison");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("std")).unwrap();
    fs::write(root.join("main.yu"), "my x = 1.0 <= 2\n").unwrap();
    fs::write(
        root.join("std").join("prelude.yu"),
        include_str!("../../../../lib/std/prelude.yu"),
    )
    .unwrap();

    let mut lowered = lower_entry_with_options(
        root.join("main.yu"),
        SourceOptions {
            std_root: Some(root.join("std")),
            implicit_prelude: true,
            search_paths: Vec::new(),
        },
    )
    .unwrap();
    let rendered = render_compact_results(&mut lowered.state);
    let x = rendered
        .iter()
        .find(|(name, _)| name == "x")
        .expect("x should be rendered");

    assert_eq!(x.1, "bool");

    let _ = fs::remove_dir_all(root);
}

#[test]
fn lowers_expansive_role_binding_to_concrete_result_from_source_loader() {
    let root = temp_root("tir-expansive-role-defaulting");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("std")).unwrap();
    fs::write(root.join("main.yu"), "my f() = Add::add 1 1\n").unwrap();
    fs::write(
        root.join("std").join("prelude.yu"),
        include_str!("../../../../lib/std/prelude.yu"),
    )
    .unwrap();

    let mut lowered = lower_entry_with_options(
        root.join("main.yu"),
        SourceOptions {
            std_root: Some(root.join("std")),
            implicit_prelude: true,
            search_paths: Vec::new(),
        },
    )
    .unwrap();
    let rendered = render_compact_results(&mut lowered.state);
    let f = rendered
        .iter()
        .find(|(name, _)| name == "f")
        .expect("f should be rendered");

    assert_eq!(f.1, "unit -> int");

    let _ = fs::remove_dir_all(root);
}

#[test]
fn lowers_mixed_expansive_role_binding_to_float_from_source_loader() {
    let root = temp_root("tir-expansive-role-defaulting-mixed-float");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("std")).unwrap();
    fs::write(root.join("main.yu"), "my f() = Add::add 1.0 2\n").unwrap();
    fs::write(
        root.join("std").join("prelude.yu"),
        include_str!("../../../../lib/std/prelude.yu"),
    )
    .unwrap();

    let mut lowered = lower_entry_with_options(
        root.join("main.yu"),
        SourceOptions {
            std_root: Some(root.join("std")),
            implicit_prelude: true,
            search_paths: Vec::new(),
        },
    )
    .unwrap();
    let rendered = render_compact_results(&mut lowered.state);
    let f = rendered
        .iter()
        .find(|(name, _)| name == "f")
        .expect("f should be rendered");

    assert_eq!(f.1, "unit -> float");

    let _ = fs::remove_dir_all(root);
}

#[test]
fn lowers_prelude_arithmetic_helper_to_simplified_role_scheme_from_source_loader() {
    let root = temp_root("tir-prelude-arith-helper-simplify");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("std")).unwrap();
    fs::write(root.join("main.yu"), "my plus1 x = x + 1\n").unwrap();
    fs::write(
        root.join("std").join("prelude.yu"),
        include_str!("../../../../lib/std/prelude.yu"),
    )
    .unwrap();

    let mut lowered = lower_entry_with_options(
        root.join("main.yu"),
        SourceOptions {
            std_root: Some(root.join("std")),
            implicit_prelude: true,
            search_paths: Vec::new(),
        },
    )
    .unwrap();
    let rendered = render_compact_results(&mut lowered.state);
    let plus1 = rendered
        .iter()
        .find(|(name, _)| name == "plus1")
        .expect("plus1 should be rendered");

    assert_eq!(plus1.1, "Add<int | α> => α -> α | int");

    let _ = fs::remove_dir_all(root);
}

#[test]
fn effect_operations_stay_frozen_across_source_set_lowering() {
    let root = temp_root("tir-frozen-effect-op");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("std")).unwrap();
    fs::write(root.join("main.yu"), "my y = id 1\n").unwrap();
    fs::write(
        root.join("std").join("prelude.yu"),
        "pub use std::var::*\npub id x = x\n",
    )
    .unwrap();
    fs::write(
        root.join("std").join("var.yu"),
        "act ref_update 'a:\n  our update: 'a -> 'a\n\n\
         type ref 'e 'a with:\n  struct self:\n    get: () -> ['e] 'a\n    update_effect: () -> [ref_update 'a; 'e] ()\n  our r.update f =\n    my loop(x: [_] _) = catch x:\n      ref_update::update v, k -> loop(k f(v))\n    loop((r.update_effect)())\n\n\
         act var 't:\n  our get: () -> 't\n  our set: 't -> ()\n",
    )
    .unwrap();

    let lowered = lower_entry_with_options(
        root.join("main.yu"),
        SourceOptions {
            std_root: Some(root.join("std")),
            implicit_prelude: true,
            search_paths: Vec::new(),
        },
    )
    .unwrap();
    let rendered = crate::display::dump::collect_compact_results_for_paths(
        &lowered.state,
        &lowered.state.ctx.collect_all_binding_paths(),
    );
    let update = rendered
        .iter()
        .find(|(name, _)| name.ends_with("ref_update::update"))
        .expect("ref_update::update should be rendered");

    assert_eq!(update.1, "α -> [std::var::ref_update<α>] α");

    let _ = fs::remove_dir_all(root);
}

#[test]
fn lowers_virtual_entry_with_local_operator_module() {
    let root = temp_root("tir-virtual-operator-syntax");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("ops.yu"),
        "pub infix (%%) 50 51 = \\x -> \\y -> x\n",
    )
    .unwrap();

    let mut lowered = lower_virtual_source_with_options(
        "mod ops\nuse ops::*\nmy y = 1 %% true\n",
        Some(root.clone()),
        SourceOptions {
            std_root: None,
            implicit_prelude: false,
            search_paths: Vec::new(),
        },
    )
    .unwrap();
    let rendered = render_compact_results(&mut lowered.state);
    let y = rendered
        .iter()
        .find(|(name, _)| name == "y")
        .expect("y should be rendered");

    assert_eq!(y.1, "int");

    let _ = fs::remove_dir_all(root);
}

#[test]
fn lowers_var_sigils_across_multiple_top_level_bindings() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my read_var =\n  my ($x, y) = (12, 13)\n  $x\n\n\
             my read_plain =\n  my ($x, y) = (12, 13)\n  y\n\n\
             my read_pair =\n  my ($x, $y) = (12, 13)\n  ($x, $y)\n\n\
             my assign_var =\n  my ($x) = 1\n  &x = 2\n  $x\n\n\
             my assign_pair =\n  my ($x, $y) = (1, 2)\n  &x = $y\n  $x\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);

        assert_eq!(
            rendered
                .iter()
                .find(|(name, _)| name == "read_var")
                .expect("read_var should be rendered")
                .1,
            "int",
        );
        assert_eq!(
            rendered
                .iter()
                .find(|(name, _)| name == "read_plain")
                .expect("read_plain should be rendered")
                .1,
            "int",
        );
        assert_eq!(
            rendered
                .iter()
                .find(|(name, _)| name == "read_pair")
                .expect("read_pair should be rendered")
                .1,
            "(int, int)",
        );
        assert_eq!(
            rendered
                .iter()
                .find(|(name, _)| name == "assign_var")
                .expect("assign_var should be rendered")
                .1,
            "int",
        );
        assert_eq!(
            rendered
                .iter()
                .find(|(name, _)| name == "assign_pair")
                .expect("assign_pair should be rendered")
                .1,
            "int",
        );
    });
}

#[test]
fn lowers_var_sigils_through_top_level_alias_chain() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my read_var =\n  my ($x, y) = (12, 13)\n  $x\n\n\
             my alias_read = read_var\n\
             my alias_read2 = alias_read\n\
             my alias_pair = (read_var, alias_read2)\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);

        assert_eq!(
            rendered
                .iter()
                .find(|(name, _)| name == "alias_read")
                .expect("alias_read should be rendered")
                .1,
            "int",
        );
        assert_eq!(
            rendered
                .iter()
                .find(|(name, _)| name == "alias_read2")
                .expect("alias_read2 should be rendered")
                .1,
            "int",
        );
        assert_eq!(
            rendered
                .iter()
                .find(|(name, _)| name == "alias_pair")
                .expect("alias_pair should be rendered")
                .1,
            "(int, int)",
        );
    });
}

#[test]
fn lowers_ref_receiver_methods_separately_from_value_methods() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my push_ref =\n  my ($xs) = [1, 2]\n  &xs.push 3\n  $xs\n\n\
             my append_value(xs: list int) = xs.append [3]\n\n\
             push_ref\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let exported = crate::export::export_principal_bindings(&mut lowered.state);
        let push_ref_body = exported
            .iter()
            .find(|binding| {
                binding
                    .name
                    .segments
                    .last()
                    .is_some_and(|name| name.0 == "push_ref")
            })
            .map(|binding| format!("{:?}", binding.body))
            .expect("push_ref should be exported");
        assert!(
            push_ref_body.contains("#ref-method:push"),
            "ref receiver selection should call the hidden ref-method, got {push_ref_body}",
        );
        let rendered = render_compact_results(&mut lowered.state);

        assert_eq!(
            rendered_type(&rendered, "append_value"),
            "std::list::list<int> -> std::list::list<int>",
        );
    });
}

#[test]
fn lowers_ref_field_projection_as_child_ref_update() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "struct point { x: int, y: int }\n\
             my move_x =\n  my ($p) = point { x: 1, y: 2 }\n  &p.x = 3\n  $p.x\n\n\
             move_x\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let exported = crate::export::export_principal_bindings(&mut lowered.state);
        let move_x_body = exported
            .iter()
            .find(|binding| {
                binding
                    .name
                    .segments
                    .last()
                    .is_some_and(|name| name.0 == "move_x")
            })
            .map(|binding| format!("{:?}", binding.body))
            .expect("move_x should be exported");
        assert!(
            move_x_body.contains("__ref_field_parent"),
            "ref field projection should allocate a child ref, got {move_x_body}",
        );
        assert!(
            move_x_body.contains("Name(\"ref_update\")")
                && move_x_body.contains("Name(\"update\")"),
            "child ref update should emit ref_update::update inside parent update, got {move_x_body}",
        );
        assert!(
            move_x_body.contains("Name(\"y\")") && move_x_body.contains("Name(\"__ref_field_old"),
            "non-target fields should be copied from the old parent value, got {move_x_body}",
        );
        let rendered = render_compact_results(&mut lowered.state);

        assert_eq!(rendered_type(&rendered, "move_x"), "int");
    });
}

#[test]
fn ref_methods_shadow_synthetic_ref_field_projection() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "struct point { x: int, y: int } with:\n  our &p.x = 99\n\
             my ref_x =\n  my ($p) = point { x: 1, y: 2 }\n  &p.x\n\n\
             ref_x\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let exported = crate::export::export_principal_bindings(&mut lowered.state);
        let ref_x_body = exported
            .iter()
            .find(|binding| {
                binding
                    .name
                    .segments
                    .last()
                    .is_some_and(|name| name.0 == "ref_x")
            })
            .map(|binding| format!("{:?}", binding.body))
            .expect("ref_x should be exported");
        assert!(
            ref_x_body.contains("#ref-method:x"),
            "explicit ref method should be selected, got {ref_x_body}",
        );
        assert!(
            !ref_x_body.contains("__ref_field_parent"),
            "explicit ref methods must shadow synthetic field refs, got {ref_x_body}",
        );
        let rendered = render_compact_results(&mut lowered.state);

        assert_eq!(rendered_type(&rendered, "ref_x"), "int");
    });
}

#[test]
fn lowers_std_var_ref_inside_nested_act_module() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my make_ref = var::var_ref\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        let make_ref = rendered
            .iter()
            .find(|(name, _)| name == "make_ref")
            .expect("make_ref should be rendered");

        assert_eq!(make_ref.1, "unit -> std::var::ref<[std::var::var<α>;], α>");
    });
}

#[test]
fn lowers_std_var_ref_through_top_level_alias() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my make_ref = var::var_ref\nmy make_ref2 = make_ref\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);

        assert_eq!(
            rendered
                .iter()
                .find(|(name, _)| name == "make_ref")
                .expect("make_ref should be rendered")
                .1,
            "unit -> std::var::ref<[std::var::var<α>;], α>",
        );
        assert_eq!(
            rendered
                .iter()
                .find(|(name, _)| name == "make_ref2")
                .expect("make_ref2 should be rendered")
                .1,
            "unit -> std::var::ref<[std::var::var<α>;], α>",
        );
    });
}

#[test]
fn lowers_record_head_spread_literal() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my head_spread v = { ..v, a: 1 }\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        let ty = &rendered
            .iter()
            .find(|(name, _)| name == "head_spread")
            .expect("head_spread should be rendered")
            .1;

        assert!(
            ty.contains(".."),
            "head spread type should keep spread form: {ty}"
        );
        assert!(
            ty.contains("a:"),
            "head spread type should mention local field: {ty}"
        );
        assert!(
            ty.find("..")
                .is_some_and(|spread| ty.find("a:").is_some_and(|field| spread < field)),
            "head spread should render tail before local fields: {ty}",
        );
    });
}

#[test]
fn lowers_record_tail_spread_literal() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my tail_spread v = { a: 1, ..v }\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        let ty = &rendered
            .iter()
            .find(|(name, _)| name == "tail_spread")
            .expect("tail_spread should be rendered")
            .1;

        assert!(
            ty.contains(".."),
            "tail spread type should keep spread form: {ty}"
        );
        assert!(
            ty.contains("a:"),
            "tail spread type should mention local field: {ty}"
        );
        assert!(
            ty.find("a:")
                .is_some_and(|field| ty.find("..").is_some_and(|spread| field < spread)),
            "tail spread should render local fields before tail: {ty}",
        );
    });
}

#[test]
fn lowers_record_pattern_defaults_in_header_args() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my f { width = 1, height = 1 } = (width, height)\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        let ty = &rendered
            .iter()
            .find(|(name, _)| name == "f")
            .expect("f should be rendered")
            .1;

        assert!(
            ty.contains("width?: α"),
            "default field should stay optional and polymorphic when present: {ty}"
        );
        assert!(
            ty.contains("height?: β"),
            "default field should stay optional and polymorphic when present: {ty}"
        );
        assert!(
            ty.contains("-> (α | int, β | int)"),
            "defaulted fields should preserve present-branch vars and missing-branch defaults: {ty}",
        );
    });
}

#[test]
fn lowers_record_pattern_defaults_in_case_arms() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my f x = case x:\n  { width = 1 } -> width\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        let ty = &rendered
            .iter()
            .find(|(name, _)| name == "f")
            .expect("f should be rendered")
            .1;

        assert!(
            ty.contains("width?: α"),
            "case arm pattern should make field optional: {ty}"
        );
        assert!(
            ty.contains("α | int"),
            "case arm pattern should include default branch in result: {ty}"
        );
    });
}

#[test]
fn lowers_record_pattern_defaults_in_catch_value_arms() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my f x = catch x:\n  { width = 1 } -> width\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        let ty = &rendered
            .iter()
            .find(|(name, _)| name == "f")
            .expect("f should be rendered")
            .1;

        assert!(
            ty.contains("width?:"),
            "catch value arm pattern should make field optional: {ty}"
        );
        assert!(
            ty.contains("| int"),
            "catch value arm pattern should include default branch in result: {ty}"
        );
    });
}

#[test]
fn lowers_record_pattern_defaults_in_catch_effect_payloads() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "act cfg:\n  our read: { width: int } -> int\n\nmy f x = catch x:\n  cfg::read { width = 1 }, k -> width\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);

        assert_eq!(
            rendered
                .iter()
                .find(|(name, _)| name == "cfg::read")
                .expect("cfg::read should be rendered")
                .1,
            "{width: int} -> [cfg] int",
        );
        assert_eq!(
            rendered
                .iter()
                .find(|(name, _)| name == "f")
                .expect("f should be rendered")
                .1,
            "α -> α | int",
        );
    });
}

#[test]
fn lowers_record_pattern_defaults_in_case_guards() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my f x = case x:\n  { flag = true } if flag -> 1\n  _ -> 0\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        let ty = &rendered
            .iter()
            .find(|(name, _)| name == "f")
            .expect("f should be rendered")
            .1;

        assert!(
            ty.contains("flag?: bool"),
            "case guard should see defaulted pattern local: {ty}"
        );
        assert!(
            ty.ends_with("-> int"),
            "case guard example should still return int: {ty}"
        );
    });
}

#[test]
fn lowers_record_pattern_defaults_in_catch_effect_guards() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "act cfg:\n  our read: { flag: bool } -> int\n\nmy f x = catch x:\n  cfg::read { flag = true }, k if flag -> 1\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        let ty = &rendered
            .iter()
            .find(|(name, _)| name == "f")
            .expect("f should be rendered")
            .1;

        assert_eq!(ty, "α -> α | int");
    });
}

#[test]
fn lowers_record_pattern_default_source() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            PAT_RECORD_DEFAULT_SOURCE,
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);

        assert_eq!(
            rendered_type(&rendered, "cfg::read"),
            "{flag: bool, width: int} -> [cfg] int",
        );
        assert_eq!(
            rendered_type(&rendered, "header_sum"),
            "{width?: α, height?: β} -> (α | int, β | int)",
        );
        assert_eq!(rendered_type(&rendered, "named_header"), "{width: α} -> α");
        assert_eq!(
            rendered_type(&rendered, "named_default_header"),
            "{width?: α} -> α | int",
        );
        assert_eq!(
            rendered_type(&rendered, "named_mix"),
            "{width?: α, height: β} -> (α | int, β)",
        );
        assert_eq!(
            rendered_type(&rendered, "nested_header"),
            "{size: {width?: α, height: β}} -> (α | int, β)",
        );
        assert_eq!(
            rendered_type(&rendered, "nested_named"),
            "{cfg: {width?: α}} -> α | int",
        );
        assert_eq!(
            rendered_type(&rendered, "case_width"),
            "{width?: α} -> α | int",
        );
        assert_eq!(
            rendered_type(&rendered, "case_nested"),
            "{size: {width?: α, height: β}} -> (α | int, β)",
        );
        assert_eq!(
            rendered_type(&rendered, "case_guard"),
            "{flag?: bool, width?: α} -> α | int",
        );
        assert_eq!(
            rendered_type(&rendered, "catch_value"),
            "{width?: α} -> α | int",
        );
        assert_eq!(
            rendered_type(&rendered, "catch_nested_value"),
            "{size: {width?: α, height: β}} -> (α | int, β)",
        );
        assert_eq!(rendered_type(&rendered, "catch_read"), "α -> α | int");
        assert_eq!(rendered_type(&rendered, "catch_read_guard"), "α -> α | int",);
    });
}

#[test]
fn lowers_record_pattern_spread_source() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            PAT_RECORD_SPREAD_SOURCE,
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);

        assert_eq!(
            rendered_type(&rendered, "head_width"),
            "{width?: α} -> α | int"
        );
        assert_eq!(
            rendered_type(&rendered, "tail_width"),
            "{width?: α} -> α | int"
        );
        assert_eq!(
            rendered_type(&rendered, "head_rest"),
            "(α & {width?: ⊤}) -> α",
        );
        assert_eq!(
            rendered_type(&rendered, "tail_rest"),
            "(α & {width?: ⊤}) -> α",
        );
        assert_eq!(
            rendered_type(&rendered, "case_head"),
            "{width?: α} -> α | int"
        );
        assert_eq!(
            rendered_type(&rendered, "case_tail"),
            "{width?: α} -> α | int"
        );
    });
}

#[test]
fn lowers_role_overlap_source() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            ROLE_OVERLAP_SOURCE,
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        lowered.state.finalize_compact_results();
        let rendered = render_compact_results(&mut lowered.state);
        let errors = lowered.state.infer.type_errors();

        assert_eq!(rendered_type(&rendered, "concrete_wins"), "std::str::str");
        assert!(
            rendered_type(&rendered, "generic_wins").contains("std::str::str"),
            "generic overlap fixture should resolve to std::str::str, got {}",
            rendered_type(&rendered, "generic_wins"),
        );
        assert!(
            errors.iter().any(|error| matches!(
                &error.kind,
                crate::diagnostic::TypeErrorKind::AmbiguousImpl {
                    role,
                    candidates,
                    previews,
                    ..
                } if role == "Fetch"
                    && *candidates == 2
                    && previews.len() == 2
            )),
            "overlap fixture should surface ambiguous Fetch impl, got {errors:?}",
        );
    });
}

#[test]
fn source_loader_surfaces_missing_impl_for_concrete_role_constraint() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "role Unshown 'a:\n  our a.unshown: string\n\nmy shown = 1.unshown\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        lowered.state.finalize_compact_results();
        let errors = lowered.state.infer.type_errors();

        assert!(
            errors.iter().any(|error| matches!(
                &error.kind,
                crate::diagnostic::TypeErrorKind::MissingImpl { role, args }
                    if role == "Unshown" && args == &vec!["int".to_string()]
            )),
            "expected missing impl error from source loader path, got {errors:?}",
        );
    });
}

#[test]
fn source_loader_surfaces_missing_impl_for_concrete_multi_arg_role_constraint() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "role Index 'container 'key:\n  type value\n  our container.index: 'key -> value\n\n\
             my shown: string = 1.index true\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        lowered.state.finalize_compact_results();
        let errors = lowered.state.infer.type_errors();

        assert!(
            errors.iter().any(|error| matches!(
                &error.kind,
                crate::diagnostic::TypeErrorKind::MissingImpl { role, args }
                    if role == "Index"
                        && args == &vec![
                            "int".to_string(),
                            "bool".to_string(),
                            "value = std::str::str".to_string(),
                        ]
            )),
            "expected missing multi-arg impl error from source loader path, got {errors:?}",
        );
    });
}

#[test]
fn lowers_enum_constructor_and_annotated_case_from_source_loader() {
    let mut lowered = lower_virtual_source_with_options(
        "enum opt 'a = nil | just 'a\n\
         my value: opt int = opt::just 1\n\
         my picked: int = case value:\n\
           opt::nil -> 2\n\
           opt::just y -> y\n",
        Some(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")),
        SourceOptions::default(),
    )
    .unwrap();
    let rendered = render_compact_results(&mut lowered.state);

    assert_eq!(rendered_type(&rendered, "value"), "opt<int>");
    assert_eq!(rendered_type(&rendered, "picked"), "int");
    assert_eq!(rendered_type(&rendered, "opt::just"), "α -> opt<α>");
    assert_eq!(rendered_type(&rendered, "opt::nil"), "opt<α>");
}

#[test]
fn lowers_std_opt_constructors_through_implicit_prelude() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my value: opt int = just 1\n\
             my picked: int = case value:\n\
               nil -> 2\n\
               just y -> y\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);

        assert_eq!(rendered_type(&rendered, "value"), "std::opt::opt<int>");
        assert_eq!(rendered_type(&rendered, "picked"), "int");
    });
}

#[test]
fn lowers_opt_if_join_to_single_concrete_payload_shape() {
    let mut lowered = lower_virtual_source_with_options(
        "enum opt 'a = nil | just 'a\n\
         my nil_pair: opt (int, int) = opt::nil\n\
         my x = if true { nil_pair } else { opt::just (1, 2) }\n",
        Some(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")),
        SourceOptions::default(),
    )
    .unwrap();
    let rendered = render_compact_results(&mut lowered.state);

    assert_eq!(rendered_type(&rendered, "x"), "opt<(int, int)>");
}

#[test]
fn lowers_opt_if_join_without_annotation_keeps_open_payload_interval() {
    let mut lowered = lower_virtual_source_with_options(
        "enum opt 'a = nil | just 'a\n\
         my nil_pair = opt::nil\n\
         my x = if true { nil_pair } else { opt::just (1, 2) }\n",
        Some(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")),
        SourceOptions::default(),
    )
    .unwrap();
    let rendered = render_compact_results(&mut lowered.state);

    assert_eq!(rendered_type(&rendered, "nil_pair"), "opt<α>");
    assert_eq!(rendered_type(&rendered, "x"), "opt<(int, int) | α>");
}

#[test]
fn compact_scheme_collapses_shared_center_to_single_payload_shape() {
    let mut lowered = lower_virtual_source_with_options(
        "enum opt 'a = nil | just 'a\n\
         my nil_pair: opt (int, int) = opt::nil\n\
         my x = if true { nil_pair } else { opt::just (1, 2) }\n",
        Some(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")),
        SourceOptions::default(),
    )
    .unwrap();
    lowered.state.finalize_compact_results();
    let x_def = lowered
        .state
        .ctx
        .resolve_value(&Name("x".to_string()))
        .expect("x should resolve");
    let scheme = lowered
        .state
        .compact_scheme_of(x_def)
        .expect("x should have a compact scheme");

    assert_eq!(
        crate::display::format::format_coalesced_scheme(&scheme),
        "opt<(int, int)>"
    );
}

#[test]
fn lowers_std_list_helpers_through_implicit_prelude() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my take_is_empty(xs: list int) = is_empty xs\n\
             my take_uncons(xs: list int) = uncons xs\n\
             my take_first(xs: list int) = first xs\n\
             my take_last(xs: list int) = last xs\n\
             my take_rev(xs: list int) = rev xs\n\
             my take_index(xs: list int) = xs.index 0\n\
             my take_index_bracket(xs: list int) = xs[0]\n\
             my take_map(xs: list int, f: int -> int) = map xs f\n\
             my take_filter(xs: list int, pred: int -> bool) = filter xs pred\n\
             my take_fold(xs: list int, z: int, f: int -> int -> int) = fold xs z f\n\
             my append_self(xs: list int) = append xs xs\n\
             my append_method_self(xs: list int) = xs.append xs\n\
             my append_qualified_method_self(xs: list int) = xs.std::list::append xs\n\
             my splice_self(xs: list int, ys: list int) = splice xs (range 0 1) ys\n\
             my splice_method_self(xs: list int, ys: list int) = xs.splice (range 0 1) ys\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        assert_eq!(
            rendered_type(&rendered, "take_is_empty"),
            "std::list::list<int> -> bool"
        );
        assert!(rendered_type(&rendered, "take_uncons").contains("std::opt::opt<"));
        assert_eq!(
            rendered_type(&rendered, "take_first"),
            "std::list::list<int> -> std::opt::opt<int>"
        );
        assert_eq!(
            rendered_type(&rendered, "take_last"),
            "std::list::list<int> -> std::opt::opt<int>"
        );
        assert_eq!(
            rendered_type(&rendered, "take_rev"),
            "std::list::list<int> -> std::list::list<int>"
        );
        assert_eq!(
            rendered_type(&rendered, "take_index"),
            "std::list::list<int> -> int"
        );
        assert_eq!(
            rendered_type(&rendered, "take_index_bracket"),
            "std::list::list<int> -> int"
        );
        assert_eq!(
            rendered_type(&rendered, "take_map"),
            "std::list::list<int> -> (int -> int) -> std::list::list<int>"
        );
        assert_eq!(
            rendered_type(&rendered, "take_filter"),
            "std::list::list<int> -> (int -> bool) -> std::list::list<int>"
        );
        assert_eq!(
            rendered_type(&rendered, "take_fold"),
            "std::list::list<int> -> int -> (int -> int -> int) -> int"
        );
        assert_eq!(
            rendered_type(&rendered, "append_self"),
            "std::list::list<int> -> std::list::list<int>"
        );
        assert_eq!(
            rendered_type(&rendered, "append_method_self"),
            "std::list::list<int> -> std::list::list<int>"
        );
        assert_eq!(
            rendered_type(&rendered, "append_qualified_method_self"),
            "std::list::list<int> -> std::list::list<int>"
        );
        assert_eq!(
            rendered_type(&rendered, "splice_self"),
            "std::list::list<int> -> std::list::list<int> -> std::list::list<int>"
        );
        assert_eq!(
            rendered_type(&rendered, "splice_method_self"),
            "std::list::list<int> -> std::list::list<int> -> std::list::list<int>"
        );
    });
}

#[test]
fn lowers_case_over_nominal_list_view_with_apply_in_body() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my probe xs z f = case std::list::view_raw xs:
  std::list::list_view::empty -> z
  std::list::list_view::leaf x -> f(z, x)
  std::list::list_view::node(left, right) -> z
",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        lowered.state.finalize_compact_results();
        let probe_def = lowered
            .state
            .ctx
            .resolve_value(&Name("probe".to_string()))
            .expect("probe should resolve");
        let scheme = lowered
            .state
            .compact_scheme_of(probe_def)
            .expect("probe should have compact scheme");

        assert_eq!(
            crate::display::format::format_coalesced_scheme(&scheme),
            "std::list::list<α> -> (β & γ) -> (β -> [δ] α -> [δ] γ) -> [δ] β | γ"
        );
    });
}

#[test]
fn lowers_std_list_fold_partial_application_with_latent_effects() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my ff = std::list::fold\n\
             my f1 xs = std::list::fold xs\n\
             my f2 xs z = std::list::fold xs z\n\
             my f3 xs z f = std::list::fold xs z f\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        let expected = "std::list::list<α> -> β -> (β -> [γ] α -> [γ] β) -> [γ] β";
        assert_eq!(rendered_type(&rendered, "ff"), expected);
        assert_eq!(rendered_type(&rendered, "f1"), expected);
        assert_eq!(rendered_type(&rendered, "f2"), expected);
        assert_eq!(rendered_type(&rendered, "f3"), expected);
    });
}

#[test]
fn constrained_effectful_function_reference_keeps_effectful_result_var() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "use std::fold::*\n\
             use std::flow::*\n\
             use std::list::*\n\
             use std::undet::*\n\
             my eachish xs = sub::sub {\n\
                 xs.fold () (\\() x -> if undet::branch() { sub::return x } else ())\n\
                 undet::fail()\n\
             }\n\
             my e = eachish\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        lowered.state.finalize_compact_results();
        let eachish_def = lowered
            .state
            .ctx
            .resolve_value(&Name("eachish".to_string()))
            .expect("eachish should resolve");
        let e_def = lowered
            .state
            .ctx
            .resolve_value(&Name("e".to_string()))
            .expect("e should resolve");
        let eachish_scheme = lowered
            .state
            .compact_scheme_of(eachish_def)
            .expect("eachish should have compact scheme");
        let e_scheme = lowered
            .state
            .compact_scheme_of(e_def)
            .expect("e should have compact scheme");
        assert_eq!(
            crate::display::format::format_coalesced_scheme(&eachish_scheme),
            "α -> [std::undet::undet] β"
        );
        assert_eq!(
            crate::display::format::format_coalesced_scheme(&e_scheme),
            "α -> [std::undet::undet] β"
        );
    });
}

#[test]
fn lowers_unit_literal_and_never_join_through_sub_to_unit() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "use std::flow::*\n\
             my x = ()\n\
             my f x = if true { sub::return x } else { () }\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        assert_eq!(rendered_type(&rendered, "x"), "unit");
        assert_eq!(
            rendered_type(&rendered, "f"),
            "α -> [std::flow::sub<α>] unit"
        );
    });
}

#[test]
fn undet_each_reference_keeps_fold_item_result_var() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "use std::undet::*\n\
             my e = undet::each\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        assert_eq!(
            rendered_type(&rendered, "e"),
            "Fold<α, item = β> => α -> [std::undet::undet] β"
        );
    });
}

#[test]
fn undet_list_reference_keeps_handled_input_effect_requirement() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "use std::undet::*\n\
             my l = undet::list\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        assert_eq!(
            rendered_type(&rendered, "l"),
            "α [std::undet::undet; β] -> [β] std::list::list<α>"
        );
    });
}

#[test]
fn effect_method_list_selection_uses_receiver_effect_row() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "use std::undet::*\n\
             my collect(x: [undet; _] _) = x.list\n\
             my collected = (each [1, 2, 3] + each [4, 5, 6]).list\n\
             my logic_value = (each [1, 2, 3] + each [4, 5, 6]).logic\n\
             my once_value = (each [1, 2, 3] + each [4, 5, 6]).once\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        assert_eq!(
            rendered_type(&rendered, "collect"),
            "α [std::undet::undet; β] -> [β] std::list::list<α>"
        );
        assert_eq!(
            rendered_type(&rendered, "collected"),
            "std::list::list<int>"
        );
        assert_eq!(
            rendered_type(&rendered, "logic_value"),
            "std::list::list<int>"
        );
        assert_eq!(rendered_type(&rendered, "once_value"), "std::opt::opt<int>");
    });
}

#[test]
fn duplicate_effect_method_names_are_ambiguous_when_both_effects_are_present() {
    run_with_large_stack(|| {
        let mut lowered = lower_virtual_source_with_options(
            concat!(
                "act a:\n",
                "  our op: () -> ()\n",
                "  pub (x: [_] _).pick = x\n",
                "act b:\n",
                "  our op: () -> ()\n",
                "  pub (x: [_] _).pick = x\n",
                "my choose(x: [a; _] int) = {\n",
                "  b::op()\n",
                "  x\n",
                "}.pick\n",
            ),
            Some(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")),
            SourceOptions::default(),
        )
        .unwrap();
        lowered.state.finalize_compact_results();
        let errors = lowered.state.infer.type_errors();

        assert!(
            errors.iter().any(|error| matches!(
                &error.kind,
                crate::diagnostic::TypeErrorKind::AmbiguousEffectMethod { method, effects }
                    if method == "pick"
                        && effects.contains(&"a".to_string())
                        && effects.contains(&"b".to_string())
            )),
            "expected ambiguous effect method error, got {errors:?}",
        );
    });
}

#[test]
fn lowers_junction_effect_in_if_conditions() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my f(x: [junction] bool) = if x { 1 } else { 0 }\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        assert_eq!(
            rendered_type(&rendered, "f"),
            "bool [std::junction::junction; α] -> [α] int"
        );
    });
}

#[test]
fn lowers_junction_helper_application() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my f(x: [junction] bool) = junction::junction x\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        assert_eq!(
            rendered_type(&rendered, "f"),
            "bool [std::junction::junction; α] -> [α] bool"
        );
    });
}

#[test]
fn lowers_junction_quantifiers_over_list_fold_from_prelude() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my q = if all [1, 2, 3] < any [2, 3, 4] { 1 } else { 0 }\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        assert_eq!(rendered_type(&rendered, "q"), "int");
        assert!(
            lowered.state.infer.type_errors().is_empty(),
            "junction quantifier lowering should not leave role errors, got {:?}",
            lowered.state.infer.type_errors(),
        );
    });
}

#[test]
fn lowers_junction_effect_in_case_guards() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my f(x: [junction] bool) = case 1:\n  1 if x -> 1\n  _ -> 0\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        assert_eq!(
            rendered_type(&rendered, "f"),
            "bool [std::junction::junction; α] -> [α] int"
        );
    });
}

#[test]
fn lowers_plain_bool_if_conditions() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my f(x: bool) = if x { 1 } else { 0 }",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        assert_eq!(rendered_type(&rendered, "f"), "bool -> int");
    });
}

#[test]
fn lowers_plain_bool_case_guards() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my f(x: bool) = case 1:\n  1 if x -> 1\n  _ -> 0\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        assert_eq!(rendered_type(&rendered, "f"), "bool -> int");
    });
}

#[test]
fn lowers_constant_case_guards() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my f = case 1:\n  1 if true -> 1\n  _ -> 0\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let f_def = lowered
            .state
            .ctx
            .collect_all_binding_paths()
            .into_iter()
            .find_map(|(path, def)| {
                (path.segments.len() == 1 && path.segments[0].0 == "f").then_some(def)
            })
            .expect("f def");
        let body = lowered.state.principal_bodies.get(&f_def).expect("f body");
        match &body.kind {
            crate::ast::expr::ExprKind::Match(_, arms) => {
                assert_eq!(arms.len(), 2);
                assert!(matches!(
                    arms[0].body.kind,
                    crate::ast::expr::ExprKind::Lit(crate::ast::expr::Lit::Int(1))
                ));
                assert!(matches!(
                    arms[1].body.kind,
                    crate::ast::expr::ExprKind::Lit(crate::ast::expr::Lit::Int(0))
                ));
            }
            other => panic!("expected match body, got {other:?}"),
        }
        let rendered = render_compact_results(&mut lowered.state);
        assert_eq!(rendered_type(&rendered, "f"), "int");
    });
}

#[test]
fn lowers_junction_effect_in_catch_guards() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my f(x: [junction] bool) = catch 1:\n  n if x -> n\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        assert_eq!(
            rendered_type(&rendered, "f"),
            "bool [std::junction::junction; α] -> [α] int"
        );
    });
}

#[test]
fn lowers_plain_bool_catch_guards() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my f(x: bool) = catch 1:\n  n if x -> n\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        assert_eq!(rendered_type(&rendered, "f"), "bool -> int");
    });
}

#[test]
fn lowers_string_role_impls_from_implicit_prelude() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my joined = \"yu\" + \"lang\"\n\
             my shown = \"%{joined}\"\n\
             my size = \"abc\".len\n\
             my first = \"abc\"[0]\n\
             my slice = \"abc\"[0..1]\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        lowered.state.finalize_compact_results();
        assert!(
            lowered.state.infer.type_errors().is_empty(),
            "string role impls should resolve without errors, got {:?}",
            lowered.state.infer.type_errors(),
        );
        let rendered = render_compact_results(&mut lowered.state);
        assert_eq!(rendered_type(&rendered, "joined"), "std::str::str");
        assert_eq!(rendered_type(&rendered, "shown"), "std::str::str");
        assert_eq!(rendered_type(&rendered, "size"), "int");
        assert_eq!(rendered_type(&rendered, "first"), "std::str::str");
        assert_eq!(rendered_type(&rendered, "slice"), "std::str::str");
    });
}

#[test]
fn registers_list_add_impl_from_implicit_prelude() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my f(xs: list _, ys: list _) = xs + ys\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let add = crate::symbols::Path {
            segments: vec![
                crate::symbols::Name("std".to_string()),
                crate::symbols::Name("prelude".to_string()),
                crate::symbols::Name("Add".to_string()),
            ],
        };
        let candidates = lowered.state.infer.role_impl_candidates_of(&add);
        let role_method_add_role = lowered
            .state
            .infer
            .role_methods
            .get(&crate::symbols::Name("add".to_string()))
            .map(|info| info.role.clone());
        assert_eq!(role_method_add_role, Some(add.clone()));
        let binding_paths = lowered
            .state
            .ctx
            .collect_all_binding_paths()
            .into_iter()
            .collect::<Vec<_>>();
        let list_add = candidates
            .iter()
            .find_map(|candidate| {
                candidate
                    .args
                    .iter()
                    .any(|arg| arg.contains("list"))
                    .then(|| {
                        candidate
                            .member_defs
                            .get(&crate::symbols::Name("add".to_string()))
                    })
                    .flatten()
            })
            .copied();
        assert!(
            list_add.is_some_and(
                |def| binding_paths.iter().any(|(_, path_def)| path_def == &def)
                    && lowered.state.principal_bodies.contains_key(&def)
            ),
            "expected Add list candidate with add member, got {:?}",
            list_add.map(|def| {
                (
                    def,
                    binding_paths
                        .iter()
                        .find(|(_, path_def)| path_def == &def)
                        .map(|(path, _)| path.clone()),
                    lowered.state.principal_bodies.contains_key(&def),
                )
            })
        );
        let program = crate::export_core_program(&mut lowered.state);
        let list_add_def = list_add.expect("list add def");
        let list_add_path = binding_paths
            .iter()
            .find_map(|(path, def)| (def == &list_add_def).then_some(path.clone()))
            .expect("list add path");
        assert!(
            program
                .program
                .bindings
                .iter()
                .any(|binding| binding.name
                    == super::super::export::names::export_path(&list_add_path)),
            "expected exported role support add binding, got {:?}",
            program
                .program
                .bindings
                .iter()
                .map(|binding| binding.name.clone())
                .collect::<Vec<_>>()
        );
    });
}

#[test]
fn lowers_qualified_std_str_impl_head_to_same_candidate_shape() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "use std::str::*\n\
             role Echo 'a:\n  our a.echo: 'a\n\n\
             impl Echo std::str::str:\n  our x.echo = x\n\n\
             my echoed = \"ok\".echo\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        lowered.state.finalize_compact_results();
        assert!(
            lowered.state.infer.type_errors().is_empty(),
            "qualified std::str::str impl head should resolve, got {:?}",
            lowered.state.infer.type_errors(),
        );
        let rendered = render_compact_results(&mut lowered.state);
        assert_eq!(rendered_type(&rendered, "echoed"), "std::str::str");
    });
}

#[test]
fn lowers_short_std_str_impl_head_to_same_candidate_shape() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "use std::str::*\n\
             role EchoShort 'a:\n  our a.echo_short: 'a\n\n\
             impl EchoShort str:\n  our x.echo_short = x\n\n\
             my echoed = \"ok\".echo_short\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        lowered.state.finalize_compact_results();
        assert!(
            lowered.state.infer.type_errors().is_empty(),
            "short str impl head should resolve through use std::str::*, got {:?}",
            lowered.state.infer.type_errors(),
        );
        let rendered = render_compact_results(&mut lowered.state);
        assert_eq!(rendered_type(&rendered, "echoed"), "std::str::str");
    });
}

#[test]
fn private_act_operations_work_inside_public_helpers() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "pub act choice:\n\
              my pick: () -> bool\n\
              pub decide() = catch pick():\n\
                pick(), k -> k true\n\
                b -> b\n\
             my x = choice::decide()\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        lowered.state.finalize_compact_results();
        assert!(
            lowered.state.infer.type_errors().is_empty(),
            "private act op helper should lower without type errors, got {:?}",
            lowered.state.infer.type_errors(),
        );
    });
}

#[test]
fn lowers_unannotated_local_fold_with_latent_effects() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my fold xs z f = case std::list::view_raw xs:\n  std::list::list_view::empty -> z\n  std::list::list_view::leaf x -> f z x\n  std::list::list_view::node (left, right) ->\n    my z2 = fold left z f\n    fold right z2 f\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        assert_eq!(
            rendered_type(&rendered, "fold"),
            "std::list::list<α> -> β -> (β -> [γ] α -> [γ] β) -> [γ] β"
        );
    });
}

#[test]
fn lowers_unannotated_local_fold_with_nested_recursive_argument_application() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my fold xs z f = case std::list::view_raw xs:\n  std::list::list_view::empty -> z\n  std::list::list_view::leaf x -> f z x\n  std::list::list_view::node(left, right) -> fold(right, fold left z f, f)\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        assert_eq!(
            rendered_type(&rendered, "fold"),
            "std::list::list<α> -> β -> (β -> [γ] α -> [γ] β) -> [γ] β"
        );
    });
}

#[test]
fn default_fold_contains_uses_associated_item_type() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "[1, 2, 3, 4].contains 3\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        lowered.state.finalize_compact_results();
        assert!(
            lowered.state.infer.type_errors().is_empty(),
            "Fold.contains should resolve without errors, got {:?}",
            lowered.state.infer.type_errors(),
        );
        let contains_def = lowered
            .state
            .ctx
            .collect_all_binding_paths()
            .into_iter()
            .find_map(|(path, def)| {
                let names = path
                    .segments
                    .iter()
                    .map(|name| name.0.as_str())
                    .collect::<Vec<_>>();
                (names == ["std", "fold", "Fold", "contains"]).then_some(def)
            })
            .expect("Fold.contains def");
        let contains = lowered
            .state
            .runtime_export_schemes
            .get(&contains_def)
            .expect("Fold.contains runtime scheme");
        assert_eq!(
            crate::display::dump::format_runtime_export_scheme(contains),
            "std::fold::Fold<container, item = item> => container -> item -> bool"
        );
    });
}

fn temp_root(name: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    std::env::temp_dir().join(format!("yulang-{name}-{nanos}"))
}

fn rendered_type<'a>(rendered: &'a [(String, String)], name: &str) -> &'a str {
    &rendered
        .iter()
        .find(|(rendered_name, _)| rendered_name == name)
        .unwrap_or_else(|| panic!("{name} should be rendered"))
        .1
}
