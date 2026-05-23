use std::fs;
use std::path::PathBuf;
use std::thread;
use std::time::{SystemTime, UNIX_EPOCH};

use super::*;
use crate::diagnostic::ExpectedEdgeKind;
use crate::display::dump::{collect_expected_edges, render_compact_results};
use crate::types::{Neg, Pos};
use yulang_sources::{InlineSource, SourceOrigin, collect_inline_source_files_with_options};
use yulang_typed_ir::{Name as CoreName, Path as CorePath};

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

fn write_real_std_prelude(root: &std::path::Path) {
    fs::write(
        root.join("std").join("ops.yu"),
        include_str!("../../../../lib/std/ops.yu"),
    )
    .unwrap();
    fs::write(
        root.join("std").join("prelude.yu"),
        include_str!("../../../../lib/std/prelude.yu"),
    )
    .unwrap();
}

fn assert_expected_edge_value_constraint(
    state: &LowerState,
    edge: &crate::diagnostic::ExpectedEdge,
) {
    let expected_lowers = state.infer.lowers_of(edge.expected_tv);
    assert!(
        expected_lowers
            .iter()
            .any(|pos| matches!(pos, Pos::Var(tv) if *tv == edge.actual_tv)),
        "expected edge should add actual as expected lower: {edge:?}, lowers={expected_lowers:?}",
    );

    let actual_uppers = state.infer.uppers_of(edge.actual_tv);
    assert!(
        actual_uppers
            .iter()
            .any(|neg| matches!(neg, Neg::Var(tv) if *tv == edge.expected_tv)),
        "expected edge should add expected as actual upper: {edge:?}, uppers={actual_uppers:?}",
    );
}

#[test]
fn std_lower_cache_preserves_entry_results() {
    let source_set = collect_inline_source_files_with_options(
        "use std::prelude::*\none",
        [InlineSource {
            path: PathBuf::from("<std>/prelude.yu"),
            module_path: CorePath {
                segments: vec![CoreName("std".to_string()), CoreName("prelude".to_string())],
            },
            origin: SourceOrigin::Std,
            source: "pub one = 1\n".to_string(),
            meta: None,
        }],
        SourceOptions {
            std_root: None,
            implicit_prelude: false,
            search_paths: Vec::new(),
        },
    );

    let mut uncached = lower_source_set(&source_set);
    let mut cache = SourceLowerCache::default();
    let mut cached = lower_source_set_with_std_cache(&source_set, &mut cache);
    let snapshot = build_std_infer_snapshot(&source_set).expect("std snapshot");
    let direct_data = build_std_infer_snapshot_data(&source_set).expect("std snapshot data");
    let manifest_json = serde_json::to_string(&snapshot.manifest()).unwrap();
    let manifest: StdInferSnapshotManifest = serde_json::from_str(&manifest_json).unwrap();
    let data_json = serde_json::to_string(snapshot.data()).unwrap();
    let data: StdInferSnapshotData = serde_json::from_str(&data_json).unwrap();
    let mut snapshotted = lower_source_set_with_std_snapshot(&source_set, &snapshot).lowered;

    assert_eq!(manifest.format_version, STD_INFER_SNAPSHOT_FORMAT_VERSION);
    assert_eq!(manifest, snapshot.manifest());
    assert_eq!(&data, snapshot.data());
    assert_eq!(direct_data.manifest, data.manifest);
    data.validate().unwrap();
    direct_data.validate().unwrap();
    assert!(
        data.modules.iter().any(|module| {
            module.path == ["std", "int"] && module.values.iter().any(|value| value.name == "add")
        }),
        "snapshot modules should include std::int::add: {:?}",
        data.modules
    );
    let int_add_symbol = data
        .values
        .iter()
        .find(|symbol| symbol.path == ["std", "int", "add"])
        .map(|symbol| symbol.snapshot_id)
        .expect("std::int::add snapshot symbol");
    let direct_int_add_symbol = direct_data
        .values
        .iter()
        .find(|symbol| symbol.path == ["std", "int", "add"])
        .map(|symbol| symbol.snapshot_id)
        .expect("std::int::add snapshot symbol");
    assert_eq!(int_add_symbol, direct_int_add_symbol);
    assert!(
        direct_data
            .schemes
            .iter()
            .any(|scheme| scheme.symbol == direct_int_add_symbol && scheme.rendered.contains("int")),
        "snapshot schemes should include std::int::add: {:?}",
        direct_data.schemes
    );
    assert!(
        data.values
            .iter()
            .any(|symbol| symbol.path == ["std", "int", "add"]),
        "snapshot values should include primitive std index: {:?}",
        data.values
    );
    assert_eq!(
        crate::render_exported_compact_results(&mut cached.state),
        crate::render_exported_compact_results(&mut uncached.state)
    );
    assert_eq!(
        crate::render_exported_compact_results(&mut snapshotted.state),
        crate::render_exported_compact_results(&mut uncached.state)
    );
    assert_eq!(cached.diagnostic_source, uncached.diagnostic_source);
    assert_eq!(snapshotted.diagnostic_source, uncached.diagnostic_source);
}

#[test]
fn std_snapshot_import_resolves_builtin_paths_and_reports_missing_std_paths() {
    let source_set = collect_inline_source_files_with_options(
        "use std::prelude::*\none",
        [InlineSource {
            path: PathBuf::from("<std>/prelude.yu"),
            module_path: CorePath {
                segments: vec![CoreName("std".to_string()), CoreName("prelude".to_string())],
            },
            origin: SourceOrigin::Std,
            source: "pub my one = 1\n".to_string(),
            meta: None,
        }],
        SourceOptions {
            std_root: None,
            implicit_prelude: false,
            search_paths: Vec::new(),
        },
    );
    let data = build_std_infer_snapshot_data(&source_set).expect("std snapshot data");
    let import = import_std_infer_snapshot_data(&data).expect("snapshot import");

    let int_add = data
        .values
        .iter()
        .find(|symbol| symbol.path == ["std", "int", "add"])
        .expect("std::int::add snapshot symbol");
    assert!(
        import.values[int_add.snapshot_id as usize].is_some(),
        "builtin std::int::add should resolve during partial import"
    );
    assert_eq!(import.coverage.modules_total, data.modules.len());
    assert_eq!(import.coverage.modules_resolved, data.modules.len());
    assert!(import.coverage.values_resolved <= import.coverage.values_total);
    assert_eq!(import.coverage.schemes_total, data.schemes.len());
    assert_eq!(
        import.coverage.can_replace_std_lowering(),
        !import.coverage.has_partial_value_or_type_import()
            && import.coverage.schemes_total == import.coverage.schemes_resolved
            && import.coverage.role_methods_total == import.coverage.role_methods_resolved
            && import.coverage.effect_methods_total == import.coverage.effect_methods_resolved
    );
    let int_add_scheme = data
        .schemes
        .iter()
        .position(|scheme| scheme.symbol == int_add.snapshot_id)
        .expect("std::int::add imported scheme ref");
    assert_eq!(
        import.refs.schemes[int_add_scheme], import.values[int_add.snapshot_id as usize],
        "scheme refs should be resolved through imported value refs"
    );
    assert_eq!(import.refs.role_methods.len(), data.role_methods.len());
    assert_eq!(import.refs.effect_methods.len(), data.effect_methods.len());
    assert_eq!(
        import.refs.effect_method_modules.len(),
        data.effect_methods.len()
    );

    let prelude = data
        .modules
        .iter()
        .find(|module| module.path == ["std", "prelude"])
        .expect("std::prelude snapshot module");
    assert!(
        import.modules[prelude.snapshot_id as usize].is_some(),
        "source-defined std::prelude module skeleton should be restored"
    );
    let missing_symbol = data.values.len() as u32;
    let bogus_value = StdInferSnapshotSymbol {
        path: vec!["std".to_string(), "prelude".to_string(), "one".to_string()],
        snapshot_id: missing_symbol,
    };
    let mut data_with_missing_value = data.clone();
    data_with_missing_value.values.push(bogus_value);
    let import_with_missing_value =
        import_std_infer_snapshot_data(&data_with_missing_value).expect("snapshot import");
    assert!(
        import_with_missing_value.coverage.values_resolved
            < import_with_missing_value.coverage.values_total
    );
    assert!(
        import_with_missing_value
            .coverage
            .has_partial_value_or_type_import()
    );
    assert!(
        !import_with_missing_value
            .coverage
            .can_replace_std_lowering()
    );
    assert!(
        import_with_missing_value
            .missing
            .values
            .iter()
            .any(|missing| missing.snapshot_id == missing_symbol
                && missing.path == ["std", "prelude", "one"]),
        "missing std value paths should be reported structurally: {:?}",
        import_with_missing_value.missing.values
    );
}

#[test]
fn std_core_snapshot_data_round_trips_through_json() {
    let source_set = collect_inline_source_files_with_options(
        "use std::prelude::*\none",
        [InlineSource {
            path: PathBuf::from("<std>/prelude.yu"),
            module_path: CorePath {
                segments: vec![CoreName("std".to_string()), CoreName("prelude".to_string())],
            },
            origin: SourceOrigin::Std,
            source: "pub my one = 1\n".to_string(),
            meta: None,
        }],
        SourceOptions {
            std_root: None,
            implicit_prelude: false,
            search_paths: Vec::new(),
        },
    );
    let data = build_std_core_snapshot_data(&source_set).expect("std core snapshot data");
    assert!(
        data.program.program.bindings.iter().any(|binding| binding
            .name
            .segments
            .iter()
            .map(|name| name.0.as_str())
            .eq(["std", "int", "add"])),
        "std core snapshot should include builtin bindings"
    );
    let json = serde_json::to_string(&data).expect("serialize std core snapshot");
    let round_tripped: StdCoreSnapshotData =
        serde_json::from_str(&json).expect("deserialize std core snapshot");
    assert_eq!(round_tripped, data);
}

#[test]
fn std_snapshot_data_validation_rejects_bad_symbol_refs() {
    let source_set = collect_inline_source_files_with_options(
        "use std::prelude::*\none",
        [InlineSource {
            path: PathBuf::from("<std>/prelude.yu"),
            module_path: CorePath {
                segments: vec![CoreName("std".to_string()), CoreName("prelude".to_string())],
            },
            origin: SourceOrigin::Std,
            source: "pub my one = 1\n".to_string(),
            meta: None,
        }],
        SourceOptions {
            std_root: None,
            implicit_prelude: false,
            search_paths: Vec::new(),
        },
    );
    let mut data = build_std_infer_snapshot_data(&source_set).expect("std snapshot data");
    data.validate().unwrap();

    let missing_symbol = data.values.len() as u32;
    let module = data
        .modules
        .iter_mut()
        .find(|module| !module.values.is_empty())
        .expect("module with values");
    module.values[0].symbol = missing_symbol;

    assert!(matches!(
        data.validate(),
        Err(StdInferSnapshotDataError::MissingModuleValue { .. })
    ));
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

my shorthand_header { flag, width } =
    if flag:
        width
    else:
        0

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

my case_shorthand_guard x = case x:
    { flag, width } if flag -> width
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
    write_real_std_prelude(&root);

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
    write_real_std_prelude(&root);

    let mut lowered = lower_entry_with_options(
        root.join("main.yu"),
        SourceOptions {
            std_root: Some(root.join("std")),
            implicit_prelude: true,
            search_paths: Vec::new(),
        },
    )
    .unwrap();
    let binding_paths = lowered.state.ctx.collect_all_binding_paths();
    let program = crate::export_core_program_for_binding_paths(&mut lowered.state, &binding_paths);
    let y = program
        .program
        .bindings
        .iter()
        .find(|binding| binding.name.segments.last().map(|name| name.0.as_str()) == Some("y"))
        .expect("y should be exported");

    match &y.body {
        yulang_typed_ir::Expr::Apply { callee, arg, .. } => {
            assert_eq!(
                arg.as_ref(),
                &yulang_typed_ir::Expr::Lit(yulang_typed_ir::Lit::Int("2".to_string()))
            );
            match callee.as_ref() {
                yulang_typed_ir::Expr::Apply { callee, arg, .. } => {
                    assert_eq!(
                        arg.as_ref(),
                        &yulang_typed_ir::Expr::Lit(yulang_typed_ir::Lit::Int("1".to_string()))
                    );
                    match callee.as_ref() {
                        yulang_typed_ir::Expr::Var(path) => {
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
    write_real_std_prelude(&root);

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
    write_real_std_prelude(&root);

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
    write_real_std_prelude(&root);

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
    write_real_std_prelude(&root);

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
    write_real_std_prelude(&root);

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

    assert_eq!(size.1, "std::list::list<int> -> int");

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
    write_real_std_prelude(&root);

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
    write_real_std_prelude(&root);

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
fn lowers_nested_list_pattern_wildcards_from_source_loader() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my pick(xs: list (list int)) = case xs:\n  [[0, _], _] -> 9\n  [[1, a], [3, _]] -> a\n  _ -> 0\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        let pick = rendered
            .iter()
            .find(|(name, _)| name == "pick")
            .expect("pick should be rendered");

        assert_eq!(pick.1, "std::list::list<std::list::list<int>> -> int");
    });
}

#[test]
fn resolves_unqualified_prelude_variant_pattern_from_source_loader() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "case just 42:\n  just n -> n\n  _ -> 0\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let program = crate::export_core_program(&mut lowered.state);
        let result = program
            .program
            .root_exprs
            .first()
            .expect("root expression should be exported");
        let yulang_typed_ir::Expr::Match { arms, .. } = result else {
            panic!("result should lower to a match expression");
        };
        let yulang_typed_ir::Pattern::Variant { tag, .. } = &arms[0].pattern else {
            panic!("first arm should be a variant pattern");
        };
        assert_eq!(tag, &yulang_typed_ir::Name("just".to_string()));
    });
}

#[test]
fn exports_top_level_destructuring_bindings_as_principal_bodies() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my (a, b) = (1, 2)\n\
             my { x, ..rec_rest } = { x: 3, y: 4 }\n\
             my [first, ..list_rest] = [10, 20, 30]\n\
             a + b + x + first\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let program = crate::export_core_program(&mut lowered.state);
        let binding_names = program
            .program
            .bindings
            .iter()
            .map(|binding| binding.name.clone())
            .collect::<Vec<_>>();

        for name in ["a", "b", "x", "first"] {
            assert!(
                binding_names
                    .iter()
                    .any(|path| path == &CorePath::from_name(CoreName(name.to_string()))),
                "missing exported destructuring binding {name}; got {binding_names:?}"
            );
        }

        let scoped_bindings = lowered
            .state
            .ctx
            .collect_all_binding_paths()
            .into_iter()
            .collect::<Vec<_>>();
        for name in ["rec_rest", "list_rest"] {
            assert!(
                scoped_bindings.iter().any(|(path, def)| path.segments
                    == [crate::symbols::Name(name.to_string())]
                    && lowered.state.principal_bodies.contains_key(def)),
                "missing scoped destructuring binding body {name}; got {scoped_bindings:?}"
            );
        }
    });
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
    write_real_std_prelude(&root);

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
    write_real_std_prelude(&root);

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
    write_real_std_prelude(&root);

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
    write_real_std_prelude(&root);

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
                        yulang_typed_ir::Name("std".to_string()),
                        yulang_typed_ir::Name("list".to_string()),
                        yulang_typed_ir::Name("len".to_string()),
                    ]
            })
            .expect("std::list::len should be exported");

        assert!(matches!(
            list_len.body,
            yulang_typed_ir::Expr::PrimitiveOp(yulang_typed_ir::PrimitiveOp::ListLen)
        ));
    });
}

#[test]
fn lowers_nested_not_syntax_from_implicit_prelude() {
    let root = temp_root("tir-implicit-nested-not-syntax");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("std")).unwrap();
    fs::write(root.join("main.yu"), "my x = not not true\n").unwrap();
    write_real_std_prelude(&root);

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
    write_real_std_prelude(&root);

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
    write_real_std_prelude(&root);

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
    write_real_std_prelude(&root);

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
    write_real_std_prelude(&root);

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
    write_real_std_prelude(&root);

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
    write_real_std_prelude(&root);

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
fn compiled_namespace_artifact_preserves_operator_value_identity() {
    let source_set = collect_inline_source_files_with_options(
        "use ops::*\nmy y = 1 %% 2\n",
        [InlineSource {
            path: PathBuf::from("<ops>.yu"),
            module_path: CorePath::new(vec![CoreName("ops".to_string())]),
            origin: SourceOrigin::User,
            source: "pub infix (%%) 50 51 = \\x -> \\y -> x\n".to_string(),
            meta: None,
        }],
        yulang_sources::SourceOptions {
            std_root: None,
            implicit_prelude: false,
            search_paths: Vec::new(),
        },
    );
    let lowered = lower_source_set(&source_set);
    let artifacts = build_compiled_namespace_artifacts(&source_set, &lowered.state);
    let ops_artifact = artifacts
        .iter()
        .find(|artifact| {
            artifact
                .namespace
                .modules
                .iter()
                .any(|module| module.path == vec!["ops"])
        })
        .expect("ops namespace artifact should exist");
    let ops_module = ops_artifact
        .namespace
        .modules
        .iter()
        .find(|module| module.path == vec!["ops"])
        .unwrap();
    let op = ops_module
        .operators
        .iter()
        .find(|operator| operator.name == "%%")
        .expect("operator value should be exported");
    let validation = ops_artifact.namespace.validate();

    assert_eq!(op.fixity, StdInferSnapshotOperatorFixity::Infix);
    assert!(validation.is_complete());
    assert_eq!(validation.operators, 1);
    assert!(
        ops_artifact
            .namespace
            .values
            .iter()
            .any(|symbol| symbol.unit_id == op.symbol
                && symbol.path == vec!["ops".to_string(), "#op:infix:%%".to_string()])
    );
}

#[test]
fn compiled_namespace_artifact_preserves_value_and_type_symbols() {
    let source_set = collect_inline_source_files_with_options(
        "use data::*\nmy y = box 1\n",
        [InlineSource {
            path: PathBuf::from("<data>.yu"),
            module_path: CorePath::new(vec![CoreName("data".to_string())]),
            origin: SourceOrigin::User,
            source: "pub struct box 'a:\n  value: 'a\n\npub make x = box x\n".to_string(),
            meta: None,
        }],
        yulang_sources::SourceOptions {
            std_root: None,
            implicit_prelude: false,
            search_paths: Vec::new(),
        },
    );
    let lowered = lower_source_set(&source_set);
    let artifacts = build_compiled_namespace_artifacts(&source_set, &lowered.state);
    let data_artifact = artifacts
        .iter()
        .find(|artifact| {
            artifact
                .namespace
                .modules
                .iter()
                .any(|module| module.path == vec!["data"])
        })
        .expect("data namespace artifact should exist");
    let data_module = data_artifact
        .namespace
        .modules
        .iter()
        .find(|module| module.path == vec!["data"])
        .unwrap();

    assert!(data_module.values.iter().any(|value| value.name == "make"));
    assert!(data_module.types.iter().any(|ty| ty.name == "box"));
    assert!(
        data_artifact
            .namespace
            .values
            .iter()
            .any(|symbol| symbol.path == vec!["data".to_string(), "make".to_string()])
    );
    assert!(
        data_artifact
            .namespace
            .types
            .iter()
            .any(|symbol| symbol.path == vec!["data".to_string(), "box".to_string()])
    );

    let encoded = serde_json::to_string(data_artifact).unwrap();
    let decoded: CompiledUnitNamespaceArtifact = serde_json::from_str(&encoded).unwrap();
    assert_eq!(&decoded, data_artifact);
    assert!(decoded.namespace.validate().is_complete());
}

#[test]
fn compiled_namespace_artifact_canonicalizes_reexported_type_symbols() {
    let source_set = collect_inline_source_files_with_options(
        "use facade::*\nmy y: thing = thing { value: 1 }\n",
        [
            InlineSource {
                path: PathBuf::from("<data>.yu"),
                module_path: CorePath::new(vec![CoreName("data".to_string())]),
                origin: SourceOrigin::User,
                source: "pub struct thing:\n  value: int\n".to_string(),
                meta: None,
            },
            InlineSource {
                path: PathBuf::from("<facade>.yu"),
                module_path: CorePath::new(vec![CoreName("facade".to_string())]),
                origin: SourceOrigin::User,
                source: "pub use data::*\n".to_string(),
                meta: None,
            },
        ],
        yulang_sources::SourceOptions {
            std_root: None,
            implicit_prelude: false,
            search_paths: Vec::new(),
        },
    );
    let lowered = lower_source_set(&source_set);
    let artifacts = build_compiled_namespace_artifacts(&source_set, &lowered.state);
    let facade_artifact = artifacts
        .iter()
        .find(|artifact| {
            artifact
                .namespace
                .modules
                .iter()
                .any(|module| module.path == vec!["facade"])
        })
        .expect("facade namespace artifact should exist");
    let facade_module = facade_artifact
        .namespace
        .modules
        .iter()
        .find(|module| module.path == vec!["facade"])
        .unwrap();
    let facade_type = facade_module
        .types
        .iter()
        .find(|ty| ty.name == "thing")
        .expect("facade should reexport thing");
    let symbol = facade_artifact
        .namespace
        .types
        .iter()
        .find(|symbol| symbol.unit_id == facade_type.symbol)
        .expect("reexported type should have a namespace symbol");

    assert_eq!(symbol.path, vec!["data".to_string(), "thing".to_string()]);
}

#[test]
fn compiled_namespace_validation_reports_missing_operator_symbol() {
    let surface = CompiledNamespaceSurface {
        modules: vec![CompiledNamespaceModule {
            path: vec!["ops".to_string()],
            values: Vec::new(),
            operators: vec![CompiledNamespaceModuleOperator {
                name: "%%".to_string(),
                fixity: StdInferSnapshotOperatorFixity::Infix,
                symbol: 0,
                visibility: StdInferSnapshotVisibility::Pub,
                lazy: false,
            }],
            types: Vec::new(),
            modules: Vec::new(),
        }],
        values: Vec::new(),
        types: Vec::new(),
    };
    let validation = surface.validate();

    assert!(!validation.is_complete());
    assert_eq!(validation.missing_value_symbols.len(), 1);
    assert_eq!(validation.missing_value_symbols[0].name, "#op:infix:%%");
}

#[test]
fn compiled_namespace_import_restores_value_type_and_operator_resolution() {
    let source_set = collect_inline_source_files_with_options(
        "use data::*\nuse ops::*\nmy y = make (1 %% 2)\n",
        [
            InlineSource {
                path: PathBuf::from("<data>.yu"),
                module_path: CorePath::new(vec![CoreName("data".to_string())]),
                origin: SourceOrigin::User,
                source: "pub struct box 'a:\n  value: 'a\n\npub make x = box x\n".to_string(),
                meta: None,
            },
            InlineSource {
                path: PathBuf::from("<ops>.yu"),
                module_path: CorePath::new(vec![CoreName("ops".to_string())]),
                origin: SourceOrigin::User,
                source: "pub infix (%%) 50 51 = \\x -> \\y -> x\n".to_string(),
                meta: None,
            },
        ],
        yulang_sources::SourceOptions {
            std_root: None,
            implicit_prelude: false,
            search_paths: Vec::new(),
        },
    );
    let lowered = lower_source_set(&source_set);
    let artifacts = build_compiled_namespace_artifacts(&source_set, &lowered.state);
    let bundle = CompiledNamespaceBundle::from_artifacts(&artifacts);
    let imported = import_compiled_namespace_surface(&bundle.surface).unwrap();
    let data = Path {
        segments: vec![Name("data".to_string())],
    };
    let ops = Path {
        segments: vec![Name("ops".to_string())],
    };
    let data_module = imported.state.ctx.resolve_module_path(&data).unwrap();
    let ops_module = imported.state.ctx.resolve_module_path(&ops).unwrap();

    assert!(
        imported
            .state
            .ctx
            .resolve_path_value(&Path {
                segments: vec![Name("data".to_string()), Name("make".to_string())],
            })
            .is_some()
    );
    assert!(
        imported
            .state
            .ctx
            .resolve_path_type(&Path {
                segments: vec![Name("data".to_string()), Name("box".to_string())],
            })
            .is_some()
    );
    assert!(
        imported
            .state
            .ctx
            .resolve_operator_value_from(ops_module, &Name("%%".to_string()), OperatorFixity::Infix)
            .is_some()
    );
    assert!(
        imported
            .state
            .ctx
            .resolve_value_from(data_module, &Name("make".to_string()))
            .is_some()
    );
}

#[test]
fn compiled_typed_artifact_preserves_schemes_and_validates_symbols() {
    let source_set = collect_inline_source_files_with_options(
        "use data::*\nmy y = id 1\n",
        [InlineSource {
            path: PathBuf::from("<data>.yu"),
            module_path: CorePath::new(vec![CoreName("data".to_string())]),
            origin: SourceOrigin::User,
            source: "pub id x = x\n".to_string(),
            meta: None,
        }],
        yulang_sources::SourceOptions {
            std_root: None,
            implicit_prelude: false,
            search_paths: Vec::new(),
        },
    );
    let lowered = lower_source_set(&source_set);
    let artifacts = build_compiled_typed_artifacts(&source_set, &lowered.state);
    let data_artifact = artifacts
        .iter()
        .find(|artifact| {
            artifact
                .namespace
                .modules
                .iter()
                .any(|module| module.path == vec!["data"])
        })
        .expect("data typed artifact should exist");
    let validation = data_artifact.typed.validate(&data_artifact.namespace);

    assert!(validation.is_complete());
    assert!(
        data_artifact
            .typed
            .schemes
            .iter()
            .any(|scheme| scheme.rendered.contains("->"))
    );

    let encoded = serde_json::to_string(data_artifact).unwrap();
    let decoded: CompiledUnitTypedArtifact = serde_json::from_str(&encoded).unwrap();
    assert_eq!(&decoded, data_artifact);
}

#[test]
fn compiled_typed_import_resolves_scheme_refs() {
    let source_set = collect_inline_source_files_with_options(
        "use data::*\nmy y = id 1\n",
        [InlineSource {
            path: PathBuf::from("<data>.yu"),
            module_path: CorePath::new(vec![CoreName("data".to_string())]),
            origin: SourceOrigin::User,
            source: "pub id x = x\n".to_string(),
            meta: None,
        }],
        yulang_sources::SourceOptions {
            std_root: None,
            implicit_prelude: false,
            search_paths: Vec::new(),
        },
    );
    let lowered = lower_source_set(&source_set);
    let artifacts = build_compiled_typed_artifacts(&source_set, &lowered.state);
    let data_artifact = artifacts
        .iter()
        .find(|artifact| {
            artifact
                .namespace
                .modules
                .iter()
                .any(|module| module.path == vec!["data"])
        })
        .expect("data typed artifact should exist");
    let imported = import_compiled_typed_artifact(data_artifact).unwrap();

    assert!(imported.validation.is_complete());
    assert!(imported.coverage.has_complete_ref_resolution());
    assert!(imported.coverage.schemes_total > 0);
    assert_eq!(
        imported.coverage.schemes_total,
        imported.coverage.schemes_resolved
    );
    assert_eq!(
        imported.refs.schemes.len(),
        data_artifact.typed.schemes.len()
    );
    assert!(imported.refs.schemes.iter().all(Option::is_some));
    assert!(
        data_artifact
            .typed
            .schemes
            .iter()
            .any(|scheme| scheme.compact.is_some())
    );
    assert!(
        imported
            .refs
            .schemes
            .iter()
            .any(|def| def.as_ref().is_some_and(|def| imported
                .namespace
                .state
                .infer
                .compact_schemes
                .borrow()
                .contains_key(def)))
    );
    let def = imported
        .refs
        .schemes
        .iter()
        .find_map(|def| *def)
        .expect("imported scheme def");
    assert!(
        imported
            .namespace
            .state
            .infer
            .frozen_scheme_of(def)
            .is_some()
    );
}

#[test]
fn compiled_typed_import_preserves_operator_role_constraints() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let source_set = collect_virtual_source_files_with_options(
            "my both x y = x + y\n",
            Some(repo_root),
            yulang_sources::SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let mut lowered = lower_source_set(&source_set);
        lowered.state.finalize_compact_results();
        let artifacts = build_compiled_unit_artifacts(&source_set, &lowered.state);
        let std_artifacts = artifacts
            .into_iter()
            .filter(|artifact| artifact.manifest.origin == SourceCompilationUnitOrigin::Std)
            .collect::<Vec<_>>();
        let bundle =
            build_compiled_unit_artifact_bundle(&std_artifacts).expect("std compiled unit bundle");
        let mut imported = lower_source_set_with_trusted_compiled_unit_artifact_bundle_profiled(
            &source_set,
            &bundle,
        )
        .lowered
        .lowered;
        let rendered = render_compact_results(&mut imported.state);
        let both = rendered
            .iter()
            .find(|(name, _)| name == "both")
            .expect("both should be rendered");

        assert_eq!(both.1, "Add<α> => α -> α -> α");
    });
}

#[test]
fn compiled_typed_import_preserves_associated_role_method_output_for_root_expr() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let options = yulang_sources::SourceOptions {
            std_root: Some(std_root),
            implicit_prelude: true,
            search_paths: Vec::new(),
        };
        let first = collect_virtual_source_files_with_options(
            "(1/3).say\n",
            Some(repo_root.clone()),
            options.clone(),
        )
        .unwrap();
        let mut lowered = lower_source_set(&first);
        lowered.state.finalize_compact_results();
        let artifacts = build_compiled_unit_artifacts(&first, &lowered.state);
        let std_artifacts = artifacts
            .into_iter()
            .filter(|artifact| artifact.manifest.origin == SourceCompilationUnitOrigin::Std)
            .collect::<Vec<_>>();
        let bundle =
            build_compiled_unit_artifact_bundle(&std_artifacts).expect("std compiled unit bundle");
        assert!(
            bundle.typed.role_methods.iter().any(|method| {
                method.name == "div"
                    && method.role == ["std", "prelude", "Div"]
                    && method.input_names == [Some("a".to_string())]
                    && method.output_name.as_deref() == Some("out")
            }),
            "compiled std bundle should preserve Div::div role method input/output mapping, got {:?}",
            bundle.typed.role_methods
        );

        let second =
            collect_virtual_source_files_with_options("(7/3).say\n", Some(repo_root), options)
                .unwrap();
        let mut imported =
            lower_source_set_with_trusted_compiled_unit_artifact_bundle_profiled(&second, &bundle)
                .lowered
                .lowered;
        imported.state.finalize_compact_results();
        assert!(
            imported.state.infer.type_errors().is_empty(),
            "cached std import should type-check associated Div output, got {:?}",
            imported.state.infer.type_errors(),
        );
    });
}

#[test]
fn compiled_typed_validation_reports_missing_scheme_symbol() {
    let typed = CompiledTypedSurface {
        schemes: vec![StdInferSnapshotScheme {
            symbol: 7,
            rendered: "int".to_string(),
            compact: None,
            role_constraints: Vec::new(),
        }],
        ..CompiledTypedSurface::default()
    };
    let validation = typed.validate(&CompiledNamespaceSurface::default());

    assert!(!validation.is_complete());
    assert_eq!(validation.missing_scheme_symbols, vec![7]);
}

#[test]
fn compiled_typed_import_rejects_missing_scheme_symbol() {
    let typed = CompiledTypedSurface {
        schemes: vec![StdInferSnapshotScheme {
            symbol: 7,
            rendered: "int".to_string(),
            compact: None,
            role_constraints: Vec::new(),
        }],
        ..CompiledTypedSurface::default()
    };
    let err = match import_compiled_typed_surface(&CompiledNamespaceSurface::default(), &typed) {
        Ok(_) => panic!("invalid typed surface should be rejected"),
        Err(err) => err,
    };

    assert!(matches!(err, CompiledTypedImportError::InvalidTyped(_)));
}

#[test]
fn compiled_unit_artifact_bundles_syntax_namespace_and_typed_surfaces() {
    let source_set = collect_inline_source_files_with_options(
        "use data::*\nuse ops::*\nmy y = id (1 %% 2)\n",
        [
            InlineSource {
                path: PathBuf::from("<data>.yu"),
                module_path: CorePath::new(vec![CoreName("data".to_string())]),
                origin: SourceOrigin::User,
                source: "pub id x = x\n".to_string(),
                meta: None,
            },
            InlineSource {
                path: PathBuf::from("<ops>.yu"),
                module_path: CorePath::new(vec![CoreName("ops".to_string())]),
                origin: SourceOrigin::User,
                source: "pub infix (%%) 50 51 = \\x -> \\y -> x\n".to_string(),
                meta: None,
            },
        ],
        yulang_sources::SourceOptions {
            std_root: None,
            implicit_prelude: false,
            search_paths: Vec::new(),
        },
    );
    let lowered = lower_source_set(&source_set);
    let artifacts = build_compiled_unit_artifacts(&source_set, &lowered.state);
    let data_artifact = artifacts
        .iter()
        .find(|artifact| {
            artifact
                .namespace
                .modules
                .iter()
                .any(|module| module.path == vec!["data"])
        })
        .expect("data unit artifact should exist");
    let ops_artifact = artifacts
        .iter()
        .find(|artifact| {
            artifact
                .namespace
                .modules
                .iter()
                .any(|module| module.path == vec!["ops"])
        })
        .expect("ops unit artifact should exist");

    assert!(
        data_artifact
            .typed
            .validate(&data_artifact.namespace)
            .is_complete()
    );
    assert!(
        ops_artifact
            .syntax
            .public_exports
            .iter()
            .any(|export| export.name.0 == "%%")
    );
    assert!(
        ops_artifact
            .namespace
            .modules
            .iter()
            .flat_map(|module| &module.operators)
            .any(|operator| operator.name == "%%")
    );
    assert!(
        ops_artifact
            .runtime
            .program
            .program
            .bindings
            .iter()
            .any(|binding| binding
                .name
                .segments
                .iter()
                .any(|name| name.0 == "#op:infix:%%"))
    );

    let encoded = serde_json::to_string(ops_artifact).unwrap();
    let decoded: CompiledUnitArtifact = serde_json::from_str(&encoded).unwrap();
    assert_eq!(&decoded, ops_artifact);
}

#[test]
fn compiled_unit_import_restores_syntax_and_typed_refs() {
    let source_set = collect_inline_source_files_with_options(
        "use ops::*\nmy y = 1 %% 2\n",
        [InlineSource {
            path: PathBuf::from("<ops>.yu"),
            module_path: CorePath::new(vec![CoreName("ops".to_string())]),
            origin: SourceOrigin::User,
            source: "pub infix (%%) 50 51 = \\x -> \\y -> x\n".to_string(),
            meta: None,
        }],
        yulang_sources::SourceOptions {
            std_root: None,
            implicit_prelude: false,
            search_paths: Vec::new(),
        },
    );
    let lowered = lower_source_set(&source_set);
    let artifacts = build_compiled_unit_artifacts(&source_set, &lowered.state);
    let ops_artifact = artifacts
        .iter()
        .find(|artifact| {
            artifact
                .namespace
                .modules
                .iter()
                .any(|module| module.path == vec!["ops"])
        })
        .expect("ops unit artifact should exist");
    let imported = import_compiled_unit_artifact(ops_artifact).unwrap();

    assert!(
        imported
            .syntax
            .public_exports
            .iter()
            .any(|export| export.name.0 == "%%")
    );
    assert!(imported.typed.coverage.has_complete_ref_resolution());
    assert!(
        imported
            .runtime
            .program
            .program
            .bindings
            .iter()
            .any(|binding| binding
                .name
                .segments
                .iter()
                .any(|name| name.0 == "#op:infix:%%"))
    );
}

#[test]
fn compiled_unit_import_skips_cached_dependency_scc() {
    let source_set = collect_inline_source_files_with_options(
        "use ops::*\nmy y = 1 %% 2\n",
        [InlineSource {
            path: PathBuf::from("<ops>.yu"),
            module_path: CorePath::new(vec![CoreName("ops".to_string())]),
            origin: SourceOrigin::User,
            source: "pub infix (%%) 50 51 = \\x -> \\y -> x\n".to_string(),
            meta: None,
        }],
        yulang_sources::SourceOptions {
            std_root: None,
            implicit_prelude: false,
            search_paths: Vec::new(),
        },
    );
    let lowered = lower_source_set(&source_set);
    let artifacts = build_compiled_unit_artifacts(&source_set, &lowered.state);
    let ops_artifact = artifacts
        .iter()
        .find(|artifact| {
            artifact
                .namespace
                .modules
                .iter()
                .any(|module| module.path == vec!["ops"])
        })
        .expect("ops unit artifact should exist")
        .clone();
    let bundle = build_compiled_unit_artifact_bundle(&[ops_artifact]).unwrap();

    let mut imported =
        lower_source_set_with_trusted_compiled_unit_artifact_bundle_profiled(&source_set, &bundle);
    imported.lowered.lowered.state.finalize_compact_results();

    assert_eq!(imported.lowered.profile.entry.files, 1);
    assert_eq!(imported.lowered.profile.user.files, 0);
    assert!(
        imported
            .lowered
            .lowered
            .state
            .infer
            .type_errors()
            .is_empty()
    );
}

#[test]
fn compiled_unit_semantic_bundle_import_skips_cached_dependency_scc_without_runtime() {
    let source_set = collect_inline_source_files_with_options(
        "use ops::*\nmy y = 1 %% 2\n",
        [InlineSource {
            path: PathBuf::from("<ops>.yu"),
            module_path: CorePath::new(vec![CoreName("ops".to_string())]),
            origin: SourceOrigin::User,
            source: "pub infix (%%) 50 51 = \\x -> \\y -> x\n".to_string(),
            meta: None,
        }],
        yulang_sources::SourceOptions {
            std_root: None,
            implicit_prelude: false,
            search_paths: Vec::new(),
        },
    );
    let lowered = lower_source_set(&source_set);
    let artifacts = build_compiled_unit_artifacts(&source_set, &lowered.state);
    let ops_artifact = artifacts
        .iter()
        .find(|artifact| {
            artifact
                .namespace
                .modules
                .iter()
                .any(|module| module.path == vec!["ops"])
        })
        .expect("ops unit artifact should exist")
        .clone();
    let bundle = build_compiled_unit_artifact_bundle(&[ops_artifact]).unwrap();
    let semantic_bundle = CompiledUnitSemanticArtifactBundle::from(&bundle);

    let mut imported =
        lower_source_set_with_trusted_compiled_unit_semantic_artifact_bundle_profiled(
            &source_set,
            &semantic_bundle,
        );
    imported.lowered.state.finalize_compact_results();

    assert_eq!(imported.profile.entry.files, 1);
    assert_eq!(imported.profile.user.files, 0);
    assert!(imported.lowered.state.infer.type_errors().is_empty());
}

#[test]
fn cached_source_act_template_seed_is_only_needed_for_act_copy_sources() {
    assert!(!source_may_contain_act_copy("my x = 1\nx\n"));
    assert!(!source_may_contain_act_copy("my fact = 1\n"));
    assert!(!source_may_contain_act_copy(
        "pub act out:\n  our write: str -> ()\n"
    ));
    assert!(source_may_contain_act_copy("my act next = last\n"));
    assert!(source_may_contain_act_copy("my act\tnext = last\n"));
}

#[test]
fn compiled_std_runtime_bundle_carries_non_unit_runtime_dependencies() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let source_set = collect_virtual_source_files_with_options(
            "(each 1..3 + each 1..3).list\n",
            Some(repo_root.clone()),
            yulang_sources::SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let mut lowered = lower_source_set(&source_set);
        lowered.state.finalize_compact_results_profiled();
        let artifacts = build_compiled_unit_artifacts(&source_set, &lowered.state);
        let runtime = CompiledRuntimeBundle::from_surfaces(
            artifacts
                .iter()
                .filter(|artifact| {
                    artifact.manifest.origin == yulang_sources::SourceCompilationUnitOrigin::Std
                })
                .map(|artifact| &artifact.runtime),
        )
        .expect("std runtime surfaces should merge without duplicate unit bindings");
        let binding_paths = runtime
            .surface
            .program
            .program
            .bindings
            .iter()
            .map(|binding| {
                binding
                    .name
                    .segments
                    .iter()
                    .map(|segment| segment.0.as_str())
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        assert!(
            binding_paths
                .iter()
                .any(|path| path.as_slice() == ["std", "int", "add"])
        );
        assert_eq!(
            binding_paths
                .iter()
                .filter(|path| path.as_slice() == ["std", "list", "empty"])
                .count(),
            1
        );
    });
}

#[test]
fn compiled_std_artifact_import_keeps_effectful_guard_constraints() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let source_set = collect_virtual_source_files_with_options(
            "{\n  my a = each 1..3\n  my b = each 1..3\n  guard: a <= b\n  (a, b)\n}.list\n",
            Some(repo_root.clone()),
            yulang_sources::SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let mut lowered = lower_source_set(&source_set);
        lowered.state.finalize_compact_results_profiled();
        let artifacts = build_compiled_unit_artifacts(&source_set, &lowered.state);
        let bundle = build_compiled_unit_artifact_bundle(
            &artifacts
                .into_iter()
                .filter(|artifact| {
                    artifact.manifest.origin == yulang_sources::SourceCompilationUnitOrigin::Std
                })
                .collect::<Vec<_>>(),
        )
        .expect("std compiled unit bundle");
        let mut imported = lower_source_set_with_trusted_compiled_unit_artifact_bundle_profiled(
            &source_set,
            &bundle,
        );
        imported.lowered.lowered.state.finalize_compact_results();

        assert!(
            imported
                .lowered
                .lowered
                .state
                .infer
                .type_errors()
                .is_empty(),
            "cached std artifact import should preserve effectful guard constraints: {:?}",
            imported.lowered.lowered.state.infer.type_errors()
        );
    });
}

#[test]
fn compiled_runtime_bundle_merges_surfaces_and_remaps_evidence_ids() {
    let left = runtime_surface_with_coerce_binding("left", 0);
    let right = runtime_surface_with_coerce_binding("right", 0);
    let bundle = CompiledRuntimeBundle::from_surfaces([&left, &right]).unwrap();

    assert_eq!(bundle.surface.program.program.bindings.len(), 2);
    assert_eq!(
        bundle
            .surface
            .program
            .evidence
            .expected_edges
            .iter()
            .map(|edge| edge.id)
            .collect::<Vec<_>>(),
        vec![0, 1]
    );

    let right_binding = bundle
        .surface
        .program
        .program
        .bindings
        .iter()
        .find(|binding| binding.name.segments[0].0 == "right")
        .expect("right binding");
    let yulang_typed_ir::Expr::Coerce {
        evidence: Some(evidence),
        ..
    } = &right_binding.body
    else {
        panic!("right binding should keep coerce evidence");
    };
    assert_eq!(evidence.source_edge, Some(1));
}

#[test]
fn compiled_runtime_bundle_remaps_record_pattern_default_apply_evidence() {
    let left = runtime_surface_with_coerce_binding("left", 0);
    let right = runtime_surface_with_record_default_apply_binding("right");
    let bundle = CompiledRuntimeBundle::from_surfaces([&left, &right]).unwrap();

    let right_binding = bundle
        .surface
        .program
        .program
        .bindings
        .iter()
        .find(|binding| binding.name.segments[0].0 == "right")
        .expect("right binding");
    let yulang_typed_ir::Expr::Block { stmts, .. } = &right_binding.body else {
        panic!("right binding should keep block body");
    };
    let yulang_typed_ir::Stmt::Let { pattern, .. } = &stmts[0] else {
        panic!("right binding should keep let statement");
    };
    let yulang_typed_ir::Pattern::Record { fields, .. } = pattern else {
        panic!("right binding should keep record pattern");
    };
    let yulang_typed_ir::Expr::Apply {
        evidence: Some(evidence),
        ..
    } = fields[0].default.as_ref().expect("record field default")
    else {
        panic!("record field default should keep apply evidence");
    };

    assert_eq!(evidence.callee_source_edge, Some(1));
    assert_eq!(evidence.arg_source_edge, Some(2));
}

#[test]
fn compiled_runtime_bundle_merges_primitive_type_metadata() {
    let mut left = runtime_surface_with_coerce_binding("left", 0);
    let mut right = runtime_surface_with_coerce_binding("right", 0);
    left.program
        .graph
        .primitive_types
        .push(primitive_type_node("int"));
    right
        .program
        .graph
        .primitive_types
        .push(primitive_type_node("int"));
    right
        .program
        .graph
        .primitive_types
        .push(primitive_type_node("bool"));

    let bundle = CompiledRuntimeBundle::from_surfaces([&left, &right]).unwrap();

    assert_eq!(
        bundle.surface.program.graph.primitive_types,
        vec![primitive_type_node("int"), primitive_type_node("bool")]
    );
}

#[test]
fn compiled_runtime_bundle_merges_enum_variant_payload_surface() {
    let mut left = runtime_surface_with_coerce_binding("left", 0);
    let mut right = runtime_surface_with_coerce_binding("right", 0);
    left.program
        .graph
        .enum_variants
        .push(enum_variant_node("list_view", "empty", None));
    right
        .program
        .graph
        .enum_variants
        .push(enum_variant_node("list_view", "empty", None));
    right.program.graph.enum_variants.push(enum_variant_node(
        "list_view",
        "node",
        Some(yulang_typed_ir::Type::Tuple(vec![
            yulang_typed_ir::Type::Named {
                path: CorePath::from_name(CoreName("list".to_string())),
                args: vec![yulang_typed_ir::TypeArg::Type(yulang_typed_ir::Type::Var(
                    yulang_typed_ir::TypeVar("a".to_string()),
                ))],
            },
            yulang_typed_ir::Type::Named {
                path: CorePath::from_name(CoreName("list".to_string())),
                args: vec![yulang_typed_ir::TypeArg::Type(yulang_typed_ir::Type::Var(
                    yulang_typed_ir::TypeVar("a".to_string()),
                ))],
            },
        ])),
    ));

    let bundle = CompiledRuntimeBundle::from_surfaces([&left, &right]).unwrap();

    assert_eq!(
        bundle.surface.program.graph.enum_variants,
        vec![
            enum_variant_node("list_view", "empty", None),
            enum_variant_node(
                "list_view",
                "node",
                Some(yulang_typed_ir::Type::Tuple(vec![
                    yulang_typed_ir::Type::Named {
                        path: CorePath::from_name(CoreName("list".to_string())),
                        args: vec![yulang_typed_ir::TypeArg::Type(yulang_typed_ir::Type::Var(
                            yulang_typed_ir::TypeVar("a".to_string()),
                        ))],
                    },
                    yulang_typed_ir::Type::Named {
                        path: CorePath::from_name(CoreName("list".to_string())),
                        args: vec![yulang_typed_ir::TypeArg::Type(yulang_typed_ir::Type::Var(
                            yulang_typed_ir::TypeVar("a".to_string()),
                        ))],
                    },
                ])),
            ),
        ]
    );
}

#[test]
fn compiled_runtime_bundle_rejects_conflicting_primitive_type_metadata() {
    let mut left = runtime_surface_with_coerce_binding("left", 0);
    let mut right = runtime_surface_with_coerce_binding("right", 0);
    left.program
        .graph
        .primitive_types
        .push(primitive_type_node("int"));
    right
        .program
        .graph
        .primitive_types
        .push(yulang_typed_ir::PrimitiveTypeGraphNode {
            family: yulang_typed_ir::PrimitiveTypeFamily::Int,
            path: CorePath::new(vec![
                CoreName("other".to_string()),
                CoreName("int".to_string()),
            ]),
        });

    let err = CompiledRuntimeBundle::from_surfaces([&left, &right]).unwrap_err();

    assert!(matches!(
        err,
        CompiledRuntimeMergeError::ConflictingPrimitiveType {
            family: yulang_typed_ir::PrimitiveTypeFamily::Int
        }
    ));
}

#[test]
fn compiled_runtime_bundle_rejects_conflicting_binding_paths() {
    let left = runtime_surface_with_coerce_binding("same", 0);
    let mut right = runtime_surface_with_coerce_binding("same", 0);
    right.program.program.bindings[0].body =
        yulang_typed_ir::Expr::Lit(yulang_typed_ir::Lit::Int("2".to_string()));

    let err = CompiledRuntimeBundle::from_surfaces([&left, &right]).unwrap_err();
    assert!(matches!(
        err,
        CompiledRuntimeMergeError::ConflictingBinding { .. }
    ));
}

#[test]
fn compiled_runtime_bundle_merges_before_user_program_and_remaps_user_evidence() {
    let dependency = runtime_surface_with_coerce_binding("dependency", 0);
    let user = runtime_surface_with_coerce_binding("user", 0);
    let bundle = CompiledRuntimeBundle::from_surfaces([&dependency]).unwrap();
    let merged = bundle.merge_with_user_program(user.program).unwrap();

    assert_eq!(
        merged
            .evidence
            .expected_edges
            .iter()
            .map(|edge| edge.id)
            .collect::<Vec<_>>(),
        vec![0, 1]
    );

    let user_binding = merged
        .program
        .bindings
        .iter()
        .find(|binding| binding.name.segments[0].0 == "user")
        .expect("user binding");
    let yulang_typed_ir::Expr::Coerce {
        evidence: Some(evidence),
        ..
    } = &user_binding.body
    else {
        panic!("user binding should keep coerce evidence");
    };
    assert_eq!(evidence.source_edge, Some(1));
}

#[test]
fn compiled_runtime_bundle_prunes_unreachable_dependencies_before_user_program() {
    let kept = CorePath::new(vec![
        CoreName("dep".to_string()),
        CoreName("kept".to_string()),
    ]);
    let dropped = CorePath::new(vec![
        CoreName("dep".to_string()),
        CoreName("dropped".to_string()),
    ]);
    let dependency = CompiledRuntimeSurface {
        program: yulang_typed_ir::CoreProgram {
            program: yulang_typed_ir::PrincipalModule {
                bindings: vec![
                    lit_binding(kept.clone(), "1"),
                    lit_binding(dropped.clone(), "2"),
                ],
                ..yulang_typed_ir::PrincipalModule::default()
            },
            graph: yulang_typed_ir::CoreGraphView {
                bindings: vec![
                    binding_graph_node(kept.clone()),
                    binding_graph_node(dropped.clone()),
                ],
                runtime_symbols: vec![
                    runtime_value_symbol(kept.clone()),
                    runtime_value_symbol(dropped.clone()),
                ],
                ..yulang_typed_ir::CoreGraphView::default()
            },
            ..yulang_typed_ir::CoreProgram::default()
        },
    };
    let user = yulang_typed_ir::CoreProgram {
        program: yulang_typed_ir::PrincipalModule {
            root_exprs: vec![yulang_typed_ir::Expr::Var(kept.clone())],
            roots: vec![yulang_typed_ir::PrincipalRoot::Expr(0)],
            ..yulang_typed_ir::PrincipalModule::default()
        },
        graph: yulang_typed_ir::CoreGraphView {
            root_exprs: vec![yulang_typed_ir::ExprGraphNode {
                owner: yulang_typed_ir::GraphOwner::RootExpr(0),
                bounds: yulang_typed_ir::TypeBounds::exact(yulang_typed_ir::Type::Any),
            }],
            ..yulang_typed_ir::CoreGraphView::default()
        },
        ..yulang_typed_ir::CoreProgram::default()
    };
    let bundle = CompiledRuntimeBundle::from_surfaces([&dependency]).unwrap();
    let merged = bundle.merge_with_user_program(user).unwrap();

    assert!(
        merged
            .program
            .bindings
            .iter()
            .any(|binding| binding.name == kept)
    );
    assert!(
        !merged
            .program
            .bindings
            .iter()
            .any(|binding| binding.name == dropped)
    );
    assert!(
        merged
            .graph
            .runtime_symbols
            .iter()
            .any(|symbol| symbol.path == kept)
    );
    assert!(
        !merged
            .graph
            .runtime_symbols
            .iter()
            .any(|symbol| symbol.path == dropped)
    );
}

#[test]
fn compiled_runtime_bundle_keeps_transitive_reachable_dependencies() {
    let kept = CorePath::new(vec![
        CoreName("dep".to_string()),
        CoreName("kept".to_string()),
    ]);
    let helper = CorePath::new(vec![
        CoreName("dep".to_string()),
        CoreName("helper".to_string()),
    ]);
    let dropped = CorePath::new(vec![
        CoreName("dep".to_string()),
        CoreName("dropped".to_string()),
    ]);
    let dependency = CompiledRuntimeSurface {
        program: yulang_typed_ir::CoreProgram {
            program: yulang_typed_ir::PrincipalModule {
                bindings: vec![
                    yulang_typed_ir::PrincipalBinding {
                        name: kept.clone(),
                        scheme: yulang_typed_ir::Scheme {
                            requirements: Vec::new(),
                            body: yulang_typed_ir::Type::Any,
                        },
                        body: yulang_typed_ir::Expr::Var(helper.clone()),
                    },
                    lit_binding(helper.clone(), "1"),
                    lit_binding(dropped.clone(), "2"),
                ],
                ..yulang_typed_ir::PrincipalModule::default()
            },
            graph: yulang_typed_ir::CoreGraphView {
                bindings: vec![
                    binding_graph_node(kept.clone()),
                    binding_graph_node(helper.clone()),
                    binding_graph_node(dropped.clone()),
                ],
                runtime_symbols: vec![
                    runtime_value_symbol(kept.clone()),
                    runtime_value_symbol(helper.clone()),
                    runtime_value_symbol(dropped.clone()),
                ],
                ..yulang_typed_ir::CoreGraphView::default()
            },
            ..yulang_typed_ir::CoreProgram::default()
        },
    };
    let user = yulang_typed_ir::CoreProgram {
        program: yulang_typed_ir::PrincipalModule {
            root_exprs: vec![yulang_typed_ir::Expr::Var(kept.clone())],
            roots: vec![yulang_typed_ir::PrincipalRoot::Expr(0)],
            ..yulang_typed_ir::PrincipalModule::default()
        },
        graph: yulang_typed_ir::CoreGraphView {
            root_exprs: vec![yulang_typed_ir::ExprGraphNode {
                owner: yulang_typed_ir::GraphOwner::RootExpr(0),
                bounds: yulang_typed_ir::TypeBounds::exact(yulang_typed_ir::Type::Any),
            }],
            ..yulang_typed_ir::CoreGraphView::default()
        },
        ..yulang_typed_ir::CoreProgram::default()
    };
    let bundle = CompiledRuntimeBundle::from_surfaces([&dependency]).unwrap();
    let merged = bundle.merge_with_user_program(user).unwrap();
    let merged_bindings = merged
        .program
        .bindings
        .iter()
        .map(|binding| binding.name.clone())
        .collect::<Vec<_>>();

    assert!(merged_bindings.contains(&kept));
    assert!(merged_bindings.contains(&helper));
    assert!(!merged_bindings.contains(&dropped));
}

fn primitive_type_node(name: &str) -> yulang_typed_ir::PrimitiveTypeGraphNode {
    let family = match name {
        "int" => yulang_typed_ir::PrimitiveTypeFamily::Int,
        "bool" => yulang_typed_ir::PrimitiveTypeFamily::Bool,
        other => panic!("unsupported primitive test family: {other}"),
    };
    yulang_typed_ir::PrimitiveTypeGraphNode {
        family,
        path: CorePath::from_name(CoreName(name.to_string())),
    }
}

fn enum_variant_node(
    enum_name: &str,
    tag: &str,
    payload: Option<yulang_typed_ir::Type>,
) -> yulang_typed_ir::EnumVariantGraphNode {
    yulang_typed_ir::EnumVariantGraphNode {
        enum_path: CorePath::from_name(CoreName(enum_name.to_string())),
        tag: CoreName(tag.to_string()),
        type_params: vec![yulang_typed_ir::TypeVar("a".to_string())],
        payload,
    }
}

fn lit_binding(name: CorePath, value: &str) -> yulang_typed_ir::PrincipalBinding {
    yulang_typed_ir::PrincipalBinding {
        name,
        scheme: yulang_typed_ir::Scheme {
            requirements: Vec::new(),
            body: yulang_typed_ir::Type::Any,
        },
        body: yulang_typed_ir::Expr::Lit(yulang_typed_ir::Lit::Int(value.to_string())),
    }
}

fn binding_graph_node(binding: CorePath) -> yulang_typed_ir::BindingGraphNode {
    yulang_typed_ir::BindingGraphNode {
        binding,
        scheme_body: yulang_typed_ir::Type::Any,
        body_bounds: yulang_typed_ir::TypeBounds::exact(yulang_typed_ir::Type::Any),
    }
}

fn runtime_value_symbol(path: CorePath) -> yulang_typed_ir::RuntimeSymbol {
    yulang_typed_ir::RuntimeSymbol {
        path,
        kind: yulang_typed_ir::RuntimeSymbolKind::Value,
    }
}

fn runtime_surface_with_coerce_binding(name: &str, source_edge: u32) -> CompiledRuntimeSurface {
    let path = CorePath::new(vec![CoreName(name.to_string())]);
    let any_scheme = yulang_typed_ir::Scheme {
        requirements: Vec::new(),
        body: yulang_typed_ir::Type::Any,
    };
    CompiledRuntimeSurface {
        program: yulang_typed_ir::CoreProgram {
            program: yulang_typed_ir::PrincipalModule {
                path: CorePath::default(),
                bindings: vec![yulang_typed_ir::PrincipalBinding {
                    name: path.clone(),
                    scheme: any_scheme,
                    body: yulang_typed_ir::Expr::Coerce {
                        expr: Box::new(yulang_typed_ir::Expr::Lit(yulang_typed_ir::Lit::Int(
                            "1".to_string(),
                        ))),
                        evidence: Some(yulang_typed_ir::CoerceEvidence {
                            source_edge: Some(source_edge),
                            actual: yulang_typed_ir::TypeBounds::exact(yulang_typed_ir::Type::Any),
                            expected: yulang_typed_ir::TypeBounds::exact(
                                yulang_typed_ir::Type::Any,
                            ),
                        }),
                    },
                }],
                root_exprs: Vec::new(),
                roots: Vec::new(),
            },
            graph: yulang_typed_ir::CoreGraphView {
                bindings: vec![yulang_typed_ir::BindingGraphNode {
                    binding: path,
                    scheme_body: yulang_typed_ir::Type::Any,
                    body_bounds: yulang_typed_ir::TypeBounds::exact(yulang_typed_ir::Type::Any),
                }],
                root_exprs: Vec::new(),
                runtime_symbols: Vec::new(),
                enum_variants: Vec::new(),
                role_impls: Vec::new(),
                primitive_types: Vec::new(),
            },
            evidence: yulang_typed_ir::PrincipalEvidence {
                expected_edges: vec![yulang_typed_ir::ExpectedEdgeEvidence {
                    id: source_edge,
                    kind: yulang_typed_ir::ExpectedEdgeKind::RepresentationCoerce,
                    source_range: None,
                    actual: yulang_typed_ir::TypeBounds::exact(yulang_typed_ir::Type::Any),
                    expected: yulang_typed_ir::TypeBounds::exact(yulang_typed_ir::Type::Any),
                    actual_effect: None,
                    expected_effect: None,
                    closed: true,
                    informative: true,
                    runtime_usable: true,
                }],
                expected_adapter_edges: Vec::new(),
                derived_expected_edges: Vec::new(),
                handler_matches: Vec::new(),
            },
        },
    }
}

fn runtime_surface_with_record_default_apply_binding(name: &str) -> CompiledRuntimeSurface {
    let path = CorePath::new(vec![CoreName(name.to_string())]);
    let callee = CorePath::new(vec![CoreName("callee".to_string())]);
    let any = yulang_typed_ir::Type::Any;
    let any_bounds = yulang_typed_ir::TypeBounds::exact(any.clone());
    let any_scheme = yulang_typed_ir::Scheme {
        requirements: Vec::new(),
        body: any.clone(),
    };
    let apply_default = yulang_typed_ir::Expr::Apply {
        callee: Box::new(yulang_typed_ir::Expr::Var(callee)),
        arg: Box::new(yulang_typed_ir::Expr::Lit(yulang_typed_ir::Lit::Int(
            "1".to_string(),
        ))),
        evidence: Some(yulang_typed_ir::ApplyEvidence {
            callee_source_edge: Some(0),
            arg_source_edge: Some(1),
            callee: any_bounds.clone(),
            expected_callee: Some(any_bounds.clone()),
            arg: any_bounds.clone(),
            expected_arg: Some(any_bounds.clone()),
            result: any_bounds.clone(),
            principal_callee: None,
            substitutions: Vec::new(),
            substitution_candidates: Vec::new(),
            role_method: false,
            principal_elaboration: None,
        }),
    };
    CompiledRuntimeSurface {
        program: yulang_typed_ir::CoreProgram {
            program: yulang_typed_ir::PrincipalModule {
                path: CorePath::default(),
                bindings: vec![yulang_typed_ir::PrincipalBinding {
                    name: path.clone(),
                    scheme: any_scheme,
                    body: yulang_typed_ir::Expr::Block {
                        stmts: vec![yulang_typed_ir::Stmt::Let {
                            pattern: yulang_typed_ir::Pattern::Record {
                                fields: vec![yulang_typed_ir::RecordPatternField {
                                    name: CoreName("value".to_string()),
                                    pattern: yulang_typed_ir::Pattern::Bind(CoreName(
                                        "value".to_string(),
                                    )),
                                    default: Some(apply_default),
                                }],
                                spread: None,
                            },
                            value: yulang_typed_ir::Expr::Record {
                                fields: Vec::new(),
                                spread: None,
                            },
                        }],
                        tail: None,
                    },
                }],
                root_exprs: Vec::new(),
                roots: Vec::new(),
            },
            graph: yulang_typed_ir::CoreGraphView {
                bindings: vec![yulang_typed_ir::BindingGraphNode {
                    binding: path,
                    scheme_body: any.clone(),
                    body_bounds: any_bounds.clone(),
                }],
                root_exprs: Vec::new(),
                runtime_symbols: Vec::new(),
                enum_variants: Vec::new(),
                role_impls: Vec::new(),
                primitive_types: Vec::new(),
            },
            evidence: yulang_typed_ir::PrincipalEvidence {
                expected_edges: vec![
                    expected_edge_evidence(0, yulang_typed_ir::ExpectedEdgeKind::ApplicationCallee),
                    expected_edge_evidence(
                        1,
                        yulang_typed_ir::ExpectedEdgeKind::ApplicationArgument,
                    ),
                ],
                expected_adapter_edges: Vec::new(),
                derived_expected_edges: Vec::new(),
                handler_matches: Vec::new(),
            },
        },
    }
}

fn expected_edge_evidence(
    id: u32,
    kind: yulang_typed_ir::ExpectedEdgeKind,
) -> yulang_typed_ir::ExpectedEdgeEvidence {
    yulang_typed_ir::ExpectedEdgeEvidence {
        id,
        kind,
        source_range: None,
        actual: yulang_typed_ir::TypeBounds::exact(yulang_typed_ir::Type::Any),
        expected: yulang_typed_ir::TypeBounds::exact(yulang_typed_ir::Type::Any),
        actual_effect: None,
        expected_effect: None,
        closed: true,
        informative: true,
        runtime_usable: true,
    }
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
        let assignment_edges = lowered
            .state
            .expected_edges
            .iter()
            .filter(|edge| edge.kind == ExpectedEdgeKind::AssignmentValue)
            .collect::<Vec<_>>();
        assert_eq!(assignment_edges.len(), 1);
        assert!(
            assignment_edges[0].cause.span.is_some(),
            "assignment expected edge should point at the assigned value",
        );
        assert_expected_edge_value_constraint(&lowered.state, assignment_edges[0]);

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
fn rejects_extra_field_in_struct_literal() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let lowered = lower_virtual_source_with_options(
            "struct point { x: int, y: int }\npoint { x: 3, y: 4, z: 5 }\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let errors = lowered.state.infer.type_errors();

        assert!(
            errors.iter().any(|error| matches!(
                &error.kind,
                crate::diagnostic::TypeErrorKind::UnknownRecordField { name } if name == "z"
            )),
            "struct constructor should reject extra literal field, got {errors:?}",
        );
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
fn lowers_ref_list_assignment_with_local_var_act() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my edited =\n  my ($xs) = [2, 3, 4]\n  &xs[1] = 6\n  $xs\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        let edited = rendered_type(&rendered, "edited");

        assert!(
            edited.contains("std::list::list<int") || edited.contains("list<int"),
            "edited should keep the list element type after ref assignment: {edited}",
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
fn freezes_pub_record_tail_spread_through_compact() {
    // Regression: `compact_pos_type` used to silently drop a CompactType's
    // record_spreads when reconstructing the Pos body of a frozen scheme.
    // For a `pub` binding, the body goes through compact -> freeze, so the
    // spread would disappear and the result type would lose every field
    // not written explicitly inline.
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "pub make_full v = { x: 1, ..v }\n",
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
            .find(|(name, _)| name == "make_full")
            .expect("make_full should be rendered")
            .1;

        assert!(
            ty.contains(".."),
            "frozen pub spread should keep tail form: {ty}"
        );
        assert!(
            ty.contains("x:"),
            "frozen pub spread should retain explicit fields: {ty}"
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
        assert!(
            lowered.state.ctx.refs.unresolved().is_empty(),
            "catch guard should see defaulted pattern local, got unresolved refs: {:?}",
            lowered.state.ctx.refs.unresolved()
        );
    });
}

#[test]
fn lowers_record_pattern_shorthand_in_catch_effect_guards() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "act cfg:\n  our read: { flag: bool } -> int\n\nmy f x = catch x:\n  cfg::read { flag }, k if flag -> 1\n  _ -> 0\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);

        assert_eq!(rendered_type(&rendered, "f"), "⊤ -> int");
        assert!(
            lowered.state.ctx.refs.unresolved().is_empty(),
            "catch guard should see shorthand pattern local, got unresolved refs: {:?}",
            lowered.state.ctx.refs.unresolved()
        );
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
            rendered_type(&rendered, "shorthand_header"),
            "{flag: bool, width: α} -> α | int",
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
            rendered_type(&rendered, "case_shorthand_guard"),
            "{flag: bool, width: α} -> α | int",
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
fn source_loader_implicit_prelude_does_not_report_role_receiver_type_arg_as_value() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let lowered = lower_virtual_source_with_options(
            "my value = 0\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let diagnostics = crate::surface_diagnostic::collect_surface_diagnostics(&lowered.state);

        assert!(
            diagnostics
                .iter()
                .all(|diagnostic| diagnostic.message != "undefined name `container`"),
            "role receiver type argument should not be left as an unresolved value ref: {diagnostics:?}",
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
fn lowers_std_opt_and_result_unqualified_through_implicit_prelude() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my maybe: opt int = just 1\n\
             my converted: result int str = case maybe:\n\
               nil -> err \"empty\"\n\
               just x -> ok x\n\
             my recovered: int = case converted:\n\
               err _ -> 0\n\
               ok x -> x\n\
             my mapped: result int str = converted.map (\\x -> x + 1)\n\
             my chained: result int str = converted.and_then (\\x -> ok (x + 1))\n\
             my unwrapped: int = converted.unwrap_or 0\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);

        assert_eq!(rendered_type(&rendered, "maybe"), "std::opt::opt<int>");
        assert_eq!(
            rendered_type(&rendered, "converted"),
            "std::result::result<int, std::str::str>"
        );
        assert_eq!(rendered_type(&rendered, "recovered"), "int");
        assert_eq!(
            rendered_type(&rendered, "mapped"),
            "std::result::result<int, std::str::str>"
        );
        assert_eq!(
            rendered_type(&rendered, "chained"),
            "std::result::result<int, std::str::str>"
        );
        assert_eq!(rendered_type(&rendered, "unwrapped"), "int");
    });
}

#[test]
fn lowers_std_undet_entrypoints_through_implicit_prelude() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my e = each\n\
             my g = guard\n\
             my collected = (each [1, 2, 3] + each [4, 5, 6]).list\n",
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
        assert_eq!(
            rendered_type(&rendered, "g"),
            "bool -> [std::undet::undet] unit"
        );
        assert_eq!(
            rendered_type(&rendered, "collected"),
            "std::list::list<int>"
        );
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
             my take_first_method(xs: list int) = xs.first\n\
             my take_last(xs: list int) = xs.last\n\
             my take_rev(xs: list int) = rev xs\n\
             my take_rev_method(xs: list int) = xs.rev\n\
             my take_sort_method(xs: list int) = xs.sort\n\
             my take_index(xs: list int) = xs.index 0\n\
             my take_index_bracket(xs: list int) = xs[0]\n\
             my take_map(xs: list int, f: int -> int) = map xs f\n\
             my take_filter(xs: list int, pred: int -> bool) = filter xs pred\n\
             my take_filter_method(xs: list int, pred: int -> bool) = xs.filter pred\n\
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
            rendered_type(&rendered, "take_first_method"),
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
            rendered_type(&rendered, "take_rev_method"),
            "std::list::list<int> -> std::list::list<int>"
        );
        assert_eq!(
            rendered_type(&rendered, "take_sort_method"),
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
            rendered_type(&rendered, "take_filter_method"),
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
fn scoped_formatter_shortens_std_list_paths_in_prelude_scope() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my take_first(xs: list int) = first xs\n\
             my take_rev(xs: list int) = rev xs\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        lowered.state.finalize_compact_results();

        for (name, expected) in [
            ("take_first", "list<int> -> opt<int>"),
            ("take_rev", "list<int> -> list<int>"),
        ] {
            let def = lowered
                .state
                .ctx
                .resolve_value(&Name(name.to_string()))
                .unwrap_or_else(|| panic!("{name} should resolve"));
            let scheme = lowered
                .state
                .compact_scheme_of(def)
                .unwrap_or_else(|| panic!("{name} should have a compact scheme"));
            let rendered = crate::display::format::format_coalesced_scheme_in_scope(
                &scheme,
                &lowered.state.ctx,
            );
            assert_eq!(rendered, expected, "scoped render for {name}");
        }
    });
}

#[test]
fn role_input_coalesce_removes_concrete_residual_vars() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            r#"my $pos: int = 0
my $committed: bool = false

my loop(n: int): int =
    if n == 0:
        $pos
    else:
        &committed = true
        loop (n - 1)
"#,
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        lowered.state.finalize_compact_results();

        let def = lowered
            .state
            .ctx
            .resolve_value(&Name("loop".to_string()))
            .expect("loop should resolve");
        let scheme = lowered
            .state
            .compact_scheme_of(def)
            .expect("loop should have a compact scheme");
        let rendered =
            crate::display::format::format_coalesced_scheme_in_scope(&scheme, &lowered.state.ctx);
        assert_eq!(rendered, "int -> int");
        assert!(
            lowered
                .state
                .infer
                .compact_role_constraints_of(def)
                .is_empty()
        );
    });
}

#[test]
fn operator_use_spans_record_resolved_def_for_hover() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let source = "my add_ints(x: int, y: int) = x + y\n";
        let lowered = lower_virtual_source_with_options(
            source,
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();

        let plus_offset = source.find('+').expect("source should contain +");
        let plus_byte = u32::try_from(plus_offset).unwrap();
        let plus_range = rowan::TextRange::new(plus_byte.into(), (plus_byte + 1).into());

        let span_hit = lowered
            .state
            .value_use_spans
            .iter()
            .find(|(span, _)| {
                span.range.start() <= plus_range.start() && plus_range.end() <= span.range.end()
            })
            .expect("hover on + should find a value_use_span");

        let (_, def) = span_hit;
        let name = lowered
            .state
            .def_name(*def)
            .expect("operator def should have a name");
        let def_id = *def;
        assert_eq!(name.0, "+", "+ should resolve to the infix operator def");
        assert!(
            lowered.state.compact_scheme_of(def_id).is_some(),
            "operator def should have a compact scheme available for hover",
        );

        let paths = lowered
            .state
            .ctx
            .collect_all_binding_paths()
            .into_iter()
            .filter(|(_, current)| *current == def_id)
            .collect::<Vec<_>>();
        assert!(
            !paths.is_empty(),
            "operator def should have at least one binding path"
        );
        let labels: Vec<String> = crate::display::collect_compact_results_for_paths_in_scope(
            &lowered.state,
            &paths,
            &lowered.state.ctx,
        )
        .into_iter()
        .map(|(label, _)| label)
        .collect();
        assert!(
            labels.iter().any(|label| label == "+"),
            "scoped label for + operator should render as `+`, got: {labels:?}",
        );
    });
}

#[test]
fn var_binding_records_def_span_and_use_span_for_sigil_read() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let source = "{ my $x = 1\n  $x + 1\n}\n";
        let lowered = lower_virtual_source_with_options(
            source,
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();

        let first_x = source.find("$x").expect("first $x");
        let first_x_range =
            rowan::TextRange::new((first_x as u32).into(), ((first_x + 2) as u32).into());

        // The def_span for the var should land on the first `$x` token.
        let (&def, _span) = lowered
            .state
            .def_spans
            .iter()
            .find(|(_, span)| {
                span.range.start() <= first_x_range.start()
                    && first_x_range.end() <= span.range.end()
            })
            .expect("first $x should have a def_span entry");
        assert_eq!(
            lowered
                .state
                .def_name(def)
                .map(|n| n.0.clone())
                .unwrap_or_default(),
            "#x",
            "def_span owner should be the #x init binding",
        );

        // The second `$x` should be in value_use_spans pointing to the same def.
        let second_x = source.rfind("$x").expect("second $x");
        let second_x_range =
            rowan::TextRange::new((second_x as u32).into(), ((second_x + 2) as u32).into());
        let matches: Vec<_> = lowered
            .state
            .value_use_spans
            .iter()
            .filter(|(span, candidate)| {
                *candidate == def
                    && span.range.start() <= second_x_range.start()
                    && second_x_range.end() <= span.range.end()
            })
            .collect();
        assert!(
            !matches.is_empty(),
            "second $x should be recorded as a value_use_span of &x"
        );
    });
}

#[test]
fn def_spans_record_origin_file_for_std_each() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let lowered = lower_virtual_source_with_options(
            "my a = each [1, 2, 3]\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();

        // After lowering completes the entry-level use_search is empty, so look up `each`
        // by walking the canonical binding paths instead of resolving from the user module.
        let each_def = lowered
            .state
            .ctx
            .collect_all_binding_paths()
            .into_iter()
            .find(|(path, _)| {
                path.segments
                    .iter()
                    .map(|name| name.0.as_str())
                    .eq(["std", "undet", "each"].into_iter())
            })
            .map(|(_, def)| def)
            .expect("std::undet::each binding path should exist");
        let def_span = lowered
            .state
            .def_spans
            .get(&each_def)
            .copied()
            .expect("each should have a def_span recorded in its source file");
        let info = lowered
            .state
            .file_info(def_span.file)
            .expect("def_span should point at a registered file");
        assert_eq!(info.origin, yulang_sources::SourceOrigin::Std);
        let path_text = info.path.to_string_lossy().into_owned();
        assert!(
            path_text.ends_with("std/undet.yu") || path_text.ends_with("std\\undet.yu"),
            "each should be defined in std::undet, got file {:?}",
            info.path,
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
            "std::list::list<α> -> β -> (β -> [γ] α -> [γ] β) -> [γ] β"
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
                 undet::reject()\n\
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
fn undet_logic_reference_keeps_result_item_var() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "use std::undet::*\n\
             my l = undet::logic\n",
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
             my once_value = (each [1, 2, 3] + each [4, 5, 6]).once\n\
             my direct_list = (each [1, 2, 3]).list\n\
             my direct_once = (each [1, 2, 3]).once\n",
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
        assert_eq!(
            rendered_type(&rendered, "direct_list"),
            "std::list::list<int | α>"
        );
        assert_eq!(
            rendered_type(&rendered, "direct_once"),
            "std::opt::opt<int | α>"
        );
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
fn records_expected_edges_for_if_conditions_and_branches() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let lowered = lower_virtual_source_with_options(
            "my f(x: bool) = if x { 1 } else { 0 }",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        )
        .unwrap();

        let condition_edges = lowered
            .state
            .expected_edges
            .iter()
            .filter(|edge| edge.kind == ExpectedEdgeKind::IfCondition)
            .count();
        let branch_edges = lowered
            .state
            .expected_edges
            .iter()
            .filter(|edge| edge.kind == ExpectedEdgeKind::IfBranch)
            .count();

        assert_eq!(condition_edges, 1);
        assert_eq!(branch_edges, 2);

        let rendered_edges = collect_expected_edges(&lowered.state);
        assert!(
            rendered_edges
                .iter()
                .any(|edge| edge.contains("if-condition"))
        );
        assert!(rendered_edges.iter().any(|edge| edge.contains("if-branch")));
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
fn records_expected_edges_for_case_guards_and_branches() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let lowered = lower_virtual_source_with_options(
            "my f(x: bool) = case 1:\n  1 if x -> 1\n  _ -> 0\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        )
        .unwrap();

        let guard_edges = lowered
            .state
            .expected_edges
            .iter()
            .filter(|edge| edge.kind == ExpectedEdgeKind::MatchGuard)
            .count();
        let branch_edges = lowered
            .state
            .expected_edges
            .iter()
            .filter(|edge| edge.kind == ExpectedEdgeKind::MatchBranch)
            .count();

        assert_eq!(guard_edges, 1);
        assert_eq!(branch_edges, 2);
    });
}

#[test]
fn lowers_constant_case_guards() {
    fn strip_expected_boundary(expr: &crate::ast::expr::TypedExpr) -> &crate::ast::expr::TypedExpr {
        match &expr.kind {
            crate::ast::expr::ExprKind::Coerce { expr, .. } => strip_expected_boundary(expr),
            _ => expr,
        }
    }

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
                    strip_expected_boundary(&arms[0].body).kind,
                    crate::ast::expr::ExprKind::Lit(crate::ast::expr::Lit::Int(ref value))
                        if value == "1"
                ));
                assert!(matches!(
                    strip_expected_boundary(&arms[1].body).kind,
                    crate::ast::expr::ExprKind::Lit(crate::ast::expr::Lit::Int(ref value))
                        if value == "0"
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
fn records_expected_edges_for_catch_guards_and_branches() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let lowered = lower_virtual_source_with_options(
            "my f(x: bool) = catch 1:\n  n if x -> n\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        )
        .unwrap();

        let guard_edges = lowered
            .state
            .expected_edges
            .iter()
            .filter(|edge| edge.kind == ExpectedEdgeKind::CatchGuard)
            .count();
        let branch_edges = lowered
            .state
            .expected_edges
            .iter()
            .filter(|edge| edge.kind == ExpectedEdgeKind::CatchBranch)
            .count();

        assert_eq!(guard_edges, 1);
        assert_eq!(branch_edges, 1);
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
        assert_eq!(rendered_type(&rendered, "first"), "std::char::char");
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
fn lowers_forward_act_helper_after_inline_for_body() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my first_over limit = route::route:\n\
                for x in 0..: if x * x > limit: route::ret x\n\
                route::ret 0\n\n\
             first_over 1\n\n\
             pub act route 'a:\n\
                pub ret: 'a -> never\n\
                pub route(x: [_] 'a): 'a = catch x:\n\
                    ret a, _ -> a\n\
                    a -> a\n",
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
            "forward act helper after inline for body should lower without type errors, got {:?}",
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

#[test]
fn header_lambda_does_not_move_prior_argument_effect_to_next_argument() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "our hold(x: [_] _, y) = (x, y)\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        assert_eq!(rendered_type(&rendered, "hold"), "α [γ] -> β -> [γ] (α, β)");
    });
}

#[test]
fn multi_argument_handler_subtracts_handled_effect_with_result_annotation() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "pub act out:\n  pub say: str -> ()\n\n\
             our listen(x: [_] _, log: str): (_, str) = catch x:\n  out::say o, k -> listen(k (), log + o + \"\\n\")\n  v -> (v, log)\n",
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
            rendered_type(&rendered, "listen"),
            "α [out; β] -> std::str::str -> [β] (α, std::str::str)"
        );
    });
}

#[test]
fn unannotated_second_header_arg_stays_value_arg_after_effectful_first_arg() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "pub act out:\n  pub say: str -> ()\n\n\
             our listen(x: [_] _, log) = catch x:\n  out::say o, k -> listen(k (), log + o + \"\\n\")\n  v -> (v, log)\n",
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
            rendered_type(&rendered, "listen"),
            "Add<std::str::str | β> => α [out; δ] -> β -> [δ] γ | (α, β | std::str::str)"
        );
    });
}

#[test]
fn fail_with_concrete_error_carries_throw_effect() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my raise_concrete(e: fs_err) = fail e\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let rendered = render_compact_results(&mut lowered.state);
        let ty = rendered_type(&rendered, "raise_concrete");
        assert!(
            ty.contains("std::fs::fs_err"),
            "raise_concrete should carry fs_err in its effect row, got: {ty}"
        );
    });
}

#[test]
fn runtime_export_closes_monomorphic_bindings_with_open_display_vars() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my fact (n: int) : int =\n  if n <= 1: 1\n  else: n * fact (n - 1)\n\n\
             my add (x: int) (y: int) : int = x + y\n\
             my add5 = add 5\n\
             my pair = (1, \"hello\")\n\
             fact 5\n\
             add5 10\n\
             case pair:\n  (n, s) -> s + \" \" + (n).show\n",
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
        let fact = rendered_type(&rendered, "fact");
        let add = rendered_type(&rendered, "add");
        assert!(
            fact.contains("int") && !fact.contains("Add") && !fact.contains('α'),
            "fact should be exported as a closed int function, got: {fact}"
        );
        assert!(
            add.contains("int") && !add.contains("Add") && !add.contains('α'),
            "add should be exported as a closed int function, got: {add}"
        );
        assert_eq!(rendered_type(&rendered, "pair"), "(int, std::str::str)");
    });
}

#[test]
fn principal_apply_evidence_fills_runtime_irrelevant_type_params() {
    run_with_large_stack(|| {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let std_root = repo_root.join("lib/std");
        let mut lowered = lower_virtual_source_with_options(
            "my xs = []\nxs.len\n",
            Some(repo_root),
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let program = crate::export_core_program(&mut lowered.state);
        let yulang_typed_ir::Expr::Apply {
            evidence: Some(evidence),
            ..
        } = &program.program.root_exprs[0]
        else {
            panic!("root should be an apply with principal evidence");
        };
        assert_eq!(evidence.substitutions.len(), 1);
        assert_eq!(
            evidence.substitutions[0].ty,
            yulang_typed_ir::Type::Tuple(Vec::new())
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
