//! Source-level compilation glue.
//!
//! This crate is intentionally above inference and native codegen.  It owns
//! adapters that need both crates, so `yulang-native` can stay focused on
//! runtime IR and backend lowering.

use std::fmt;
use std::path::PathBuf;

pub use yulang_sources::{SourceLoadError, SourceOptions};

pub type SourceRuntimeResult<T> = Result<T, SourceRuntimeError>;

#[derive(Debug)]
pub enum SourceRuntimeError {
    SourceLoad(SourceLoadError),
    SurfaceDiagnostics(Vec<String>),
    RuntimeLower(yulang_runtime::RuntimeError),
}

impl fmt::Display for SourceRuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SourceRuntimeError::SourceLoad(error) => write!(f, "{error}"),
            SourceRuntimeError::SurfaceDiagnostics(messages) => {
                write!(f, "{}", messages.join("\n"))
            }
            SourceRuntimeError::RuntimeLower(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for SourceRuntimeError {}

impl From<SourceLoadError> for SourceRuntimeError {
    fn from(error: SourceLoadError) -> Self {
        SourceRuntimeError::SourceLoad(error)
    }
}

impl From<yulang_runtime::RuntimeError> for SourceRuntimeError {
    fn from(error: yulang_runtime::RuntimeError) -> Self {
        SourceRuntimeError::RuntimeLower(error)
    }
}

pub fn runtime_module_from_virtual_source_with_options(
    source: &str,
    base_dir: Option<PathBuf>,
    options: SourceOptions,
) -> SourceRuntimeResult<yulang_runtime::Module> {
    let mut lowered = yulang_infer::lower_virtual_source_with_options(source, base_dir, options)?;
    runtime_module_from_lowered_sources(&mut lowered)
}

pub fn runtime_module_from_lowered_sources(
    lowered: &mut yulang_infer::LoweredSources,
) -> SourceRuntimeResult<yulang_runtime::Module> {
    let diagnostics = yulang_infer::collect_surface_diagnostics(&lowered.state);
    if !diagnostics.is_empty() {
        return Err(SourceRuntimeError::SurfaceDiagnostics(
            diagnostics
                .into_iter()
                .map(|diagnostic| diagnostic.message)
                .collect(),
        ));
    }
    let program = yulang_infer::export_core_program(&mut lowered.state);
    yulang_runtime::lower_core_program(program)
        .and_then(yulang_runtime::monomorphize_module)
        .map_err(SourceRuntimeError::from)
}

pub type NativeSourceResult<T> = Result<T, NativeSourceError>;

#[derive(Debug)]
pub enum NativeSourceError {
    Compile(SourceRuntimeError),
    NativeLower(yulang_native::NativeLowerError),
    NativeEval(yulang_native::NativeEvalError),
    Cranelift(yulang_native::NativeCraneliftError),
    ValueCranelift(yulang_native::NativeValueCraneliftError),
    CpsReprCranelift(yulang_native::CpsReprCraneliftError),
    CpsCompare(yulang_native::CpsCompareError),
    NativeCompare(yulang_native::NativeSourceCompareError),
}

impl fmt::Display for NativeSourceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NativeSourceError::Compile(error) => write!(f, "{error}"),
            NativeSourceError::NativeLower(error) => write!(f, "{error}"),
            NativeSourceError::NativeEval(error) => write!(f, "{error}"),
            NativeSourceError::Cranelift(error) => write!(f, "{error}"),
            NativeSourceError::ValueCranelift(error) => write!(f, "{error}"),
            NativeSourceError::CpsReprCranelift(error) => write!(f, "{error}"),
            NativeSourceError::CpsCompare(error) => write!(f, "{error}"),
            NativeSourceError::NativeCompare(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for NativeSourceError {}

impl From<SourceRuntimeError> for NativeSourceError {
    fn from(error: SourceRuntimeError) -> Self {
        NativeSourceError::Compile(error)
    }
}

impl From<yulang_native::NativeLowerError> for NativeSourceError {
    fn from(error: yulang_native::NativeLowerError) -> Self {
        NativeSourceError::NativeLower(error)
    }
}

impl From<yulang_native::NativeEvalError> for NativeSourceError {
    fn from(error: yulang_native::NativeEvalError) -> Self {
        NativeSourceError::NativeEval(error)
    }
}

impl From<yulang_native::NativeCraneliftError> for NativeSourceError {
    fn from(error: yulang_native::NativeCraneliftError) -> Self {
        NativeSourceError::Cranelift(error)
    }
}

impl From<yulang_native::NativeValueCraneliftError> for NativeSourceError {
    fn from(error: yulang_native::NativeValueCraneliftError) -> Self {
        NativeSourceError::ValueCranelift(error)
    }
}

impl From<yulang_native::CpsReprCraneliftError> for NativeSourceError {
    fn from(error: yulang_native::CpsReprCraneliftError) -> Self {
        NativeSourceError::CpsReprCranelift(error)
    }
}

impl From<yulang_native::CpsCompareError> for NativeSourceError {
    fn from(error: yulang_native::CpsCompareError) -> Self {
        NativeSourceError::CpsCompare(error)
    }
}

impl From<yulang_native::NativeSourceCompareError> for NativeSourceError {
    fn from(error: yulang_native::NativeSourceCompareError) -> Self {
        NativeSourceError::NativeCompare(error)
    }
}

pub fn compile_source_with_options(
    source: &str,
    options: SourceOptions,
) -> NativeSourceResult<yulang_native::NativeModule> {
    let module = runtime_module_from_virtual_source_with_options(source, None, options)?;
    yulang_native::lower_module(&module).map_err(NativeSourceError::from)
}

pub fn eval_source_with_options(
    source: &str,
    options: SourceOptions,
) -> NativeSourceResult<Vec<yulang_runtime::VmValue>> {
    let module = compile_source_with_options(source, options)?;
    yulang_native::eval_module(&module).map_err(NativeSourceError::from)
}

pub fn eval_source_i64_with_options(
    source: &str,
    options: SourceOptions,
) -> NativeSourceResult<Vec<i64>> {
    let native_module = compile_source_with_options(source, options)?;
    let closure_module = yulang_native::closure_convert_module(&native_module);
    let abi_module = yulang_native::lower_closure_module_to_abi(&closure_module);
    let mut jit = yulang_native::compile_abi_module(&abi_module)?;
    jit.run_roots_i64().map_err(NativeSourceError::from)
}

pub fn eval_source_value_lane_with_options(
    source: &str,
    options: SourceOptions,
) -> NativeSourceResult<Vec<yulang_runtime::VmValue>> {
    let runtime_module = runtime_module_from_virtual_source_with_options(source, None, options)?;
    let native_module = yulang_native::lower_module(&runtime_module)?;
    let closure_module = yulang_native::closure_convert_module(&native_module);
    let abi_module = yulang_native::lower_closure_module_to_abi(&closure_module);
    let mut jit = yulang_native::compile_value_abi_module(&abi_module)?;
    jit.run_roots().map_err(NativeSourceError::from)
}

pub fn compare_source_i64_with_options(
    source: &str,
    options: SourceOptions,
) -> NativeSourceResult<()> {
    let runtime_module = runtime_module_from_virtual_source_with_options(source, None, options)?;
    yulang_native::compare_module_i64(&runtime_module).map_err(NativeSourceError::from)
}

pub fn compare_source_cps_repr_i64_with_options(
    source: &str,
    options: SourceOptions,
) -> NativeSourceResult<()> {
    let runtime_module = runtime_module_from_virtual_source_with_options(source, None, options)?;
    yulang_native::compare_cps_repr_cranelift_i64(&runtime_module).map_err(NativeSourceError::from)
}

pub fn analyze_source_abi_reprs_with_options(
    source: &str,
    options: SourceOptions,
) -> NativeSourceResult<yulang_native::NativeAbiReprAnalysis> {
    let runtime_module = runtime_module_from_virtual_source_with_options(source, None, options)?;
    let native_module = yulang_native::lower_module(&runtime_module)?;
    let closure_module = yulang_native::closure_convert_module(&native_module);
    let abi_module = yulang_native::lower_closure_module_to_abi(&closure_module);
    Ok(yulang_native::analyze_abi_reprs(&abi_module))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn evaluates_literal_source_through_native_adapter() {
        let values = eval_source_with_options("41", SourceOptions::default()).expect("native eval");
        assert_eq!(values, vec![yulang_runtime::VmValue::Int("41".to_string())]);
    }

    #[test]
    fn compares_literal_source_through_scalar_paths() {
        compare_source_i64_with_options("41", SourceOptions::default()).expect("native compare");
    }

    #[test]
    fn runs_guarded_record_match_with_std_operator_through_value_lane() {
        assert_source_value_with_std(
            r#"
case {ok: true, n: 41}:
    {ok, n} if n < 50 -> n + 1
    _ -> 0
"#,
        )
        .expect("value lane native eval");
    }

    #[test]
    fn runs_branch_selected_closure_through_value_lane() {
        assert_source_value_with_std(
            r#"
my base = 40
my f = if true { \x -> x + base } else { \x -> x }
f 2
"#,
        )
        .expect("value lane native eval");
    }

    #[test]
    fn runs_partial_top_level_function_through_value_lane() {
        assert_source_value_with_std(
            r#"
my add x y = x + y
my f = add 40
f 2
"#,
        )
        .expect("value lane native eval");
    }

    #[test]
    fn runs_list_map_through_value_lane() {
        assert_source_value_text_with_std(
            r#"
[1, 2, 3].map (\x -> x + 1)
"#,
            "[[2, 3, 4]]",
        )
        .expect("value lane native eval");
    }

    #[test]
    fn runs_list_filter_through_value_lane() {
        assert_source_value_text_with_std(
            r#"
[1, 2, 3].filter (\x -> x < 3)
"#,
            "[[1, 2]]",
        )
        .expect("value lane native eval");
    }

    #[test]
    fn runs_list_fold_through_value_lane() {
        assert_source_value_text_with_std(
            r#"
[1, 2, 3].fold 0 (\acc x -> acc + x)
"#,
            "[6]",
        )
        .expect("value lane native eval");
    }

    #[test]
    fn compares_direct_nullary_return_call_through_cps_repr() {
        compare_source_cps_repr_with_std(
            r#"use std::flow::*

our f() = return 0

our g h = sub:
    f()
    return 1

sub:
    my b = g f
    2
"#,
        )
        .expect("CPS repr native compare");
    }

    #[test]
    fn compares_callback_return_hygiene_through_cps_repr() {
        compare_source_cps_repr_with_std(
            r#"use std::flow::*

our f() = return 0

our g h = sub:
    h()
    return 1

sub:
    my b = g f
    2
"#,
        )
        .expect("CPS repr native compare");
    }

    #[test]
    fn runs_direct_return_hygiene_result_through_cps_repr() {
        assert_source_cps_repr_display_with_std(
            r#"use std::flow::*

our f() = return 0

our g h = sub:
    f()
    return 1

sub:
    my b = g f
    2
"#,
            vec!["2"],
        )
        .expect("CPS repr native display");
    }

    #[test]
    fn runs_callback_return_hygiene_result_through_cps_repr() {
        assert_source_cps_repr_display_with_std(
            r#"use std::flow::*

our f() = return 0

our g h = sub:
    h()
    return 1

sub:
    my b = g f
    2
"#,
            vec!["0"],
        )
        .expect("CPS repr native display");
    }

    #[test]
    fn runs_indexed_callback_return_hygiene_result_through_cps_repr() {
        assert_source_cps_repr_display_with_std(
            r#"use std::flow::*

our f() = return 0

our g h = sub:
    my hs = [h]
    ((std::list::index_raw hs) 0)()
    return 1

sub:
    my b = g f
    2
"#,
            vec!["0"],
        )
        .expect("CPS repr native display");
    }

    #[test]
    fn runs_sub_return_binding_in_list_through_cps_repr() {
        assert_source_cps_repr_display_with_std(
            r#"use std::flow::*

my t = sub:
    return 7
    0

[t, t]
"#,
            vec!["[7, 7]"],
        )
        .expect("CPS repr native display");
    }

    #[test]
    fn runs_closure_from_record_through_cps_repr() {
        assert_source_cps_repr_display_with_std(
            r#"my f: int -> int = \x -> x + 1
my r = {call: f}
r.call 41
"#,
            vec!["42"],
        )
        .expect("CPS repr native display");
    }

    #[test]
    fn runs_captured_closure_from_record_through_cps_repr() {
        assert_source_cps_repr_display_with_std(
            r#"my base = 40
my f: int -> int = \x -> x + base
my r = {call: f}
r.call 2
"#,
            vec!["42"],
        )
        .expect("CPS repr native display");
    }

    #[test]
    fn runs_string_captured_closure_from_record_through_cps_repr() {
        assert_source_cps_repr_display_with_std(
            r#"my s = "x"
my f: str -> str = \x -> x + s
my r = {call: f}
r.call "hi"
"#,
            vec!["hix"],
        )
        .expect("CPS repr native display");
    }

    #[test]
    fn runs_closure_from_indexed_list_through_cps_repr() {
        assert_source_cps_repr_display_with_std(
            r#"my f: int -> int = \x -> x + 1
my fs = [f]
((std::list::index_raw fs) 0) 41
"#,
            vec!["42"],
        )
        .expect("CPS repr native display");
    }

    #[test]
    fn runs_captured_closure_from_indexed_list_through_cps_repr() {
        assert_source_cps_repr_display_with_std(
            r#"my base = 40
my f: int -> int = \x -> x + base
my fs = [f]
((std::list::index_raw fs) 0) 2
"#,
            vec!["42"],
        )
        .expect("CPS repr native display");
    }

    #[test]
    fn runs_string_captured_closure_from_indexed_list_through_cps_repr() {
        assert_source_cps_repr_display_with_std(
            r#"my s = "x"
my f: str -> str = \x -> x + s
my fs = [f]
((std::list::index_raw fs) 0) "hi"
"#,
            vec!["hix"],
        )
        .expect("CPS repr native display");
    }

    #[test]
    fn runs_lazy_operator_results_in_tuple_through_cps_repr() {
        assert_source_cps_repr_display_with_std(
            r#"(true or false, false or true)
"#,
            vec!["(1, 1)"],
        )
        .expect("CPS repr native display");
    }

    #[test]
    fn runs_lazy_operator_results_in_indexed_list_through_cps_repr() {
        assert_source_cps_repr_display_with_std(
            r#"my xs = [true or false, false or true]
(std::list::index_raw xs) 1
"#,
            vec!["1"],
        )
        .expect("CPS repr native display");
    }

    #[test]
    fn runs_lazy_operator_result_in_record_field_through_cps_repr() {
        assert_source_cps_repr_display_with_std(
            r#"my r = {ok: true or false}
r.ok
"#,
            vec!["1"],
        )
        .expect("CPS repr native display");
    }

    #[test]
    fn runs_lazy_operator_result_in_variant_payload_through_cps_repr() {
        assert_source_cps_repr_display_with_std(
            r#"case just (true or false):
    just value -> value
    nil -> false
"#,
            vec!["1"],
        )
        .expect("CPS repr native display");
    }

    #[test]
    fn runs_simple_undet_list_through_cps_repr() {
        assert_source_cps_repr_display_with_std(
            r#"use std::undet::*

(branch()).list
"#,
            vec!["[1, 0]"],
        )
        .expect("CPS repr native display");
    }

    #[test]
    fn runs_undet_logic_each_through_cps_repr() {
        assert_source_cps_repr_display_with_std(
            r#"use std::undet::*

(each [1, 2, 3]).logic
"#,
            vec!["[1, 2, 3]"],
        )
        .expect("CPS repr native display");
    }

    #[test]
    fn runs_undet_list_each_through_cps_repr() {
        assert_source_cps_repr_display_with_std(
            r#"use std::undet::*

(each [1, 2, 3]).list
"#,
            vec!["[1, 2, 3]"],
        )
        .expect("CPS repr native display");
    }

    #[test]
    fn runs_undet_list_nested_each_sum_through_cps_repr() {
        assert_source_cps_repr_display_with_std(
            r#"use std::undet::*

(each [1, 2, 3] + each [10, 20]).list
"#,
            vec!["[11, 21, 12, 22, 13, 23]"],
        )
        .expect("CPS repr native display");
    }

    #[test]
    fn runs_undet_logic_nested_each_sum_through_cps_repr() {
        assert_source_cps_repr_display_with_std(
            r#"use std::undet::*

(each [1, 2, 3] + each [10, 20]).logic
"#,
            vec!["[11, 12, 21, 13, 22, 23]"],
        )
        .expect("CPS repr native display");
    }

    #[test]
    fn runs_undet_once_nested_each_sum_through_cps_repr() {
        assert_source_cps_repr_display_with_std(
            r#"use std::undet::*

(each [1, 2, 3] + each [10, 20]).once
"#,
            vec![":just 11"],
        )
        .expect("CPS repr native display");
    }

    fn compare_source_cps_repr_with_std(source: &str) -> Result<(), String> {
        let source = source.to_string();
        run_with_large_stack(move || {
            let repo_root = repo_root();
            let module = runtime_module_from_virtual_source_with_options(
                &source,
                Some(repo_root),
                source_options_with_std(),
            )
            .map_err(|error| error.to_string())?;
            yulang_native::compare_cps_repr_cranelift_i64(&module)
                .map_err(|error| error.to_string())
        })
    }

    fn assert_source_cps_repr_display_with_std(
        source: &str,
        expected: Vec<&'static str>,
    ) -> Result<(), String> {
        let source = source.to_string();
        run_with_large_stack(move || {
            let repo_root = repo_root();
            let module = runtime_module_from_virtual_source_with_options(
                &source,
                Some(repo_root),
                source_options_with_std(),
            )
            .map_err(|error| error.to_string())?;
            let cps_module =
                yulang_native::lower_cps_module(&module).map_err(|error| error.to_string())?;
            let cps_values =
                yulang_native::eval_cps_module(&cps_module).map_err(|error| error.to_string())?;
            let cps_actual: Vec<String> = cps_values.iter().map(format_native_i64_value).collect();
            if cps_actual != expected {
                return Err(format!(
                    "unexpected CPS eval display result: {cps_actual:?}"
                ));
            }
            let cps_repr_module = yulang_native::lower_cps_repr_module(&cps_module);
            let cps_repr_values = yulang_native::eval_cps_repr_module(&cps_repr_module)
                .map_err(|error| error.to_string())?;
            let cps_repr_actual: Vec<String> = cps_repr_values
                .iter()
                .map(format_native_i64_value)
                .collect();
            if cps_repr_actual != expected {
                return Err(format!(
                    "unexpected CPS repr eval display result: {cps_repr_actual:?}"
                ));
            }
            let mut jit = yulang_native::compile_runtime_module_to_cps_repr_jit(&module)
                .map_err(|error| error.to_string())?;
            let actual = jit.run_roots_display().map_err(|error| error.to_string())?;
            if actual != expected {
                return Err(format!("unexpected CPS repr display result: {actual:?}"));
            }
            Ok(())
        })
    }

    fn assert_source_value_with_std(source: &str) -> Result<(), String> {
        assert_source_value_text_with_std(source, "[42]")
    }

    fn assert_source_value_text_with_std(
        source: &str,
        expected: &'static str,
    ) -> Result<(), String> {
        let source = source.to_string();
        run_with_large_stack(move || {
            let values = eval_source_value_lane_with_options(&source, source_options_with_std())
                .map_err(|error| error.to_string())?;
            let actual = format_values(&values);
            if actual != expected {
                return Err(format!("unexpected value-lane result: {actual}"));
            }
            Ok(())
        })
    }

    fn format_values(values: &[yulang_runtime::VmValue]) -> String {
        format!(
            "[{}]",
            values
                .iter()
                .map(format_value)
                .collect::<Vec<_>>()
                .join(", ")
        )
    }

    fn format_value(value: &yulang_runtime::VmValue) -> String {
        match value {
            yulang_runtime::VmValue::Int(value) | yulang_runtime::VmValue::Float(value) => {
                value.clone()
            }
            yulang_runtime::VmValue::String(value) => format!("{:?}", value.to_flat_string()),
            yulang_runtime::VmValue::Bool(value) => value.to_string(),
            yulang_runtime::VmValue::Unit => "()".to_string(),
            yulang_runtime::VmValue::List(items) => format!(
                "[{}]",
                items
                    .to_vec()
                    .iter()
                    .map(|item| format_value(item))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            other => format!("{other:?}"),
        }
    }

    fn format_native_i64_value(value: &yulang_runtime::VmValue) -> String {
        match value {
            yulang_runtime::VmValue::Bool(true) => "1".to_string(),
            yulang_runtime::VmValue::Bool(false) => "0".to_string(),
            yulang_runtime::VmValue::String(value) => value.to_flat_string(),
            yulang_runtime::VmValue::Tuple(items) => format!(
                "({})",
                items
                    .iter()
                    .map(format_native_i64_value)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            yulang_runtime::VmValue::List(items) => format!(
                "[{}]",
                items
                    .to_vec()
                    .iter()
                    .map(|item| format_native_i64_value(item))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            yulang_runtime::VmValue::Variant { tag, value } => match value {
                Some(value) => format!(":{} {}", tag.0, format_native_i64_value(value.as_ref())),
                None => format!(":{}", tag.0),
            },
            other => format_value(other),
        }
    }

    fn source_options_with_std() -> SourceOptions {
        let repo_root = repo_root();
        SourceOptions {
            std_root: Some(repo_root.join("lib/std")),
            implicit_prelude: true,
            search_paths: Vec::new(),
        }
    }

    fn repo_root() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
    }

    fn run_with_large_stack<T, F>(f: F) -> T
    where
        T: Send + 'static,
        F: FnOnce() -> T + Send + 'static,
    {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(f)
            .expect("spawned large-stack test thread")
            .join()
            .expect("large-stack test thread finished")
    }
}
