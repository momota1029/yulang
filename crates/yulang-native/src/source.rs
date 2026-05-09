//! Source-string entrypoints for the native backend.
//!
//! The native backend itself still starts from `runtime::Module`.  This module
//! is a thin experimental adapter used by tests and local tooling that want to
//! start from Yulang source text without copying the frontend pipeline.

use std::fmt;
use std::path::PathBuf;

use yulang_infer as infer;
use yulang_runtime as runtime;

use crate::abi::lower_closure_module_to_abi;
use crate::abi_lane::{NativeAbiReprAnalysis, analyze_abi_reprs};
use crate::closure::closure_convert_module;
use crate::control_ir::NativeModule;
use crate::cps_compare::CpsCompareError;
use crate::cps_repr_cranelift::{CpsReprCraneliftError, compile_runtime_module_to_cps_repr_jit};
use crate::cranelift::{
    NativeCraneliftError, NativeObjectModule, compile_abi_module, compile_abi_module_to_object,
};
use crate::eval::{NativeEvalError, eval_module};
use crate::lower::{NativeLowerError, lower_module};
use crate::value_cranelift::{
    NativeValueCraneliftError, NativeValueObjectModule, compile_value_abi_module,
    compile_value_abi_module_to_object,
};

pub type NativeSourceResult<T> = Result<T, NativeSourceError>;

#[derive(Debug)]
pub enum NativeSourceError {
    SourceLoad(infer::SourceLoadError),
    SurfaceDiagnostics(Vec<String>),
    RuntimeLower(runtime::RuntimeError),
    NativeLower(NativeLowerError),
    NativeEval(NativeEvalError),
    Cranelift(NativeCraneliftError),
    ValueCranelift(NativeValueCraneliftError),
    CpsReprCranelift(CpsReprCraneliftError),
    CpsCompare(CpsCompareError),
}

impl fmt::Display for NativeSourceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NativeSourceError::SourceLoad(error) => write!(f, "{error}"),
            NativeSourceError::SurfaceDiagnostics(messages) => {
                write!(f, "{}", messages.join("\n"))
            }
            NativeSourceError::RuntimeLower(error) => write!(f, "{error}"),
            NativeSourceError::NativeLower(error) => write!(f, "{error}"),
            NativeSourceError::NativeEval(error) => write!(f, "{error}"),
            NativeSourceError::Cranelift(error) => write!(f, "{error}"),
            NativeSourceError::ValueCranelift(error) => write!(f, "{error}"),
            NativeSourceError::CpsReprCranelift(error) => write!(f, "{error}"),
            NativeSourceError::CpsCompare(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for NativeSourceError {}

impl From<infer::SourceLoadError> for NativeSourceError {
    fn from(error: infer::SourceLoadError) -> Self {
        NativeSourceError::SourceLoad(error)
    }
}

impl From<runtime::RuntimeError> for NativeSourceError {
    fn from(error: runtime::RuntimeError) -> Self {
        NativeSourceError::RuntimeLower(error)
    }
}

impl From<NativeLowerError> for NativeSourceError {
    fn from(error: NativeLowerError) -> Self {
        NativeSourceError::NativeLower(error)
    }
}

impl From<NativeEvalError> for NativeSourceError {
    fn from(error: NativeEvalError) -> Self {
        NativeSourceError::NativeEval(error)
    }
}

impl From<NativeCraneliftError> for NativeSourceError {
    fn from(error: NativeCraneliftError) -> Self {
        NativeSourceError::Cranelift(error)
    }
}

impl From<NativeValueCraneliftError> for NativeSourceError {
    fn from(error: NativeValueCraneliftError) -> Self {
        NativeSourceError::ValueCranelift(error)
    }
}

impl From<CpsReprCraneliftError> for NativeSourceError {
    fn from(error: CpsReprCraneliftError) -> Self {
        NativeSourceError::CpsReprCranelift(error)
    }
}

impl From<CpsCompareError> for NativeSourceError {
    fn from(error: CpsCompareError) -> Self {
        NativeSourceError::CpsCompare(error)
    }
}

pub fn compile_source(source: &str) -> NativeSourceResult<NativeModule> {
    compile_source_with_options(source, native_default_source_options())
}

pub fn compile_source_with_options(
    source: &str,
    options: infer::SourceOptions,
) -> NativeSourceResult<NativeModule> {
    let module = runtime_module_from_source_with_options(source, options)?;
    lower_module(&module).map_err(NativeSourceError::from)
}

pub fn eval_source(source: &str) -> NativeSourceResult<Vec<runtime::VmValue>> {
    eval_source_with_options(source, native_default_source_options())
}

pub fn eval_source_with_options(
    source: &str,
    options: infer::SourceOptions,
) -> NativeSourceResult<Vec<runtime::VmValue>> {
    let module = compile_source_with_options(source, options)?;
    eval_module(&module).map_err(NativeSourceError::from)
}

pub fn eval_source_i64(source: &str) -> NativeSourceResult<Vec<i64>> {
    eval_source_i64_with_options(source, native_default_source_options())
}

pub fn eval_source_i64_with_options(
    source: &str,
    options: infer::SourceOptions,
) -> NativeSourceResult<Vec<i64>> {
    let native_module = compile_source_with_options(source, options)?;
    let closure_module = closure_convert_module(&native_module);
    let abi_module = lower_closure_module_to_abi(&closure_module);
    let mut jit = compile_abi_module(&abi_module)?;
    jit.run_roots_i64().map_err(NativeSourceError::from)
}

pub fn compile_source_object(source: &str) -> NativeSourceResult<NativeObjectModule> {
    compile_source_object_with_options(source, native_default_source_options())
}

pub fn compile_source_object_with_options(
    source: &str,
    options: infer::SourceOptions,
) -> NativeSourceResult<NativeObjectModule> {
    let native_module = compile_source_with_options(source, options)?;
    let closure_module = closure_convert_module(&native_module);
    let abi_module = lower_closure_module_to_abi(&closure_module);
    compile_abi_module_to_object(&abi_module).map_err(NativeSourceError::from)
}

pub fn eval_source_value_lane(source: &str) -> NativeSourceResult<Vec<runtime::VmValue>> {
    eval_source_value_lane_with_options(source, native_default_source_options())
}

pub fn eval_source_value_lane_with_options(
    source: &str,
    options: infer::SourceOptions,
) -> NativeSourceResult<Vec<runtime::VmValue>> {
    let runtime_module = runtime_module_from_source_with_options(source, options)?;
    let native_module = lower_module(&runtime_module)?;
    let closure_module = closure_convert_module(&native_module);
    let abi_module = lower_closure_module_to_abi(&closure_module);
    let mut jit = compile_value_abi_module(&abi_module)?;
    jit.run_roots().map_err(NativeSourceError::from)
}

pub fn compile_source_value_object(source: &str) -> NativeSourceResult<NativeValueObjectModule> {
    compile_source_value_object_with_options(source, native_default_source_options())
}

pub fn compile_source_value_object_with_options(
    source: &str,
    options: infer::SourceOptions,
) -> NativeSourceResult<NativeValueObjectModule> {
    let runtime_module = runtime_module_from_source_with_options(source, options)?;
    let native_module = lower_module(&runtime_module)?;
    let closure_module = closure_convert_module(&native_module);
    let abi_module = lower_closure_module_to_abi(&closure_module);
    compile_value_abi_module_to_object(&abi_module).map_err(NativeSourceError::from)
}

pub fn eval_source_cps_repr_i64(source: &str) -> NativeSourceResult<Vec<i64>> {
    eval_source_cps_repr_i64_with_options(source, native_default_source_options())
}

pub fn eval_source_cps_repr_i64_with_options(
    source: &str,
    options: infer::SourceOptions,
) -> NativeSourceResult<Vec<i64>> {
    let runtime_module = runtime_module_from_source_with_options(source, options)?;
    let mut jit = compile_runtime_module_to_cps_repr_jit(&runtime_module)?;
    jit.run_roots_i64().map_err(NativeSourceError::from)
}

pub fn compare_source_cps_repr_i64(source: &str) -> NativeSourceResult<()> {
    compare_source_cps_repr_i64_with_options(source, native_default_source_options())
}

pub fn compare_source_cps_repr_i64_with_options(
    source: &str,
    options: infer::SourceOptions,
) -> NativeSourceResult<()> {
    let runtime_module = runtime_module_from_source_with_options(source, options)?;
    crate::cps_compare::compare_cps_repr_cranelift_i64(&runtime_module)
        .map_err(NativeSourceError::from)
}

pub fn analyze_source_abi_reprs(source: &str) -> NativeSourceResult<NativeAbiReprAnalysis> {
    analyze_source_abi_reprs_with_options(source, native_default_source_options())
}

pub fn analyze_source_abi_reprs_with_options(
    source: &str,
    options: infer::SourceOptions,
) -> NativeSourceResult<NativeAbiReprAnalysis> {
    let runtime_module = runtime_module_from_source_with_options(source, options)?;
    let native_module = lower_module(&runtime_module)?;
    let closure_module = closure_convert_module(&native_module);
    let abi_module = lower_closure_module_to_abi(&closure_module);
    Ok(analyze_abi_reprs(&abi_module))
}

pub fn runtime_module_from_source_with_options(
    source: &str,
    options: infer::SourceOptions,
) -> NativeSourceResult<runtime::Module> {
    let mut lowered = infer::lower_virtual_source_with_options(source, None, options)?;
    let diagnostics = infer::collect_surface_diagnostics(&lowered.state);
    if !diagnostics.is_empty() {
        return Err(NativeSourceError::SurfaceDiagnostics(
            diagnostics
                .into_iter()
                .map(|diagnostic| diagnostic.message)
                .collect(),
        ));
    }
    let program = infer::export_core_program(&mut lowered.state);
    runtime::lower_core_program(program)
        .and_then(runtime::monomorphize_module)
        .map_err(NativeSourceError::from)
}

pub fn native_default_source_options() -> infer::SourceOptions {
    let std_root = default_std_root();
    infer::SourceOptions {
        implicit_prelude: std_root.is_some(),
        std_root,
        search_paths: Vec::new(),
    }
}

fn default_std_root() -> Option<PathBuf> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../lib/std");
    root.is_dir().then_some(root)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use crate::{NativeAbiRepr, NativeAbiValueLane, NativeRuntimePtrKind};

    use super::*;

    #[test]
    fn evals_literal_source_string() {
        let values = eval_source_with_options("41", infer::SourceOptions::default())
            .expect("native source eval");
        assert_eq!(values, vec![runtime::VmValue::Int("41".to_string())]);
    }

    #[test]
    fn evals_literal_source_string_through_cranelift_scalar_path() {
        let values = eval_source_i64_with_options("41", infer::SourceOptions::default())
            .expect("native source jit eval");
        assert_eq!(values, vec![41]);
    }

    #[test]
    fn emits_literal_source_object() {
        let object = compile_source_object_with_options("41", infer::SourceOptions::default())
            .expect("native source object compile");
        assert!(!object.bytes().is_empty());
    }

    #[test]
    fn evals_literal_source_through_cps_repr_cranelift() {
        let values = eval_source_cps_repr_i64_with_options("41", infer::SourceOptions::default())
            .expect("native CPS repr jit eval");
        assert_eq!(values, vec![41]);
    }

    #[test]
    fn evals_prelude_source_through_cps_repr_cranelift() {
        let values = run_with_large_stack(|| {
            eval_source_cps_repr_i64("41").expect("native CPS repr jit eval with prelude")
        });
        assert_eq!(values, vec![41]);
    }

    #[test]
    fn compares_source_effect_handler_through_cps_repr_cranelift() {
        compare_source_cps_repr_i64_with_options(
            r#"pub act choose:
  pub pick: int -> int

catch choose::pick 41:
    choose::pick x, k -> k x
"#,
            infer::SourceOptions::default(),
        )
        .expect("source CPS repr jit compare");
    }

    #[test]
    fn compares_source_value_handler_arm_through_cps_repr_cranelift() {
        compare_source_cps_repr_i64_with_options(
            r#"catch 31:
    value -> 41
"#,
            infer::SourceOptions::default(),
        )
        .expect("source CPS repr jit compare");
    }

    #[test]
    fn compares_source_resume_result_outside_value_arm_through_cps_repr_cranelift() {
        compare_source_cps_repr_i64_with_options(
            r#"pub act choose:
  pub pick: int -> int

catch choose::pick 31:
    choose::pick x, k -> k x
    value -> 41
"#,
            infer::SourceOptions::default(),
        )
        .expect("source CPS repr jit compare");
    }

    #[test]
    fn compares_prelude_source_effect_handler_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choose:
  pub pick: int -> int

catch choose::pick 41:
    choose::pick x, k -> k x
"#,
            )
            .expect("source CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_prelude_source_multishot_effect_handler_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choose:
  pub pick: int -> int

catch choose::pick 41:
    choose::pick x, k -> k 1 + k 2
"#,
            )
            .expect("source multishot CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_prelude_source_handler_arm_direct_call_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choose:
  pub pick: int -> int

my id x = x

catch choose::pick 41:
    choose::pick x, k -> id (k x)
"#,
            )
            .expect("source handler direct-call CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_prelude_source_handler_arm_block_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choose:
  pub pick: int -> int

catch choose::pick 41:
    choose::pick x, k ->
        my y = k x
        y + 1
"#,
            )
            .expect("source handler block CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_prelude_source_effect_inside_primitive_arg_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choose:
  pub pick: int -> int

catch choose::pick 1 + 2:
    choose::pick x, k -> k x
"#,
            )
            .expect("source effect-in-primitive CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_prelude_source_handler_value_arm_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choose:
  pub pick: int -> int

catch choose::pick 41:
    choose::pick x, k -> k x
    value -> value + 1
"#,
            )
            .expect("source handler value-arm CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_prelude_source_handler_arm_bool_if_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choose:
  pub pick: int -> int

catch choose::pick 41:
    choose::pick x, k -> if true: k x else: k x + 1
"#,
            )
            .expect("source handler bool-if CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_prelude_source_handler_arm_comparison_if_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choose:
  pub pick: int -> int

catch choose::pick 41:
    choose::pick x, k -> if x < 0: k x else: k x + 1
"#,
            )
            .expect("source handler comparison-if CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_prelude_source_handler_arm_or_if_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choose:
  pub pick: int -> int

catch choose::pick 41:
    choose::pick x, k -> if x < 0 or x == 0: k x else: k x + 1
"#,
            )
            .expect("source handler or-if CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_prelude_source_handler_arm_and_if_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choose:
  pub pick: int -> int

catch choose::pick 41:
    choose::pick x, k -> if x < 0 and x == 0: k x else: k x + 1
"#,
            )
            .expect("source handler and-if CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_prelude_source_handler_arm_not_if_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choose:
  pub pick: int -> int

catch choose::pick 41:
    choose::pick x, k -> if not (x < 0): k x else: k x + 1
"#,
            )
            .expect("source handler not-if CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_prelude_source_handler_arm_nested_if_condition_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choose:
  pub pick: int -> int

catch choose::pick 41:
    choose::pick x, k -> if if x < 0: false else: true: k x else: k x + 1
"#,
            )
            .expect("source handler nested-if condition CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_prelude_source_handler_arm_let_condition_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choose:
  pub pick: int -> int

catch choose::pick 41:
    choose::pick x, k ->
        my c = x < 0 or x == 0
        if c: k x else: k x + 1
"#,
            )
            .expect("source handler let condition CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_std_sub_return_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64("std::flow::sub::sub { std::flow::sub::return 41 }")
                .expect("std sub return CPS repr jit compare");
        });
    }

    #[test]
    fn analyzes_string_source_as_runtime_pointer_lane() {
        let analysis =
            analyze_source_abi_reprs_with_options("\"hello\"", infer::SourceOptions::default())
                .expect("native ABI reprs");

        assert_eq!(
            analysis.function_repr("root_0"),
            Some(&NativeAbiRepr::RuntimeValuePtr(
                NativeRuntimePtrKind::String
            ))
        );
        assert_eq!(
            analysis.function_lane("root_0"),
            Some(NativeAbiValueLane::RuntimeValuePtr)
        );
    }

    #[test]
    fn evals_string_source_through_cranelift_value_lane() {
        let values =
            eval_source_value_lane_with_options("\"hello\"", infer::SourceOptions::default())
                .expect("native value jit eval");

        assert_eq!(
            values,
            vec![runtime::VmValue::String(
                runtime::runtime::string_tree::StringTree::from_str("hello")
            )]
        );
    }

    #[test]
    fn evals_string_concat_source_through_cranelift_value_lane() {
        let value = run_with_large_stack(|| {
            let values = eval_source_value_lane("\"a\" + \"b\"").expect("native value jit eval");
            let [runtime::VmValue::String(value)] = values.as_slice() else {
                panic!("expected one string value");
            };
            value.to_flat_string()
        });

        assert_eq!(value, "ab");
    }

    #[test]
    fn evals_scalar_sources_through_cranelift_value_lane() {
        let values =
            eval_source_value_lane_with_options("true\n()\n1.5", infer::SourceOptions::default())
                .expect("native value jit eval");

        assert_eq!(
            values,
            vec![
                runtime::VmValue::Bool(true),
                runtime::VmValue::Unit,
                runtime::VmValue::Float("1.5".to_string())
            ]
        );
    }

    #[test]
    fn evals_list_literal_source_through_cranelift_value_lane() {
        let items = run_with_large_stack(|| {
            let values = eval_source_value_lane("[1, 2, 3]").expect("native value jit eval");
            let [runtime::VmValue::List(list)] = values.as_slice() else {
                panic!("expected one list value");
            };
            list.to_vec()
                .into_iter()
                .map(|value| match value.as_ref() {
                    runtime::VmValue::Int(value) => value.clone(),
                    value => panic!("expected int list item, got {value:?}"),
                })
                .collect::<Vec<_>>()
        });

        assert_eq!(items, vec!["1", "2", "3"]);
    }

    #[test]
    fn evals_list_len_and_index_source_through_cranelift_value_lane() {
        let values = run_with_large_stack(|| {
            eval_source_value_lane("[1, 2].len\n[1, 2].index 1")
                .expect("native value jit eval")
                .into_iter()
                .map(|value| match value {
                    runtime::VmValue::Int(value) => value,
                    value => panic!("expected int value, got {value:?}"),
                })
                .collect::<Vec<_>>()
        });

        assert_eq!(values, vec!["2", "2"]);
    }

    #[test]
    fn evals_structural_sources_through_cranelift_value_lane() {
        let values = eval_source_value_lane_with_options(
            "(1, 2)\n{x: 1, y: 2}\n{x: 1, y: 2}.x\nmy get_y p = p.y\nget_y {x: 3, y: 4}\n:label \"send\"",
            infer::SourceOptions::default(),
        )
        .expect("native value jit eval");

        assert_eq!(
            values,
            vec![
                runtime::VmValue::Tuple(vec![
                    runtime::VmValue::Int("1".to_string()),
                    runtime::VmValue::Int("2".to_string())
                ]),
                runtime::VmValue::Record(BTreeMap::from([
                    (
                        yulang_core_ir::Name("x".to_string()),
                        runtime::VmValue::Int("1".to_string())
                    ),
                    (
                        yulang_core_ir::Name("y".to_string()),
                        runtime::VmValue::Int("2".to_string())
                    )
                ])),
                runtime::VmValue::Int("1".to_string()),
                runtime::VmValue::Int("4".to_string()),
                runtime::VmValue::Variant {
                    tag: yulang_core_ir::Name("label".to_string()),
                    value: Some(Box::new(runtime::VmValue::String(
                        runtime::runtime::string_tree::StringTree::from_str("send")
                    )))
                }
            ]
        );
    }

    #[test]
    fn emits_string_source_value_object() {
        let object =
            compile_source_value_object_with_options("\"hello\"", infer::SourceOptions::default())
                .expect("native value object");

        assert!(!object.bytes().is_empty());
        assert_eq!(object.roots(), &["root_0".to_string()]);
    }

    #[test]
    fn analyzes_list_source_element_repr() {
        let analysis = run_with_large_stack(|| {
            analyze_source_abi_reprs("[1, 2, 3]").expect("native ABI reprs")
        });

        assert_eq!(
            analysis.function_repr("root_0"),
            Some(&NativeAbiRepr::List(Box::new(NativeAbiRepr::Int)))
        );
        assert_eq!(
            analysis.function_lane("root_0"),
            Some(NativeAbiValueLane::RuntimeValuePtr)
        );
    }

    #[test]
    fn source_diagnostics_are_reported_before_runtime_lowering() {
        let error = eval_source_with_options("missing_name", infer::SourceOptions::default())
            .expect_err("diagnostic");
        assert!(matches!(error, NativeSourceError::SurfaceDiagnostics(_)));
    }

    fn run_with_large_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(f)
            .expect("spawn native source test thread")
            .join()
            .expect("join native source test thread")
    }
}
