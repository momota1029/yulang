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

    fn assert_source_value_with_std(source: &str) -> Result<(), String> {
        let source = source.to_string();
        run_with_large_stack(move || {
            let values = eval_source_value_lane_with_options(&source, source_options_with_std())
                .map_err(|error| error.to_string())?;
            if values != vec![yulang_runtime::VmValue::Int("42".to_string())] {
                return Err(format!("unexpected value-lane result: {values:?}"));
            }
            Ok(())
        })
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
