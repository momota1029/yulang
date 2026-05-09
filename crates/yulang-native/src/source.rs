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
use crate::closure::closure_convert_module;
use crate::control_ir::NativeModule;
use crate::cranelift::{NativeCraneliftError, compile_abi_module};
use crate::eval::{NativeEvalError, eval_module};
use crate::lower::{NativeLowerError, lower_module};

pub type NativeSourceResult<T> = Result<T, NativeSourceError>;

#[derive(Debug)]
pub enum NativeSourceError {
    SourceLoad(infer::SourceLoadError),
    SurfaceDiagnostics(Vec<String>),
    RuntimeLower(runtime::RuntimeError),
    NativeLower(NativeLowerError),
    NativeEval(NativeEvalError),
    Cranelift(NativeCraneliftError),
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
    fn source_diagnostics_are_reported_before_runtime_lowering() {
        let error = eval_source_with_options("missing_name", infer::SourceOptions::default())
            .expect_err("diagnostic");
        assert!(matches!(error, NativeSourceError::SurfaceDiagnostics(_)));
    }
}
