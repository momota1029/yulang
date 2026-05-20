//! Source-level runtime compilation glue.
//!
//! Native codegen was archived with `archive/yulang-native`; this crate now
//! only owns source-to-runtime adapters that are shared by frontends.

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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lowers_literal_source_to_runtime_module() {
        let module = runtime_module_from_virtual_source_with_options(
            "41",
            None,
            SourceOptions {
                implicit_prelude: false,
                std_root: None,
                search_paths: Vec::new(),
            },
        )
        .expect("runtime module");

        assert_eq!(module.root_exprs.len(), 1);
    }
}
