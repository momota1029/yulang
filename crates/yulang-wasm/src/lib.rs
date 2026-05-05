use serde::Serialize;
use wasm_bindgen::prelude::*;

use yulang_infer::{collect_surface_diagnostics, export_core_program, lower_source_set};
use yulang_runtime as runtime;
use yulang_source::{SourceOptions, collect_inline_source_files_with_options};

pub use color::{ColorizeOutput, HighlightSpan};
pub use output::{Diagnostic, RunOutput, RunResult, TypeResult};

#[wasm_bindgen]
pub fn run(source: &str) -> JsValue {
    console_error_panic_hook::set_once();
    to_js_value(&run_inner(source))
}

#[wasm_bindgen]
pub fn colorize(source: &str) -> JsValue {
    console_error_panic_hook::set_once();
    to_js_value(&color::colorize_source(source))
}

fn run_inner(source: &str) -> RunOutput {
    match compile_and_run(source) {
        Ok((results, types)) => RunOutput {
            ok: true,
            results,
            types,
            diagnostics: Vec::new(),
        },
        Err(message) => RunOutput {
            ok: false,
            results: Vec::new(),
            types: Vec::new(),
            diagnostics: vec![Diagnostic::error(message, source.len())],
        },
    }
}

fn compile_and_run(source: &str) -> Result<(Vec<RunResult>, Vec<TypeResult>), String> {
    let source = playground_source(source);
    let source_set = collect_inline_source_files_with_options(
        &source,
        std_sources::inline_sources(),
        SourceOptions {
            std_root: None,
            implicit_prelude: true,
            search_paths: Vec::new(),
        },
    );
    let mut lowered = lower_source_set(&source_set);
    let types = yulang_infer::render_exported_compact_results(&mut lowered.state)
        .into_iter()
        .map(|(name, ty)| TypeResult { name, ty })
        .collect();
    let surface_diagnostics = collect_surface_diagnostics(&lowered.state);
    if !surface_diagnostics.is_empty() {
        return Err(surface_diagnostics
            .into_iter()
            .map(|diagnostic| diagnostic.message)
            .collect::<Vec<_>>()
            .join("\n"));
    }
    let program = export_core_program(&mut lowered.state);
    let module = runtime::lower_core_program(program)
        .and_then(runtime::monomorphize_module)
        .map_err(|error| error.to_string())?;
    let vm = runtime::compile_vm_module(module).map_err(|error| error.to_string())?;
    vm.eval_roots()
        .map_err(|error| error.to_string())
        .map(|results| {
            (
                results
                    .iter()
                    .enumerate()
                    .map(|(index, result)| RunResult {
                        index,
                        value: output::format_vm_result(result),
                    })
                    .collect(),
                types,
            )
        })
}

fn playground_source(source: &str) -> String {
    format!("use std::undet::*\n{source}")
}

fn to_js_value<T: Serialize>(value: &T) -> JsValue {
    serde_wasm_bindgen::to_value(value).unwrap_or_else(|error| {
        JsValue::from_str(&format!("failed to serialize playground response: {error}"))
    })
}

mod color;
mod output;
mod std_sources;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn runs_undet_list_example() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let output = run_inner(
                    r#"(each [1, 2, 3] + each [4, 5, 6]).list
"#,
                );
                assert_eq!(output.results.len(), 1);
                assert_eq!(output.results[0].value, "[5, 6, 7, 6, 7, 8, 7, 8, 9]");
                assert!(output.ok, "{:?}", output.diagnostics);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn reports_exported_types() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let output = run_inner(
                    r#"our f x = x + 1
my hidden x = x
pub g = f 1
g
"#,
                );
                assert!(output.ok, "{:?}", output.diagnostics);
                let names = output
                    .types
                    .iter()
                    .map(|item| item.name.as_str())
                    .collect::<Vec<_>>();
                assert!(names.contains(&"f"));
                assert!(names.contains(&"g"));
                assert!(!names.contains(&"hidden"));
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn reports_multiple_root_results() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let output = run_inner(
                    r#"1 + 2
3 + 4
"#,
                );
                assert!(output.ok, "{:?}", output.diagnostics);
                assert_eq!(output.results.len(), 2);
                assert_eq!(output.results[0].value, "3");
                assert_eq!(output.results[1].value, "7");
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn reports_runtime_type_mismatch_without_internal_type_dump() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let output = run_inner("1 + true\n");
                assert!(!output.ok);
                let message = &output.diagnostics[0].message;
                assert!(message.contains("type mismatch"), "{message}");
                assert!(message.contains("expected bool"), "{message}");
                assert!(message.contains("got int"), "{message}");
                assert!(message.contains("+"), "{message}");
                assert!(!message.contains("failed to lower runtime IR"), "{message}");
                assert!(!message.contains("Named {"), "{message}");
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn reports_undefined_name_before_runtime_lowering() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let output = run_inner("x\n");
                assert!(!output.ok);
                let message = &output.diagnostics[0].message;
                assert!(message.contains("undefined name `x`"), "{message}");
                assert!(
                    !message.contains("could not determine the type"),
                    "{message}"
                );
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn reports_unresolved_method_before_runtime_lowering() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let output = run_inner("1.foo\n");
                assert!(!output.ok);
                let message = &output.diagnostics[0].message;
                assert!(
                    message.contains("no field or method named `.foo` could be resolved"),
                    "{message}"
                );
                assert!(
                    !message.contains("could not determine the type"),
                    "{message}"
                );
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
