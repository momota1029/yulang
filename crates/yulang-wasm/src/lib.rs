use serde::Serialize;
use std::cell::RefCell;
use wasm_bindgen::prelude::*;

use yulang_infer::{
    SourceLowerCache, collect_surface_diagnostics, export_core_program,
    lower_source_set_with_std_cache_profiled, warm_std_source_cache,
};
use yulang_runtime as runtime;

pub use color::{ColorizeOutput, HighlightSpan};
pub use output::{Diagnostic, RunOutput, RunResult, RunTimings, TypeResult, WarmupOutput};

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

#[wasm_bindgen]
pub fn warm_std_cache() -> JsValue {
    console_error_panic_hook::set_once();
    to_js_value(&warm_std_cache_inner())
}

fn warm_std_cache_inner() -> WarmupOutput {
    let start = now_ms();
    let source_set = std_sources::warm_source_set();
    let profile = SOURCE_LOWER_CACHE
        .with(|cache| warm_std_source_cache(&source_set, &mut cache.borrow_mut()));
    WarmupOutput {
        source_cache_hits: profile.hits,
        source_cache_misses: profile.misses,
        source_cache_clone_ms: profile.clone.as_secs_f64() * 1_000.0,
        source_cache_build_ms: profile.build.as_secs_f64() * 1_000.0,
        total_ms: elapsed_ms(start),
    }
}

fn run_inner(source: &str) -> RunOutput {
    match compile_and_run(source) {
        Ok(output) => RunOutput {
            ok: true,
            results: output.results,
            stdout: output.stdout,
            types: output.types,
            timings: Some(output.timings),
            diagnostics: Vec::new(),
        },
        Err(message) => RunOutput {
            ok: false,
            results: Vec::new(),
            stdout: String::new(),
            types: Vec::new(),
            timings: None,
            diagnostics: vec![Diagnostic::error(message, source.len())],
        },
    }
}

struct CompileRunOutput {
    results: Vec<RunResult>,
    stdout: String,
    types: Vec<TypeResult>,
    timings: RunTimings,
}

fn compile_and_run(source: &str) -> Result<CompileRunOutput, String> {
    let total_start = now_ms();
    let source = playground_source(source);
    let source_set_start = now_ms();
    let source_set = std_sources::source_set(&source);
    let source_set_ms = elapsed_ms(source_set_start);
    let files = source_set.files.len();
    let entry_files = source_set.entry_files().count();
    let std_files = source_set.std_files().count();
    let user_files = source_set.user_files().count();
    let infer_lower_start = now_ms();
    let profiled_lowered = lower_with_cache(&source_set);
    let source_cache = profiled_lowered.profile.std_cache.clone();
    let mut lowered = profiled_lowered.lowered;
    let infer_lower_ms = elapsed_ms(infer_lower_start);
    let type_render_start = now_ms();
    let types = yulang_infer::render_exported_compact_results(&mut lowered.state)
        .into_iter()
        .map(|(name, ty)| TypeResult { name, ty })
        .collect();
    let type_render_ms = elapsed_ms(type_render_start);
    let diagnostics_start = now_ms();
    let surface_diagnostics = collect_surface_diagnostics(&lowered.state);
    let diagnostics_ms = elapsed_ms(diagnostics_start);
    if !surface_diagnostics.is_empty() {
        return Err(surface_diagnostics
            .into_iter()
            .map(|diagnostic| diagnostic.message)
            .collect::<Vec<_>>()
            .join("\n"));
    }
    let export_core_start = now_ms();
    let program = export_core_program(&mut lowered.state);
    let export_core_ms = elapsed_ms(export_core_start);
    let runtime_lower_start = now_ms();
    let module = runtime::lower_core_program(program).map_err(|error| error.to_string())?;
    let runtime_lower_ms = elapsed_ms(runtime_lower_start);
    let monomorphize_start = now_ms();
    let module = runtime::monomorphize_module(module).map_err(|error| error.to_string())?;
    let monomorphize_ms = elapsed_ms(monomorphize_start);
    let vm_compile_start = now_ms();
    let vm = runtime::compile_vm_module(module).map_err(|error| error.to_string())?;
    let vm_compile_ms = elapsed_ms(vm_compile_start);
    let vm_eval_start = now_ms();
    runtime::eval_roots_with_basic_host(&vm)
        .map_err(|error| error.to_string())
        .map(|host_output| CompileRunOutput {
            results: host_output
                .results
                .iter()
                .enumerate()
                .map(|(index, result)| RunResult {
                    index,
                    value: output::format_vm_result(result),
                })
                .collect(),
            stdout: host_output.stdout,
            types,
            timings: RunTimings {
                source_set_ms,
                infer_lower_ms,
                type_render_ms,
                diagnostics_ms,
                export_core_ms,
                runtime_lower_ms,
                monomorphize_ms,
                vm_compile_ms,
                vm_eval_ms: elapsed_ms(vm_eval_start),
                total_ms: elapsed_ms(total_start),
                files,
                entry_files,
                std_files,
                user_files,
                source_cache_hits: source_cache.hits,
                source_cache_misses: source_cache.misses,
                source_cache_clone_ms: source_cache.clone.as_secs_f64() * 1_000.0,
                source_cache_build_ms: source_cache.build.as_secs_f64() * 1_000.0,
            },
        })
}

thread_local! {
    static SOURCE_LOWER_CACHE: RefCell<SourceLowerCache> = RefCell::new(SourceLowerCache::default());
}

fn lower_with_cache(source_set: &yulang_source::SourceSet) -> yulang_infer::ProfiledLoweredSources {
    SOURCE_LOWER_CACHE
        .with(|cache| lower_source_set_with_std_cache_profiled(source_set, &mut cache.borrow_mut()))
}

fn playground_source(source: &str) -> String {
    format!("use std::undet::*\n{source}")
}

fn to_js_value<T: Serialize>(value: &T) -> JsValue {
    serde_wasm_bindgen::to_value(value).unwrap_or_else(|error| {
        JsValue::from_str(&format!("failed to serialize playground response: {error}"))
    })
}

#[cfg(target_arch = "wasm32")]
fn now_ms() -> f64 {
    js_sys::Date::now()
}

#[cfg(not(target_arch = "wasm32"))]
fn now_ms() -> f64 {
    use std::sync::OnceLock;
    use std::time::Instant;

    static START: OnceLock<Instant> = OnceLock::new();
    START.get_or_init(Instant::now).elapsed().as_secs_f64() * 1000.0
}

fn elapsed_ms(start: f64) -> f64 {
    now_ms() - start
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
    fn reports_compile_timings() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let output = run_inner("1 + 2\n");
                assert!(output.ok, "{:?}", output.diagnostics);
                let timings = output.timings.expect("run timings");
                assert!(timings.files > 1);
                assert!(timings.total_ms >= 0.0);
                assert_eq!(timings.source_cache_hits + timings.source_cache_misses, 1);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn warm_std_cache_makes_later_runs_hit() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let _ = warm_std_cache_inner();
                let output = run_inner("1 + 2\n");
                assert!(output.ok, "{:?}", output.diagnostics);
                let timings = output.timings.expect("run timings");
                assert_eq!(timings.source_cache_hits, 1);
                assert_eq!(timings.source_cache_misses, 0);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn captures_console_output() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let output = run_inner(
                    r#"println "hello"
1 + 2
"#,
                );
                assert!(output.ok, "{:?}", output.diagnostics);
                assert_eq!(output.stdout, "hello\n");
                assert_eq!(output.results.len(), 2);
                assert_eq!(output.results[0].value, "()");
                assert_eq!(output.results[1].value, "3");
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn runs_newline_separated_list_items() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let output = run_inner(
                    r#"[
    1
    2
    3
    4
]
"#,
                );
                assert!(output.ok, "{:?}", output.diagnostics);
                assert_eq!(output.results.len(), 1);
                assert_eq!(output.results[0].value, "[1, 2, 3, 4]");
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn runs_multiline_sub_return_expression() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let output = run_inner(
                    r#"my f() = sub:
    return
        1 + 2 + 3 + 4

f()
"#,
                );
                assert!(output.ok, "{:?}", output.diagnostics);
                assert_eq!(output.results.len(), 1);
                assert_eq!(output.results[0].value, "10");
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
