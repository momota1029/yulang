use serde::Serialize;
use std::cell::RefCell;
use wasm_bindgen::prelude::*;

use yulang_infer::{
    SourceLowerCache, build_compiled_unit_artifacts, build_std_core_snapshot_data,
    build_std_infer_snapshot_data, collect_surface_diagnostics, export_core_program,
    import_std_infer_snapshot_data, lower_source_set,
    lower_source_set_with_compiled_unit_artifacts_profiled,
    lower_source_set_with_std_cache_profiled, warm_std_source_cache,
};
use yulang_runtime as runtime;

pub use color::{ColorizeOutput, HighlightSpan};
pub use output::{
    Diagnostic, EmbeddedStdArtifactsOutput, RunOutput, RunResult, RunTimings, TypeResult,
    WarmupOutput,
};

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

#[wasm_bindgen]
pub fn std_snapshot_data() -> JsValue {
    console_error_panic_hook::set_once();
    let source_set = std_sources::warm_source_set();
    to_js_value(&build_std_infer_snapshot_data(&source_set))
}

#[wasm_bindgen]
pub fn std_snapshot_import_coverage() -> JsValue {
    console_error_panic_hook::set_once();
    let source_set = std_sources::warm_source_set();
    let coverage = build_std_infer_snapshot_data(&source_set)
        .and_then(|data| import_std_infer_snapshot_data(&data).ok())
        .map(|import| import.coverage);
    to_js_value(&coverage)
}

#[wasm_bindgen]
pub fn std_core_snapshot_data() -> JsValue {
    console_error_panic_hook::set_once();
    let source_set = std_sources::warm_source_set();
    to_js_value(&build_std_core_snapshot_data(&source_set))
}

#[wasm_bindgen]
pub fn std_compiled_unit_artifacts() -> JsValue {
    console_error_panic_hook::set_once();
    let source_set = std_sources::warm_source_set();
    let lowered = lower_source_set(&source_set);
    to_js_value(&build_compiled_unit_artifacts(&source_set, &lowered.state))
}

#[wasm_bindgen]
pub fn embedded_std_compiled_unit_artifacts() -> JsValue {
    console_error_panic_hook::set_once();
    to_js_value(&embedded_std_compiled_unit_artifacts_inner())
}

#[wasm_bindgen]
pub fn embedded_std_compiled_unit_artifact_status() -> JsValue {
    console_error_panic_hook::set_once();
    to_js_value(&embedded_std_compiled_unit_artifact_status_inner())
}

fn embedded_std_compiled_unit_artifacts_inner() -> Vec<yulang_infer::CompiledUnitArtifact> {
    load_embedded_std_compiled_unit_artifacts()
        .expect("embedded std compiled unit artifacts should deserialize and validate")
}

fn embedded_std_compiled_unit_artifact_status_inner() -> EmbeddedStdArtifactsOutput {
    match load_embedded_std_compiled_unit_artifacts() {
        Ok(artifacts) => EmbeddedStdArtifactsOutput {
            runtime_bindings: artifacts
                .iter()
                .map(|artifact| artifact.runtime.program.program.bindings.len())
                .sum(),
            artifacts: artifacts.len(),
            bytes: EMBEDDED_STD_COMPILED_UNIT_ARTIFACTS_JSON.len(),
            valid: true,
            fallback_reason: None,
        },
        Err(reason) => EmbeddedStdArtifactsOutput {
            artifacts: 0,
            runtime_bindings: 0,
            bytes: EMBEDDED_STD_COMPILED_UNIT_ARTIFACTS_JSON.len(),
            valid: false,
            fallback_reason: Some(reason),
        },
    }
}

const EMBEDDED_STD_COMPILED_UNIT_ARTIFACTS_JSON: &str = include_str!(concat!(
    env!("OUT_DIR"),
    "/std_compiled_unit_artifacts.json"
));

fn load_embedded_std_compiled_unit_artifacts()
-> Result<Vec<yulang_infer::CompiledUnitArtifact>, String> {
    let artifacts = serde_json::from_str::<Vec<yulang_infer::CompiledUnitArtifact>>(
        EMBEDDED_STD_COMPILED_UNIT_ARTIFACTS_JSON,
    )
    .map_err(|error| format!("deserialize embedded std artifacts: {error}"))?;
    validate_embedded_std_compiled_unit_artifacts(&artifacts)?;
    Ok(artifacts)
}

fn validate_embedded_std_compiled_unit_artifacts(
    artifacts: &[yulang_infer::CompiledUnitArtifact],
) -> Result<(), String> {
    if artifacts.is_empty() {
        return Err("embedded std artifacts are empty".to_string());
    }
    for artifact in artifacts {
        if artifact.manifest.artifact_format_version
            != yulang_source::COMPILED_UNIT_ARTIFACT_FORMAT_VERSION
        {
            return Err(format!(
                "unsupported compiled-unit artifact format {}",
                artifact.manifest.artifact_format_version
            ));
        }
        if artifact.manifest.parser_format_version
            != yulang_source::COMPILED_UNIT_PARSER_FORMAT_VERSION
        {
            return Err(format!(
                "unsupported parser format {}",
                artifact.manifest.parser_format_version
            ));
        }
        let namespace_validation = artifact.namespace.validate();
        if !namespace_validation.is_complete() {
            return Err(format!(
                "invalid namespace surface in unit {}",
                artifact.manifest.unit_index
            ));
        }
        let typed_validation = artifact.typed.validate(&artifact.namespace);
        if !typed_validation.is_complete() {
            return Err(format!(
                "invalid typed surface in unit {}",
                artifact.manifest.unit_index
            ));
        }
    }
    Ok(())
}

fn warm_std_cache_inner() -> WarmupOutput {
    let start = now_ms();
    let source_set = std_sources::warm_source_set();
    let embedded = embedded_std_compiled_unit_artifact_status_inner();
    let profile = SOURCE_LOWER_CACHE
        .with(|cache| warm_std_source_cache(&source_set, &mut cache.borrow_mut()));
    WarmupOutput {
        source_cache_hits: profile.hits,
        source_cache_misses: profile.misses,
        source_cache_clone_ms: profile.clone.as_secs_f64() * 1_000.0,
        source_cache_build_ms: profile.build.as_secs_f64() * 1_000.0,
        embedded_std_artifacts: embedded.artifacts,
        embedded_std_runtime_bindings: embedded.runtime_bindings,
        embedded_std_artifacts_bytes: embedded.bytes,
        embedded_std_artifacts_valid: embedded.valid,
        embedded_std_artifacts_fallback_reason: embedded.fallback_reason,
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
    compile_and_run_with_embedded_std(source, true, None)
}

fn compile_and_run_with_embedded_std(
    source: &str,
    use_embedded_std: bool,
    forced_fallback_reason: Option<String>,
) -> Result<CompileRunOutput, String> {
    let total_start = now_ms();
    let raw_source = source;
    let source = playground_source(raw_source);
    let source_set_start = now_ms();
    let source_set = std_sources::source_set(&source);
    let source_set_ms = elapsed_ms(source_set_start);
    let files = source_set.files.len();
    let entry_files = source_set.entry_files().count();
    let std_files = source_set.std_files().count();
    let user_files = source_set.user_files().count();
    let infer_lower_start = now_ms();
    let compiled_std_lowering = if use_embedded_std {
        lower_with_embedded_std_artifacts(&source_set)
    } else {
        Err(forced_fallback_reason
            .clone()
            .unwrap_or_else(|| "embedded std artifact path disabled".to_string()))
    };
    let compiled_std_fallback_reason = forced_fallback_reason
        .clone()
        .or_else(|| compiled_std_lowering.as_ref().err().cloned());
    let (profiled_lowered, compiled_std_runtime, compiled_std_artifacts, compiled_std_bindings) =
        match compiled_std_lowering {
            Ok(lowering) => (
                lowering.lowered,
                Some(lowering.runtime),
                lowering.artifacts,
                lowering.runtime_bindings,
            ),
            Err(_) => (lower_with_cache(&source_set), None, 0, 0),
        };
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
        let message = surface_diagnostics
            .into_iter()
            .map(|diagnostic| diagnostic.message)
            .collect::<Vec<_>>()
            .join("\n");
        if use_embedded_std && compiled_std_runtime.is_some() {
            return compile_and_run_with_embedded_std(
                raw_source,
                false,
                Some(format!("embedded std artifact diagnostics: {message}")),
            );
        }
        return Err(message);
    }
    let export_core_start = now_ms();
    let mut program = export_core_program(&mut lowered.state);
    if let Some(runtime) = &compiled_std_runtime {
        program = match runtime.merge_with_user_program(program) {
            Ok(program) => program,
            Err(error) if use_embedded_std => {
                return compile_and_run_with_embedded_std(
                    raw_source,
                    false,
                    Some(format!("merge embedded std runtime surfaces: {error:?}")),
                );
            }
            Err(error) => return Err(format!("merge embedded std runtime surfaces: {error:?}")),
        };
    }
    let export_core_ms = elapsed_ms(export_core_start);
    let runtime_lower_start = now_ms();
    let module = match runtime::lower_core_program(program) {
        Ok(module) => module,
        Err(error) if use_embedded_std && compiled_std_runtime.is_some() => {
            return compile_and_run_with_embedded_std(
                raw_source,
                false,
                Some(format!("lower embedded std runtime program: {error}")),
            );
        }
        Err(error) => return Err(error.to_string()),
    };
    let runtime_lower_ms = elapsed_ms(runtime_lower_start);
    let monomorphize_start = now_ms();
    let module = match runtime::monomorphize_module(module) {
        Ok(module) => module,
        Err(error) if use_embedded_std && compiled_std_runtime.is_some() => {
            return compile_and_run_with_embedded_std(
                raw_source,
                false,
                Some(format!(
                    "monomorphize embedded std runtime program: {error}"
                )),
            );
        }
        Err(error) => return Err(error.to_string()),
    };
    let monomorphize_ms = elapsed_ms(monomorphize_start);
    let vm_compile_start = now_ms();
    let vm = match runtime::compile_vm_module(module) {
        Ok(vm) => vm,
        Err(error) if use_embedded_std && compiled_std_runtime.is_some() => {
            return compile_and_run_with_embedded_std(
                raw_source,
                false,
                Some(format!("compile embedded std runtime program: {error}")),
            );
        }
        Err(error) => return Err(error.to_string()),
    };
    let vm_compile_ms = elapsed_ms(vm_compile_start);
    let vm_eval_start = now_ms();
    match runtime::eval_roots_with_basic_host(&vm) {
        Ok(host_output) => {
            if use_embedded_std
                && compiled_std_runtime.is_some()
                && host_output
                    .results
                    .iter()
                    .any(|result| matches!(result, runtime::VmResult::Request(_)))
            {
                return compile_and_run_with_embedded_std(
                    raw_source,
                    false,
                    Some("embedded std runtime left a root request unresolved".to_string()),
                );
            }

            Ok(CompileRunOutput {
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
                    compiled_std_artifacts,
                    compiled_std_runtime_bindings: compiled_std_bindings,
                    compiled_std_cache_hit: compiled_std_runtime.is_some(),
                    compiled_std_fallback_reason,
                },
            })
        }
        Err(error) if use_embedded_std && compiled_std_runtime.is_some() => {
            compile_and_run_with_embedded_std(
                raw_source,
                false,
                Some(format!("eval embedded std runtime program: {error}")),
            )
        }
        Err(error) => Err(error.to_string()),
    }
}

thread_local! {
    static SOURCE_LOWER_CACHE: RefCell<SourceLowerCache> = RefCell::new(SourceLowerCache::default());
}

fn lower_with_cache(source_set: &yulang_source::SourceSet) -> yulang_infer::ProfiledLoweredSources {
    SOURCE_LOWER_CACHE
        .with(|cache| lower_source_set_with_std_cache_profiled(source_set, &mut cache.borrow_mut()))
}

struct EmbeddedStdLowering {
    lowered: yulang_infer::ProfiledLoweredSources,
    runtime: yulang_infer::CompiledRuntimeBundle,
    artifacts: usize,
    runtime_bindings: usize,
}

fn lower_with_embedded_std_artifacts(
    source_set: &yulang_source::SourceSet,
) -> Result<EmbeddedStdLowering, String> {
    let artifacts = load_embedded_std_compiled_unit_artifacts()?;
    let std_artifacts = artifacts
        .into_iter()
        .filter(artifact_has_std_module)
        .collect::<Vec<_>>();
    if std_artifacts.is_empty() {
        return Err("embedded std artifacts contain no std units".to_string());
    }
    let runtime_bindings = std_artifacts
        .iter()
        .map(|artifact| artifact.runtime.program.program.bindings.len())
        .sum();
    let lowered =
        lower_source_set_with_compiled_unit_artifacts_profiled(source_set, &std_artifacts)
            .map_err(|error| format!("import embedded std artifacts: {error:?}"))?;

    Ok(EmbeddedStdLowering {
        lowered: lowered.lowered,
        runtime: lowered.runtime,
        artifacts: std_artifacts.len(),
        runtime_bindings,
    })
}

fn artifact_has_std_module(artifact: &yulang_infer::CompiledUnitArtifact) -> bool {
    artifact.namespace.modules.iter().any(|module| {
        module
            .path
            .first()
            .is_some_and(|segment| segment.as_str() == "std")
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
                if timings.compiled_std_cache_hit {
                    assert!(timings.compiled_std_artifacts > 1);
                    assert!(timings.compiled_std_runtime_bindings > 10);
                    assert!(timings.compiled_std_fallback_reason.is_none());
                } else {
                    assert!(timings.compiled_std_fallback_reason.is_some());
                }
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
                let warmup = warm_std_cache_inner();
                assert!(warmup.embedded_std_artifacts > 1);
                assert!(warmup.embedded_std_runtime_bindings > 10);
                assert!(warmup.embedded_std_artifacts_bytes > 1024);
                assert!(warmup.embedded_std_artifacts_valid);
                assert!(warmup.embedded_std_artifacts_fallback_reason.is_none());
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
    fn builds_std_snapshot_import_coverage_for_wasm_export() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let source_set = std_sources::warm_source_set();
                let data = build_std_infer_snapshot_data(&source_set).expect("std snapshot data");
                let import = import_std_infer_snapshot_data(&data).expect("std snapshot import");
                assert!(import.coverage.modules_total > 0);
                assert_eq!(
                    import.coverage.modules_total,
                    import.coverage.modules_resolved
                );
                assert!(import.coverage.values_total > 0);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn builds_std_core_snapshot_data_for_wasm_export() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let source_set = std_sources::warm_source_set();
                let data =
                    build_std_core_snapshot_data(&source_set).expect("std core snapshot data");
                assert!(data.program.program.bindings.len() > 10);
                assert!(data.program.program.bindings.iter().any(|binding| {
                    binding
                        .name
                        .segments
                        .iter()
                        .map(|name| name.0.as_str())
                        .eq(["std", "list", "fold_impl"])
                }));
                assert_eq!(
                    data.manifest.format_version,
                    yulang_infer::STD_INFER_SNAPSHOT_FORMAT_VERSION
                );
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn builds_std_compiled_unit_artifacts_for_wasm_export() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let source_set = std_sources::warm_source_set();
                let lowered = lower_source_set(&source_set);
                let artifacts = build_compiled_unit_artifacts(&source_set, &lowered.state);
                assert!(artifacts.len() > 1);
                let list_artifact = artifacts
                    .iter()
                    .find(|artifact| {
                        artifact
                            .namespace
                            .modules
                            .iter()
                            .any(|module| module.path == ["std", "list"])
                    })
                    .expect("std::list compiled unit artifact");
                assert!(
                    list_artifact
                        .runtime
                        .program
                        .program
                        .bindings
                        .iter()
                        .any(|binding| {
                            binding
                                .name
                                .segments
                                .iter()
                                .map(|name| name.0.as_str())
                                .eq(["std", "list", "fold_impl"])
                        })
                );
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn embeds_std_compiled_unit_artifacts_for_wasm_bundle() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let status = embedded_std_compiled_unit_artifact_status_inner();
                assert!(status.valid, "{:?}", status.fallback_reason);
                assert!(status.artifacts > 1);
                assert!(status.runtime_bindings > 10);
                let artifacts = embedded_std_compiled_unit_artifacts_inner();
                assert!(artifacts.len() > 1);
                assert!(artifacts.iter().any(|artifact| {
                    artifact
                        .namespace
                        .modules
                        .iter()
                        .any(|module| module.path == ["std", "list"])
                        && artifact
                            .runtime
                            .program
                            .program
                            .bindings
                            .iter()
                            .any(|binding| {
                                binding
                                    .name
                                    .segments
                                    .iter()
                                    .map(|name| name.0.as_str())
                                    .eq(["std", "list", "fold_impl"])
                            })
                }));
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn runs_program_with_dependency_runtime_surface_merged() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let source_set = yulang_source::collect_inline_source_files_with_options(
                    "use dep::*\nf 41\n",
                    [yulang_source::InlineSource {
                        path: std::path::PathBuf::from("<dep>.yu"),
                        module_path: yulang_core_ir::Path::new(vec![yulang_core_ir::Name(
                            "dep".to_string(),
                        )]),
                        origin: yulang_source::SourceOrigin::User,
                        source: "pub f x = x\n".to_string(),
                        meta: None,
                    }],
                    yulang_source::SourceOptions {
                        std_root: None,
                        implicit_prelude: false,
                        search_paths: Vec::new(),
                    },
                );
                let mut lowered = lower_source_set(&source_set);
                let artifacts = build_compiled_unit_artifacts(&source_set, &lowered.state);
                let dep_artifact = artifacts
                    .iter()
                    .find(|artifact| {
                        artifact
                            .namespace
                            .modules
                            .iter()
                            .any(|module| module.path == ["dep"])
                    })
                    .expect("dep compiled unit artifact");
                let bundle =
                    yulang_infer::CompiledRuntimeBundle::from_surfaces([&dep_artifact.runtime])
                        .expect("runtime bundle");
                let mut user_program = export_core_program(&mut lowered.state);
                remove_program_bindings_in_module(&mut user_program, "dep");

                let merged = bundle
                    .merge_with_user_program(user_program)
                    .expect("merged runtime program");
                let module = runtime::lower_core_program(merged).expect("lowered runtime program");
                let module = runtime::monomorphize_module(module).expect("monomorphized module");
                let vm = runtime::compile_vm_module(module).expect("compiled vm module");
                let output = runtime::eval_roots_with_basic_host(&vm).expect("vm output");
                assert_eq!(output.results.len(), 1);
                assert_eq!(output::format_vm_result(&output.results[0]), "41");
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn runs_program_with_std_runtime_surfaces_merged() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let source_set = std_sources::source_set("1 + 2\n");
                let mut lowered = lower_source_set(&source_set);
                let artifacts = embedded_std_compiled_unit_artifacts_inner();
                let std_surfaces = artifacts
                    .iter()
                    .filter(|artifact| {
                        artifact
                            .namespace
                            .modules
                            .iter()
                            .any(|module| module.path.first().is_some_and(|part| part == "std"))
                    })
                    .map(|artifact| &artifact.runtime)
                    .collect::<Vec<_>>();
                assert!(std_surfaces.len() > 1);
                let bundle = yulang_infer::CompiledRuntimeBundle::from_surfaces(std_surfaces)
                    .expect("std runtime bundle");

                let mut user_program = export_core_program(&mut lowered.state);
                remove_program_bindings_present_in_bundle(&mut user_program, &bundle);
                let merged = bundle
                    .merge_with_user_program(user_program)
                    .expect("merged runtime program");
                assert!(
                    merged
                        .program
                        .bindings
                        .iter()
                        .any(|binding| path_starts_with(&binding.name, "std")),
                    "merged program should restore std bindings from runtime surfaces"
                );

                let module = runtime::lower_core_program(merged).expect("lowered runtime program");
                let module = runtime::monomorphize_module(module).expect("monomorphized module");
                let vm = runtime::compile_vm_module(module).expect("compiled vm module");
                let output = runtime::eval_roots_with_basic_host(&vm).expect("vm output");
                assert_eq!(output.results.len(), 1);
                assert_eq!(output::format_vm_result(&output.results[0]), "3");
            })
            .unwrap()
            .join()
            .unwrap();
    }

    fn remove_program_bindings_in_module(program: &mut yulang_core_ir::CoreProgram, module: &str) {
        program
            .program
            .bindings
            .retain(|binding| !path_starts_with(&binding.name, module));
        program
            .graph
            .bindings
            .retain(|node| !path_starts_with(&node.binding, module));
        program
            .graph
            .runtime_symbols
            .retain(|symbol| !path_starts_with(&symbol.path, module));
    }

    fn path_starts_with(path: &yulang_core_ir::Path, module: &str) -> bool {
        path.segments
            .first()
            .is_some_and(|segment| segment.0 == module)
    }

    fn remove_program_bindings_present_in_bundle(
        program: &mut yulang_core_ir::CoreProgram,
        bundle: &yulang_infer::CompiledRuntimeBundle,
    ) {
        let bundled_paths = bundle
            .surface
            .program
            .program
            .bindings
            .iter()
            .map(|binding| binding.name.clone())
            .collect::<std::collections::HashSet<_>>();
        program
            .program
            .bindings
            .retain(|binding| !bundled_paths.contains(&binding.name));
        program
            .graph
            .bindings
            .retain(|node| !bundled_paths.contains(&node.binding));
        program
            .graph
            .runtime_symbols
            .retain(|symbol| !bundled_paths.contains(&symbol.path));
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

    #[test]
    fn builds_std_snapshot_data_for_wasm_export() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let source_set = std_sources::warm_source_set();
                let data = build_std_infer_snapshot_data(&source_set).expect("std snapshot data");
                assert!(data.manifest.key.covers(
                    &yulang_infer::StdSourceCacheKey::from_source_set(&source_set)
                ));
                assert!(data.values.iter().any(|symbol| {
                    symbol.path == ["std", "prelude", "Add", "add"]
                        || symbol.path == ["std", "int", "add"]
                }));
                assert!(!data.schemes.is_empty());
                assert!(!data.roles.is_empty());
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
