use std::cell::RefCell;
use std::collections::HashMap;

use parser::sink::YulangLanguage;
use poly::expr::{Def, Vis};
use poly::types::{Neg, Neu, Pos, StackWeight, Subtractability};
use rowan::SyntaxNode;
use serde::Serialize;
use wasm_bindgen::prelude::*;
use yulang_editor::diagnostics as editor_diagnostics;
use yulang_editor::semantic_tokens;
use yulang_editor::text as editor_text;

const PLAYGROUND_ENTRY: &str = "playground.yu";
const PLAYGROUND_STD_ARTIFACT_ENTRY: &str = "<embedded-playground-std-root>";
const FULL_STD_ARTIFACT_ENTRY: &str = "<embedded-std-root>";
const EMBEDDED_PLAYGROUND_STD_ARTIFACT: &[u8] =
    include_bytes!(concat!(env!("OUT_DIR"), "/embedded_playground_std.yucu"));
const EMBEDDED_FULL_STD_ARTIFACT: &[u8] =
    include_bytes!(concat!(env!("OUT_DIR"), "/embedded_full_std.yucu"));

#[cfg(not(target_arch = "wasm32"))]
#[derive(Debug, Clone, Copy)]
struct ClockInstant(std::time::Instant);

#[cfg(target_arch = "wasm32")]
#[derive(Debug, Clone, Copy)]
struct ClockInstant(f64);

impl ClockInstant {
    fn now() -> Self {
        #[cfg(not(target_arch = "wasm32"))]
        {
            Self(std::time::Instant::now())
        }
        #[cfg(target_arch = "wasm32")]
        {
            Self(js_sys::Date::now())
        }
    }

    fn elapsed_ms(self) -> f64 {
        #[cfg(not(target_arch = "wasm32"))]
        {
            self.0.elapsed().as_secs_f64() * 1_000.0
        }
        #[cfg(target_arch = "wasm32")]
        {
            (js_sys::Date::now() - self.0).max(0.0)
        }
    }
}

fn duration_ms(duration: std::time::Duration) -> f64 {
    duration.as_secs_f64() * 1_000.0
}

#[derive(Debug, Clone, Copy, Default, PartialEq)]
struct RunPhaseTimings {
    source_set_ms: f64,
    infer_lower_ms: f64,
    type_render_ms: f64,
    runtime_lower_ms: f64,
    evidence_plan_ms: f64,
    vm_eval_ms: f64,
    artifact_decode_ms: f64,
    artifact_decode_cache_hit: bool,
    compiled_std_artifacts: usize,
    compiled_std_cache_hit: bool,
}

thread_local! {
    static RUN_CACHE: RefCell<HashMap<RunCacheKey, RunOutput>> = RefCell::new(HashMap::new());
    static PLAYGROUND_STD_ARTIFACT: RefCell<Option<Option<yulang::cache::CachedCompiledUnitArtifact>>> =
        const { RefCell::new(None) };
    static FULL_STD_ARTIFACT: RefCell<Option<Option<yulang::cache::CachedCompiledUnitArtifact>>> =
        const { RefCell::new(None) };
}

#[wasm_bindgen]
pub fn run(source: &str, lang: &str) -> JsValue {
    set_panic_hook();
    to_js_value(&run_inner_with_lang(source, lang))
}

#[wasm_bindgen]
pub fn check(source: &str) -> JsValue {
    set_panic_hook();
    to_js_value(&check_inner(source))
}

#[wasm_bindgen]
pub fn colorize(source: &str) -> JsValue {
    set_panic_hook();
    to_js_value(&colorize_inner(source))
}

#[wasm_bindgen]
pub fn warm_std_cache() -> JsValue {
    set_panic_hook();
    to_js_value(&warm_std_cache_inner())
}

#[wasm_bindgen]
pub fn clear_std_cache() {
    RUN_CACHE.with(|cache| cache.borrow_mut().clear());
}

#[wasm_bindgen]
pub fn embedded_std_compiled_unit_artifact_status() -> JsValue {
    set_panic_hook();
    to_js_value(&embedded_std_status_inner())
}

#[wasm_bindgen(js_name = dumpPoly)]
pub fn dump_poly(source: &str) -> JsValue {
    set_panic_hook();
    to_js_value(&dump_poly_inner(source))
}

#[wasm_bindgen(js_name = dumpMono)]
pub fn dump_mono(source: &str) -> JsValue {
    set_panic_hook();
    to_js_value(&dump_mono_inner(source))
}

#[wasm_bindgen(js_name = stdFileCount)]
pub fn std_file_count() -> usize {
    yulang::stdlib::embedded_std_files().len()
}

pub fn colorize_inner(source: &str) -> ColorizeOutput {
    let spans = colorize_with_playground_op_table(source)
        .unwrap_or_else(|| colorize_with_default_op_table(source));
    // The playground calls this on the browser main thread. Keep whole-program
    // diagnostics on the explicit `check` export rather than blocking syntax highlighting.
    ColorizeOutput {
        ok: true,
        spans,
        diagnostics: Vec::new(),
        source_len: source.len(),
    }
}

fn colorize_with_playground_op_table(source: &str) -> Option<Vec<HighlightSpan>> {
    let root =
        yulang::load_source_text_with_embedded_playground_std(PLAYGROUND_ENTRY, source.to_owned())
            .ok()?
            .into_iter()
            .find(|file| file.module_path.segments.is_empty())?;
    if !root.source.ends_with(source) {
        return None;
    }
    let prefix_len = root.source.len().checked_sub(source.len())?;
    let root_node = SyntaxNode::<YulangLanguage>::new_root(root.cst);
    let encoded = semantic_tokens::compute_with_root_and_highlights(&root.source, &root_node, None);
    Some(semantic_highlight_spans(
        source,
        &root.source,
        prefix_len,
        &encoded,
    ))
}

fn colorize_with_default_op_table(source: &str) -> Vec<HighlightSpan> {
    let encoded = semantic_tokens::compute(source);
    semantic_highlight_spans(source, source, 0, &encoded)
}

fn semantic_highlight_spans(
    source: &str,
    parsed_source: &str,
    source_offset_bytes: usize,
    encoded: &[u32],
) -> Vec<HighlightSpan> {
    let line_starts = line_utf16_starts(parsed_source);
    let source_offset = parsed_source[..source_offset_bytes.min(parsed_source.len())]
        .encode_utf16()
        .count();
    let source_len = source.encode_utf16().count();
    let mut line = 0usize;
    let mut col = 0usize;
    let mut spans = Vec::new();

    for chunk in encoded.chunks_exact(5) {
        let delta_line = chunk[0] as usize;
        let delta_col = chunk[1] as usize;
        line += delta_line;
        if delta_line == 0 {
            col += delta_col;
        } else {
            col = delta_col;
        }

        let Some(line_start) = line_starts.get(line).copied() else {
            continue;
        };
        let Some(kind) = highlight_kind_from_token_type(chunk[3]) else {
            continue;
        };
        let start = line_start + col;
        let end = start + chunk[2] as usize;
        if start < source_offset || end <= source_offset {
            continue;
        }
        let start = start - source_offset;
        let end = end - source_offset;
        if source_len < start || source_len < end {
            continue;
        }
        spans.push(HighlightSpan { start, end, kind });
    }

    spans
}

pub fn warm_std_cache_inner() -> WarmupOutput {
    let started = ClockInstant::now();
    let status = embedded_std_status_inner();
    let (prefix_fallback_reason, prefix_import_ms) = warm_embedded_std_prefixes();
    let fallback_reason = status.fallback_reason.or(prefix_fallback_reason);
    WarmupOutput {
        source_cache_hits: status.cache_hits,
        source_cache_misses: status.cache_misses,
        source_cache_clone_ms: status.clone_ms,
        source_cache_build_ms: prefix_import_ms,
        embedded_std_artifacts: status.artifacts,
        embedded_std_runtime_bindings: status.runtime_bindings,
        embedded_std_artifacts_bytes: status.bytes,
        embedded_std_artifacts_valid: status.valid && fallback_reason.is_none(),
        embedded_std_artifacts_fallback_reason: fallback_reason,
        artifact_decode_ms: status.decode_ms,
        prefix_import_ms,
        total_ms: started.elapsed_ms(),
        worker_wall_ms: 0.0,
    }
}

fn warm_embedded_std_prefixes() -> (Option<String>, f64) {
    let started = ClockInstant::now();
    let mut errors = Vec::new();
    match embedded_playground_std_artifact().artifact {
        Some(artifact) => {
            if let Err(error) =
                yulang::warm_embedded_playground_std_compiled_unit_artifact_prefix(artifact)
            {
                errors.push(format!("embedded playground std prefix: {error}"));
            }
        }
        None => errors.push("embedded playground std artifact failed validation".to_string()),
    }
    match embedded_full_std_artifact().artifact {
        Some(artifact) => {
            if let Err(error) = yulang::warm_embedded_std_compiled_unit_artifact_prefix(artifact) {
                errors.push(format!("embedded full std prefix: {error}"));
            }
        }
        None => errors.push("embedded full std artifact failed validation".to_string()),
    }
    (
        (!errors.is_empty()).then(|| errors.join("; ")),
        started.elapsed_ms(),
    )
}

pub fn embedded_std_status_inner() -> EmbeddedStdArtifactsOutput {
    let playground = embedded_playground_std_artifact();
    let full = embedded_full_std_artifact();
    let valid = playground.artifact.is_some() && full.artifact.is_some();
    EmbeddedStdArtifactsOutput {
        artifacts: usize::from(playground.artifact.is_some())
            + usize::from(full.artifact.is_some()),
        runtime_bindings: 0,
        bytes: EMBEDDED_PLAYGROUND_STD_ARTIFACT.len() + EMBEDDED_FULL_STD_ARTIFACT.len(),
        valid,
        fallback_reason: (!valid).then(|| "embedded std artifact failed validation".to_string()),
        cache_hits: usize::from(playground.cache_hit) + usize::from(full.cache_hit),
        cache_misses: usize::from(!playground.cache_hit) + usize::from(!full.cache_hit),
        decode_ms: playground.decode_ms + full.decode_ms,
        clone_ms: playground.clone_ms + full.clone_ms,
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct RunCacheKey {
    source: String,
    print_nth_label: &'static str,
}

pub fn run_inner(source: &str) -> RunOutput {
    run_inner_with_lang(source, "en")
}

pub fn run_inner_with_lang(source: &str, lang: &str) -> RunOutput {
    let started = ClockInstant::now();
    let print_nth_label = print_nth_label_for_lang(lang);
    let cache_key = RunCacheKey {
        source: source.to_string(),
        print_nth_label,
    };
    let cached = RUN_CACHE.with(|cache| cache.borrow().get(&cache_key).cloned());
    if let Some(mut output) = cached {
        if let Some(timings) = output.timings.as_mut() {
            timings.mark_source_cache_hit(started.elapsed_ms());
        }
        return output;
    }

    let mut output = run_inner_uncached(source, print_nth_label);
    if let Some(timings) = output.timings.as_mut() {
        timings.mark_source_cache_miss(started.elapsed_ms());
    }
    if output.cache_safe() {
        RUN_CACHE.with(|cache| {
            cache.borrow_mut().insert(cache_key, output.clone());
        });
    }
    output
}

fn print_nth_label_for_lang(lang: &str) -> &'static str {
    match lang {
        "ja" => "出力",
        _ => "Out",
    }
}

pub fn check_inner(source: &str) -> CheckOutput {
    match yulang::check_poly_from_source_text_with_embedded_std(PLAYGROUND_ENTRY, source) {
        Ok(output) => {
            let diagnostics =
                diagnostics_from_source_diagnostics(&output.diagnostics, source.len());
            CheckOutput {
                ok: diagnostics.is_empty(),
                file_count: output.file_count,
                text: output.text,
                diagnostics,
            }
        }
        Err(error) => CheckOutput::from_error(error.to_string(), source.len()),
    }
}

pub fn dump_poly_inner(source: &str) -> DumpOutput {
    match yulang::dump_poly_from_source_text_with_embedded_std(PLAYGROUND_ENTRY, source) {
        Ok(output) => DumpOutput::from_dump(output.file_count, output.text, output.errors, source),
        Err(error) => DumpOutput::from_error(error.to_string(), source.len()),
    }
}

pub fn dump_mono_inner(source: &str) -> DumpOutput {
    match yulang::dump_mono_from_source_text_with_embedded_std(PLAYGROUND_ENTRY, source) {
        Ok(output) => DumpOutput::from_dump(output.file_count, output.text, output.errors, source),
        Err(error) => DumpOutput::from_error(error.to_string(), source.len()),
    }
}

fn run_inner_uncached(source: &str, print_nth_label: &str) -> RunOutput {
    match run_evidence_from_source_text_without_std(source, print_nth_label) {
        Ok(output) if output.errors.is_empty() => {
            return RunOutput::from_runtime_output(output, source, false);
        }
        Ok(output) if should_retry_with_embedded_std(source, &output.errors) => {
            return run_with_embedded_std_fallback(source, None, print_nth_label);
        }
        Ok(output) => return RunOutput::from_runtime_output(output, source, false),
        Err(_) if source_likely_needs_embedded_std(source) => {
            return run_with_embedded_std_fallback(source, None, print_nth_label);
        }
        Err(no_std_error) => {
            return run_with_embedded_std_fallback(source, Some(no_std_error), print_nth_label);
        }
    }
}

fn run_with_embedded_std_fallback(
    source: &str,
    no_std_error: Option<WasmRuntimeError>,
    print_nth_label: &str,
) -> RunOutput {
    if !yulang::source_text_needs_full_embedded_std_for_playground(source) {
        match run_evidence_from_source_text_with_playground_std(source, print_nth_label) {
            Ok(output) if output.errors.is_empty() => {
                return RunOutput::from_runtime_output(output, source, true);
            }
            Ok(_) | Err(_) => {}
        }
    }

    match run_evidence_from_source_text_with_embedded_std(source, print_nth_label) {
        Ok(output) => RunOutput::from_runtime_output(output, source, true),
        Err(std_error) => {
            if let Some(output) = run_output_from_lowering_diagnostics(source, &std_error) {
                return output;
            }
            let error = preferred_runtime_error(std_error, no_std_error);
            RunOutput::from_runtime_error(error, source.len())
        }
    }
}

fn preferred_runtime_error(
    embedded_std_error: WasmRuntimeError,
    no_std_error: Option<WasmRuntimeError>,
) -> WasmRuntimeError {
    match no_std_error {
        Some(no_std_error)
            if no_std_error.has_stable_diagnostic()
                || !embedded_std_error.has_stable_diagnostic() =>
        {
            no_std_error
        }
        _ => embedded_std_error,
    }
}

fn run_output_from_lowering_diagnostics(
    source: &str,
    error: &WasmRuntimeError,
) -> Option<RunOutput> {
    if !matches!(
        error,
        WasmRuntimeError::Route(yulang::RouteError::LoweringDiagnostics { .. })
    ) {
        return None;
    }

    let output =
        yulang::check_poly_from_source_text_with_embedded_std(PLAYGROUND_ENTRY, source).ok()?;
    if output.diagnostics.is_empty() {
        return None;
    }
    Some(RunOutput::from_check_output(output, source))
}

fn run_evidence_from_source_text_without_std(
    source: &str,
    print_nth_label: &str,
) -> Result<WasmRuntimeOutput, WasmRuntimeError> {
    let source_started = ClockInstant::now();
    let files = yulang::collect_local_source_text(PLAYGROUND_ENTRY, source.to_string())?;
    let source_set_ms = source_started.elapsed_ms();
    let (poly, lowering_timing) =
        yulang::build_poly_from_collected_sources_with_lowering_timing(files)?;
    let timing = RunPhaseTimings {
        source_set_ms,
        infer_lower_ms: duration_ms(lowering_timing.total),
        ..RunPhaseTimings::default()
    };
    let output = build_named_runtime_from_poly(poly, timing)?;
    run_built_evidence_program(output, print_nth_label)
}

fn run_evidence_from_source_text_with_embedded_std(
    source: &str,
    print_nth_label: &str,
) -> Result<WasmRuntimeOutput, WasmRuntimeError> {
    let EmbeddedArtifactLookup {
        artifact,
        cache_hit,
        decode_ms,
        ..
    } = embedded_full_std_artifact();
    let output = match artifact {
        Some(artifact) => {
            let (mut poly, lowering_timing) =
                yulang::build_poly_from_embedded_std_compiled_unit_artifact_with_lowering_timing(
                    artifact,
                    source.to_string(),
                )?;
            attach_playground_runtime_diagnostic_source(&mut poly, source);
            let timing = RunPhaseTimings {
                infer_lower_ms: duration_ms(lowering_timing.total),
                artifact_decode_ms: decode_ms,
                artifact_decode_cache_hit: cache_hit,
                compiled_std_artifacts: 1,
                compiled_std_cache_hit: true,
                ..RunPhaseTimings::default()
            };
            build_named_runtime_from_poly(poly, timing)?
        }
        None => {
            let build_started = ClockInstant::now();
            let (poly, lowering_timing) =
                yulang::build_poly_from_source_text_with_embedded_std_with_lowering_timing(
                    PLAYGROUND_ENTRY,
                    source.to_string(),
                )?;
            let infer_lower_ms = duration_ms(lowering_timing.total);
            let timing = RunPhaseTimings {
                source_set_ms: (build_started.elapsed_ms() - infer_lower_ms).max(0.0),
                infer_lower_ms,
                artifact_decode_ms: decode_ms,
                artifact_decode_cache_hit: cache_hit,
                ..RunPhaseTimings::default()
            };
            build_named_runtime_from_poly(poly, timing)?
        }
    };
    run_built_evidence_program(output, print_nth_label)
}

fn run_evidence_from_source_text_with_playground_std(
    source: &str,
    print_nth_label: &str,
) -> Result<WasmRuntimeOutput, WasmRuntimeError> {
    let EmbeddedArtifactLookup {
        artifact,
        cache_hit,
        decode_ms,
        ..
    } = embedded_playground_std_artifact();
    let (poly, timing) = match artifact {
        Some(artifact) => {
            let (mut poly, lowering_timing) = yulang::
                build_poly_from_embedded_playground_std_compiled_unit_artifact_with_lowering_timing(
                    artifact,
                    source.to_string(),
                )?;
            attach_playground_runtime_diagnostic_source(&mut poly, source);
            let timing = RunPhaseTimings {
                infer_lower_ms: duration_ms(lowering_timing.total),
                artifact_decode_ms: decode_ms,
                artifact_decode_cache_hit: cache_hit,
                compiled_std_artifacts: 1,
                compiled_std_cache_hit: true,
                ..RunPhaseTimings::default()
            };
            (poly, timing)
        }
        None => {
            let build_started = ClockInstant::now();
            let (poly, lowering_timing) = yulang::
                build_poly_from_source_text_with_embedded_playground_std_with_lowering_timing(
                    PLAYGROUND_ENTRY,
                    source.to_string(),
                )?;
            let infer_lower_ms = duration_ms(lowering_timing.total);
            let timing = RunPhaseTimings {
                source_set_ms: (build_started.elapsed_ms() - infer_lower_ms).max(0.0),
                infer_lower_ms,
                artifact_decode_ms: decode_ms,
                artifact_decode_cache_hit: cache_hit,
                ..RunPhaseTimings::default()
            };
            (poly, timing)
        }
    };
    let output = build_named_runtime_from_poly(poly, timing)?;
    run_built_evidence_program(output, print_nth_label)
}

fn attach_playground_runtime_diagnostic_source(output: &mut yulang::BuildPolyOutput, source: &str) {
    let root = yulang::CollectedSource::new(
        PLAYGROUND_ENTRY.into(),
        Default::default(),
        format!("{}{source}", yulang::IMPLICIT_PRELUDE_IMPORT),
    );
    output.diagnostic_sources = yulang::RuntimeDiagnosticSources::from_collected_sources(&[root]);
}

#[derive(Clone)]
struct EmbeddedArtifactLookup {
    artifact: Option<yulang::cache::CachedCompiledUnitArtifact>,
    cache_hit: bool,
    decode_ms: f64,
    clone_ms: f64,
}

fn embedded_playground_std_artifact() -> EmbeddedArtifactLookup {
    let started = ClockInstant::now();
    PLAYGROUND_STD_ARTIFACT.with(|cache| {
        if let Some(cached) = cache.borrow().as_ref() {
            return EmbeddedArtifactLookup {
                artifact: cached.clone(),
                cache_hit: true,
                decode_ms: 0.0,
                clone_ms: started.elapsed_ms(),
            };
        }

        let decoded = decode_embedded_playground_std_artifact();
        *cache.borrow_mut() = Some(decoded.clone());
        EmbeddedArtifactLookup {
            artifact: decoded,
            cache_hit: false,
            decode_ms: started.elapsed_ms(),
            clone_ms: 0.0,
        }
    })
}

fn embedded_full_std_artifact() -> EmbeddedArtifactLookup {
    let started = ClockInstant::now();
    FULL_STD_ARTIFACT.with(|cache| {
        if let Some(cached) = cache.borrow().as_ref() {
            return EmbeddedArtifactLookup {
                artifact: cached.clone(),
                cache_hit: true,
                decode_ms: 0.0,
                clone_ms: started.elapsed_ms(),
            };
        }

        let decoded = decode_embedded_full_std_artifact();
        *cache.borrow_mut() = Some(decoded.clone());
        EmbeddedArtifactLookup {
            artifact: decoded,
            cache_hit: false,
            decode_ms: started.elapsed_ms(),
            clone_ms: 0.0,
        }
    })
}

fn decode_embedded_playground_std_artifact() -> Option<yulang::cache::CachedCompiledUnitArtifact> {
    let files = yulang::collect_source_text_with_embedded_playground_std(
        PLAYGROUND_STD_ARTIFACT_ENTRY,
        String::new(),
    )
    .ok()?;
    let key = yulang::cache::source_cache_key(&files);
    let artifact =
        yulang::cache::decode_compiled_unit_artifact_bytes(EMBEDDED_PLAYGROUND_STD_ARTIFACT, key)
            .ok()
            .flatten()?;
    artifact.errors.is_empty().then_some(artifact)
}

fn decode_embedded_full_std_artifact() -> Option<yulang::cache::CachedCompiledUnitArtifact> {
    let files =
        yulang::collect_source_text_with_embedded_std(FULL_STD_ARTIFACT_ENTRY, String::new())
            .ok()?;
    let key = yulang::cache::source_cache_key(&files);
    let artifact =
        yulang::cache::decode_compiled_unit_artifact_bytes(EMBEDDED_FULL_STD_ARTIFACT, key)
            .ok()
            .flatten()?;
    artifact.errors.is_empty().then_some(artifact)
}

#[derive(Debug, Clone, PartialEq)]
struct NamedRuntimeBuild {
    output: yulang::BuildControlOutput,
    types: Vec<TypeResult>,
    display: PlaygroundDisplayContext,
    timing: RunPhaseTimings,
}

fn build_named_runtime_from_poly(
    poly: yulang::BuildPolyOutput,
    mut timing: RunPhaseTimings,
) -> Result<NamedRuntimeBuild, yulang::RouteError> {
    let type_started = ClockInstant::now();
    let display = PlaygroundDisplayContext::from_poly(&poly);
    let types = exported_type_results(&poly, &display);
    timing.type_render_ms = type_started.elapsed_ms();
    let runtime_started = ClockInstant::now();
    let output = yulang::build_control_from_poly_output(&poly)?;
    timing.runtime_lower_ms = runtime_started.elapsed_ms();
    Ok(NamedRuntimeBuild {
        output,
        types,
        display,
        timing,
    })
}

fn exported_type_results(
    poly: &yulang::BuildPolyOutput,
    display: &PlaygroundDisplayContext,
) -> Vec<TypeResult> {
    poly.arena
        .roots
        .iter()
        .filter_map(|def| exported_type_result(poly, display, *def))
        .collect()
}

fn exported_type_result(
    poly: &yulang::BuildPolyOutput,
    display: &PlaygroundDisplayContext,
    def: poly::expr::DefId,
) -> Option<TypeResult> {
    let Def::Let {
        vis,
        scheme: Some(scheme),
        ..
    } = poly.arena.defs.get(def)?
    else {
        return None;
    };
    if !matches!(vis, Vis::Pub | Vis::Our) {
        return None;
    }
    let name = poly
        .labels
        .def_label(def)
        .map(str::to_string)
        .unwrap_or_else(|| format!("d{}", def.0));
    let ty =
        poly::dump::format_scheme_public_with_path_rewriter(&poly.arena.typ, scheme, &|path| {
            display.rewrite_type_path(path)
        })
        .text;
    Some(TypeResult { name, ty })
}

fn run_built_evidence_program(
    mut build: NamedRuntimeBuild,
    print_nth_label: &str,
) -> Result<WasmRuntimeOutput, WasmRuntimeError> {
    let plan_started = ClockInstant::now();
    let plan = evidence_vm::build_plan(&build.output.program, &build.output.runtime_evidence);
    build.timing.evidence_plan_ms = plan_started.elapsed_ms();
    let eval_started = ClockInstant::now();
    let output = match evidence_vm::run_program_with_plan_print_nth_label(
        &build.output.program,
        &plan,
        print_nth_label,
    ) {
        Ok(output) => output,
        Err(error) => {
            let diagnostic = runtime_evidence_source_diagnostic(
                &error,
                &build.output.application_provenance,
                &build.output.selection_provenance,
                &build.output.diagnostic_sources,
            );
            return Err(WasmRuntimeError::Runtime(diagnostic));
        }
    };
    build.timing.vm_eval_ms = eval_started.elapsed_ms();
    let runtime_display = build.display.runtime_evidence_context();
    let all_root_value_texts =
        output.root_value_texts_with_display_context(Some(&build.output.labels), &runtime_display);
    let results = playground_visible_root_value_texts(
        build.output.program.roots.len(),
        output.last_root_produced_value,
        all_root_value_texts,
    );
    let text = output.roots_text_with_display_context(Some(&build.output.labels), &runtime_display);
    Ok(WasmRuntimeOutput {
        file_count: build.output.file_count,
        errors: build.output.errors,
        text,
        results,
        types: build.types,
        stdout: output.stdout,
        stats: output.evidence_stats,
        timing: build.timing,
    })
}

fn playground_visible_root_value_texts(
    root_count: usize,
    last_root_produced_value: bool,
    mut all_root_value_texts: Vec<String>,
) -> Vec<String> {
    if root_count == 0 || !last_root_produced_value {
        return Vec::new();
    }
    all_root_value_texts.pop().into_iter().collect()
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct PlaygroundDisplayContext {
    constructors: HashMap<u32, String>,
    type_paths: ShortPathIndex,
}

impl PlaygroundDisplayContext {
    fn from_poly(poly: &yulang::BuildPolyOutput) -> Self {
        let constructor_paths = poly
            .arena
            .constructors
            .iter()
            .map(|(def, constructor)| (*def, constructor_full_path(constructor)))
            .collect::<Vec<_>>();
        let value_paths = ShortPathIndex::new(constructor_paths.iter().map(|(_, path)| path));
        let constructors = constructor_paths
            .into_iter()
            .map(|(def, path)| (def.0, value_paths.rewrite(&path).join("::")))
            .collect();

        let type_paths = ShortPathIndex::new(collect_type_display_paths(poly).iter());

        Self {
            constructors,
            type_paths,
        }
    }

    fn runtime_evidence_context(&self) -> evidence_vm::RuntimeEvidenceDisplayContext {
        let mut context = evidence_vm::RuntimeEvidenceDisplayContext::new();
        for (def, name) in &self.constructors {
            context.set_constructor_name_id(*def, name.clone());
        }
        context
    }

    fn rewrite_type_path(&self, path: &[String]) -> Vec<String> {
        self.type_paths.rewrite(path)
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct ShortPathIndex {
    rewrites: HashMap<Vec<String>, Vec<String>>,
}

impl ShortPathIndex {
    fn new<'a>(paths: impl IntoIterator<Item = &'a Vec<String>>) -> Self {
        let mut unique_paths = paths
            .into_iter()
            .filter(|path| !path.is_empty())
            .cloned()
            .collect::<Vec<_>>();
        unique_paths.sort();
        unique_paths.dedup();

        let mut suffix_counts: HashMap<Vec<String>, usize> = HashMap::new();
        for path in &unique_paths {
            for start in 0..path.len() {
                *suffix_counts.entry(path[start..].to_vec()).or_default() += 1;
            }
        }

        let rewrites = unique_paths
            .into_iter()
            .map(|path| {
                let suffix = (0..path.len())
                    .rev()
                    .map(|start| path[start..].to_vec())
                    .find(|suffix| suffix_counts.get(suffix) == Some(&1))
                    .unwrap_or_else(|| path.clone());
                (path, suffix)
            })
            .collect();

        Self { rewrites }
    }

    fn rewrite(&self, path: &[String]) -> Vec<String> {
        self.rewrites
            .get(path)
            .cloned()
            .unwrap_or_else(|| path.to_vec())
    }
}

fn constructor_full_path(constructor: &poly::expr::Constructor) -> Vec<String> {
    let mut path = constructor.owner_path.clone();
    path.push(constructor.name.clone());
    path
}

fn collect_type_display_paths(poly: &yulang::BuildPolyOutput) -> Vec<Vec<String>> {
    let mut paths = Vec::new();
    for node in poly.arena.typ.pos_nodes() {
        collect_pos_type_paths(node, &mut paths);
    }
    for node in poly.arena.typ.neg_nodes() {
        collect_neg_type_paths(node, &mut paths);
    }
    for node in poly.arena.typ.neu_nodes() {
        collect_neu_type_paths(node, &mut paths);
    }
    for (_, def) in poly.arena.defs.iter() {
        if let Def::Let {
            scheme: Some(scheme),
            ..
        } = def
        {
            for predicate in &scheme.role_predicates {
                paths.push(predicate.role.clone());
            }
        }
    }
    paths
}

fn collect_pos_type_paths(node: &Pos, paths: &mut Vec<Vec<String>>) {
    match node {
        Pos::Con(path, _) => paths.push(path.clone()),
        Pos::Stack { weight, .. } | Pos::NonSubtract(_, weight) => {
            collect_stack_weight_paths(weight, paths);
        }
        _ => {}
    }
}

fn collect_neg_type_paths(node: &Neg, paths: &mut Vec<Vec<String>>) {
    match node {
        Neg::Con(path, _) => paths.push(path.clone()),
        Neg::Stack { weight, .. } => collect_stack_weight_paths(weight, paths),
        _ => {}
    }
}

fn collect_neu_type_paths(node: &Neu, paths: &mut Vec<Vec<String>>) {
    if let Neu::Con(path, _) = node {
        paths.push(path.clone());
    }
}

fn collect_stack_weight_paths(weight: &StackWeight, paths: &mut Vec<Vec<String>>) {
    collect_subtractability_paths(weight.filter_set(), paths);
    for entry in weight.entries() {
        for bound in entry.floor.iter().chain(entry.stack.iter()) {
            collect_subtractability_paths(bound, paths);
        }
    }
}

fn collect_subtractability_paths(value: &Subtractability, paths: &mut Vec<Vec<String>>) {
    match value {
        Subtractability::Empty | Subtractability::All => {}
        Subtractability::Set(path, _) | Subtractability::AllExcept(path, _) => {
            paths.push(path.clone());
        }
        Subtractability::SetMany(families) | Subtractability::AllExceptMany(families) => {
            paths.extend(families.iter().map(|(path, _)| path.clone()));
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
struct WasmRuntimeOutput {
    file_count: usize,
    errors: Vec<String>,
    text: String,
    results: Vec<String>,
    types: Vec<TypeResult>,
    stdout: String,
    stats: evidence_vm::RuntimeEvidenceRunStats,
    timing: RunPhaseTimings,
}

#[derive(Debug)]
enum WasmRuntimeError {
    Route(yulang::RouteError),
    Runtime(RuntimeSourceDiagnostic),
}

impl From<yulang::RouteError> for WasmRuntimeError {
    fn from(error: yulang::RouteError) -> Self {
        Self::Route(error)
    }
}

impl WasmRuntimeError {
    fn has_stable_diagnostic(&self) -> bool {
        matches!(
            self,
            Self::Runtime(_) | Self::Route(yulang::RouteError::Runtime(_))
        )
    }

    fn into_source_diagnostic(self) -> RuntimeSourceDiagnostic {
        match self {
            Self::Route(yulang::RouteError::Runtime(error)) => {
                mono_runtime_source_diagnostic(&error)
            }
            Self::Route(yulang::RouteError::SpecializeDiagnostic { error, context }) => {
                ranged_specialize_source_diagnostic(&error, &context)
                    .unwrap_or_else(|| RuntimeSourceDiagnostic::new(None, error.to_string(), None))
            }
            Self::Route(yulang::RouteError::Specialize(error)) => {
                specialize_source_diagnostic(&error)
                    .unwrap_or_else(|| RuntimeSourceDiagnostic::new(None, error.to_string(), None))
            }
            Self::Route(error) => RuntimeSourceDiagnostic::new(None, error.to_string(), None),
            Self::Runtime(diagnostic) => diagnostic,
        }
    }
}

#[derive(Debug)]
struct RuntimeSourceDiagnostic {
    diagnostic: yulang::SourceDiagnostic,
    range_offset: usize,
}

impl RuntimeSourceDiagnostic {
    fn new(code: Option<&str>, message: String, hint: Option<&str>) -> Self {
        Self {
            diagnostic: yulang::SourceDiagnostic {
                severity: yulang::SourceDiagnosticSeverity::Error,
                code: code.map(str::to_string),
                label: None,
                file: None,
                range: None,
                message,
                hint: hint.map(str::to_string),
                related: Vec::new(),
            },
            range_offset: 0,
        }
    }
}

fn ranged_specialize_source_diagnostic(
    error: &specialize::SpecializeError,
    context: &yulang::source::SpecializeDiagnosticContext,
) -> Option<RuntimeSourceDiagnostic> {
    if !matches!(
        error,
        specialize::SpecializeError::UnsatisfiedSubtype {
            origin: Some(specialize::UnsatisfiedSubtypeOrigin::MissingRecordField { .. }),
            ..
        } | specialize::SpecializeError::UnsatisfiedSubtype {
            origin: None,
            provenance: Some(_),
            ..
        } | specialize::SpecializeError::UnresolvedTypeclassMethod { .. }
            | specialize::SpecializeError::AmbiguousTypeclassMethod { .. }
    ) {
        return None;
    }

    let mut diagnostic = specialize_source_diagnostic(error)?;
    let has_primary_range = !matches!(
        error,
        specialize::SpecializeError::UnsatisfiedSubtype {
            origin: None,
            provenance: Some(_),
            ..
        }
    );
    diagnostic.diagnostic.file = has_primary_range.then(|| context.file.clone());
    diagnostic.diagnostic.range = has_primary_range.then_some(context.range);
    diagnostic.diagnostic.related = context.related.clone();
    diagnostic.range_offset = context.source.range_offset;
    Some(diagnostic)
}

fn specialize_source_diagnostic(
    error: &specialize::SpecializeError,
) -> Option<RuntimeSourceDiagnostic> {
    match error {
        specialize::SpecializeError::UnsatisfiedSubtype {
            origin:
                Some(specialize::UnsatisfiedSubtypeOrigin::MissingRecordField {
                    field,
                    actual_fields,
                    ..
                }),
            ..
        } => {
            let actual = describe_actual_record_fields(actual_fields);
            let hint = format!(
                "add `{field}` to this record or use a value that provides it; actual record has {actual}"
            );
            Some(RuntimeSourceDiagnostic::new(
                Some("yulang.unsatisfied-subtype"),
                format!("record is missing field `{field}`"),
                Some(&hint),
            ))
        }
        specialize::SpecializeError::UnsatisfiedSubtype {
            origin: None,
            provenance: Some(_),
            ..
        } => Some(RuntimeSourceDiagnostic::new(
            Some("yulang.unsatisfied-subtype"),
            error.to_string(),
            Some("check that the value provides the fields or shape required by this use"),
        )),
        specialize::SpecializeError::UnsatisfiedSubtype { .. } => {
            Some(RuntimeSourceDiagnostic::new(
                Some("yulang.unsatisfied-subtype"),
                "value does not satisfy the required type or record shape".to_string(),
                Some("check that the value provides the fields or shape required by this use"),
            ))
        }
        specialize::SpecializeError::UnresolvedTypeclassMethod { .. } => {
            Some(RuntimeSourceDiagnostic::new(
                Some("yulang.unresolved-method"),
                "no role implementation satisfies this method call".to_string(),
                Some(
                    "add or import an impl for the receiver type, or call a method supported by that value",
                ),
            ))
        }
        specialize::SpecializeError::AmbiguousTypeclassMethod { .. } => {
            Some(RuntimeSourceDiagnostic::new(
                Some("yulang.ambiguous-method"),
                "more than one role implementation satisfies this method call".to_string(),
                Some(
                    "make the receiver type more specific or keep only one matching impl in scope",
                ),
            ))
        }
        _ => None,
    }
}

fn describe_actual_record_fields(actual_fields: &[String]) -> String {
    if actual_fields.is_empty() {
        "no fields".to_string()
    } else {
        format!("fields {}", actual_fields.join(", "))
    }
}

fn runtime_evidence_source_diagnostic(
    error: &evidence_vm::RuntimeEvidenceRunError,
    application_provenance: &yulang::RuntimeApplicationProvenance,
    selection_provenance: &yulang::RuntimeSelectionProvenance,
    diagnostic_sources: &yulang::RuntimeDiagnosticSources,
) -> RuntimeSourceDiagnostic {
    match error {
        evidence_vm::RuntimeEvidenceRunError::EscapedEffect { site, path } => {
            let diagnostic = RuntimeSourceDiagnostic::new(
                Some("yulang.unhandled-effect"),
                format!("unhandled effect request {}", path.join("::")),
                Some("handle this computation with a matching effect handler before running it"),
            );
            runtime_application_diagnostic(
                diagnostic,
                *site,
                application_provenance,
                diagnostic_sources,
            )
        }
        evidence_vm::RuntimeEvidenceRunError::UnsupportedHostCapability { site, path } => {
            let diagnostic = RuntimeSourceDiagnostic::new(
                Some("yulang.unsupported-host-capability"),
                format!(
                    "host capability {} is not available in this runtime",
                    path.join("::")
                ),
                Some(
                    "use a host that grants this capability or handle the capability with a mock effect handler",
                ),
            );
            runtime_application_diagnostic(
                diagnostic,
                *site,
                application_provenance,
                diagnostic_sources,
            )
        }
        evidence_vm::RuntimeEvidenceRunError::HostIoError {
            operation,
            path,
            kind,
        } => RuntimeSourceDiagnostic::new(
            Some("yulang.host-io-error"),
            format!(
                "host operation {} failed for {path} ({kind})",
                operation.join("::")
            ),
            Some(
                "check that the target path exists and that this process has the required file permissions",
            ),
        ),
        evidence_vm::RuntimeEvidenceRunError::HostAbiError { operation, message } => {
            RuntimeSourceDiagnostic::new(
                Some("yulang.host-abi-error"),
                format!("host operation {} failed ({message})", operation.join("::")),
                Some("this host implementation returned a value outside its ABI contract"),
            )
        }
        evidence_vm::RuntimeEvidenceRunError::NotFunction { site, value } => {
            let diagnostic = RuntimeSourceDiagnostic::new(
                Some("yulang.not-callable"),
                format!("tried to call a non-function value {value}"),
                Some(
                    "check the expression before the argument; calls are written as `f x` or `f(...)`",
                ),
            );
            runtime_application_diagnostic(
                diagnostic,
                *site,
                application_provenance,
                diagnostic_sources,
            )
        }
        evidence_vm::RuntimeEvidenceRunError::NotRecord { site, value } => {
            let diagnostic = RuntimeSourceDiagnostic::new(
                Some("yulang.not-record"),
                format!("tried to read fields from non-record value {value}"),
                Some("use `.field` only on record values"),
            );
            runtime_selection_diagnostic(
                diagnostic,
                *site,
                selection_provenance,
                diagnostic_sources,
            )
        }
        evidence_vm::RuntimeEvidenceRunError::PatternMismatch => RuntimeSourceDiagnostic::new(
            Some("yulang.pattern-mismatch"),
            "no pattern matched the value".to_string(),
            Some("add a fallback pattern such as `_ -> ...`"),
        ),
        evidence_vm::RuntimeEvidenceRunError::MissingRecordField(name) => {
            RuntimeSourceDiagnostic::new(
                Some("yulang.missing-field"),
                format!("record does not contain field `{name}`"),
                Some("check the field name or provide a record value with this field"),
            )
        }
        evidence_vm::RuntimeEvidenceRunError::DivideByZero => RuntimeSourceDiagnostic::new(
            Some("yulang.divide-by-zero"),
            "attempted to divide by zero".to_string(),
            Some("check the divisor before division"),
        ),
        evidence_vm::RuntimeEvidenceRunError::AssertionFailed { site } => {
            let diagnostic = RuntimeSourceDiagnostic::new(
                Some("yulang.assertion-failed"),
                "assertion evaluated to false".to_string(),
                Some("make the asserted condition true"),
            );
            runtime_application_diagnostic(
                diagnostic,
                *site,
                application_provenance,
                diagnostic_sources,
            )
        }
        evidence_vm::RuntimeEvidenceRunError::AssertionEqualityFailed {
            site,
            expected,
            actual,
        } => {
            let diagnostic = RuntimeSourceDiagnostic::new(
                Some("yulang.assertion-equality-failed"),
                format!(
                    "assertion values are not equal\n  expected: {expected}\n    actual: {actual}"
                ),
                Some("make the expected and actual values equal"),
            );
            runtime_application_diagnostic(
                diagnostic,
                *site,
                application_provenance,
                diagnostic_sources,
            )
        }
        evidence_vm::RuntimeEvidenceRunError::NotThunk(value) => RuntimeSourceDiagnostic::new(
            Some("yulang.runtime-internal"),
            format!("expected a delayed computation, got {value}"),
            Some("report this with the source program if it came from normal `yulang run`"),
        ),
        evidence_vm::RuntimeEvidenceRunError::UnsupportedExpr(feature) => {
            RuntimeSourceDiagnostic::new(
                Some("yulang.unsupported-runtime-feature"),
                format!("unsupported expression in runtime: {feature}"),
                Some("try the interpreter oracle or reduce this source to a smaller report"),
            )
        }
        evidence_vm::RuntimeEvidenceRunError::UnsupportedPrimitive(op) => {
            RuntimeSourceDiagnostic::new(
                Some("yulang.unsupported-runtime-feature"),
                format!("unsupported primitive in runtime: {op:?}"),
                Some("this primitive is not available in the selected runtime"),
            )
        }
        evidence_vm::RuntimeEvidenceRunError::MissingExpr(_)
        | evidence_vm::RuntimeEvidenceRunError::MissingInstance(_)
        | evidence_vm::RuntimeEvidenceRunError::MismatchedInstanceSlot { .. }
        | evidence_vm::RuntimeEvidenceRunError::RecursiveInstance(_)
        | evidence_vm::RuntimeEvidenceRunError::UnboundLocal(_)
        | evidence_vm::RuntimeEvidenceRunError::PrintNthNondetTerminal => {
            RuntimeSourceDiagnostic::new(
                Some("yulang.runtime-internal"),
                error.to_string(),
                Some("report this with the source program if it came from normal `yulang run`"),
            )
        }
    }
}

fn runtime_application_diagnostic(
    mut diagnostic: RuntimeSourceDiagnostic,
    site: Option<control_ir::ExprId>,
    application_provenance: &yulang::RuntimeApplicationProvenance,
    diagnostic_sources: &yulang::RuntimeDiagnosticSources,
) -> RuntimeSourceDiagnostic {
    let Some(site) = site else {
        return diagnostic;
    };
    let Some(provenance) = application_provenance.resolve(site) else {
        return diagnostic;
    };
    if provenance.callee_span.file != provenance.application_span.file {
        return diagnostic;
    }
    let Some(source) = diagnostic_sources.source_for_span(&provenance.callee_span) else {
        return diagnostic;
    };

    diagnostic.diagnostic.file = Some(provenance.callee_span.file.clone());
    diagnostic.diagnostic.range = Some(provenance.callee_span.range);
    diagnostic.diagnostic.related = vec![yulang::SourceDiagnosticRelated {
        message: "application occurs here".to_string(),
        file: provenance.application_span.file.clone(),
        range: provenance.application_span.range,
        origin: Some(yulang::SourceDiagnosticRelatedOrigin::Expression),
    }];
    diagnostic.range_offset = source.source.range_offset;
    diagnostic
}

fn runtime_selection_diagnostic(
    mut diagnostic: RuntimeSourceDiagnostic,
    site: Option<control_ir::ExprId>,
    selection_provenance: &yulang::RuntimeSelectionProvenance,
    diagnostic_sources: &yulang::RuntimeDiagnosticSources,
) -> RuntimeSourceDiagnostic {
    let Some(site) = site else {
        return diagnostic;
    };
    let Some(provenance) = selection_provenance.resolve(site) else {
        return diagnostic;
    };
    let Some(source) = diagnostic_sources.source_for_span(provenance) else {
        return diagnostic;
    };

    diagnostic.diagnostic.file = Some(provenance.file.clone());
    diagnostic.diagnostic.range = Some(provenance.range);
    diagnostic.range_offset = source.source.range_offset;
    diagnostic
}

fn mono_runtime_source_diagnostic(error: &mono_runtime::RuntimeError) -> RuntimeSourceDiagnostic {
    match error {
        mono_runtime::RuntimeError::UnhandledEffect { path } => RuntimeSourceDiagnostic::new(
            Some("yulang.unhandled-effect"),
            format!("unhandled effect request {}", path.join("::")),
            Some("handle this computation with a matching effect handler before running it"),
        ),
        mono_runtime::RuntimeError::NotFunction { value } => RuntimeSourceDiagnostic::new(
            Some("yulang.not-callable"),
            format!(
                "tried to call a non-function value {}",
                format_mono_runtime_value(value)
            ),
            Some(
                "check the expression before the argument; calls are written as `f x` or `f(...)`",
            ),
        ),
        mono_runtime::RuntimeError::ExpectedRecord { value } => RuntimeSourceDiagnostic::new(
            Some("yulang.not-record"),
            format!(
                "tried to read fields from non-record value {}",
                format_mono_runtime_value(value)
            ),
            Some("use `.field` only on record values"),
        ),
        mono_runtime::RuntimeError::MissingRecordField { name } => RuntimeSourceDiagnostic::new(
            Some("yulang.missing-field"),
            format!("record does not contain field `{name}`"),
            Some("check the field name or provide a record value with this field"),
        ),
        mono_runtime::RuntimeError::PatternMismatch
        | mono_runtime::RuntimeError::NoMatchingCase => RuntimeSourceDiagnostic::new(
            Some("yulang.pattern-mismatch"),
            "no pattern matched the value".to_string(),
            Some("add a fallback pattern such as `_ -> ...`"),
        ),
        mono_runtime::RuntimeError::NonBoolGuard { value } => RuntimeSourceDiagnostic::new(
            Some("yulang.non-bool-guard"),
            format!(
                "case guard returned non-bool value {}",
                format_mono_runtime_value(value)
            ),
            Some("make the guard return true or false"),
        ),
        mono_runtime::RuntimeError::ExpectedInt { value } => {
            mono_runtime_type_diagnostic("int", value)
        }
        mono_runtime::RuntimeError::ExpectedFloat { value } => {
            mono_runtime_type_diagnostic("float", value)
        }
        mono_runtime::RuntimeError::ExpectedBool { value } => {
            mono_runtime_type_diagnostic("bool", value)
        }
        mono_runtime::RuntimeError::ExpectedList { value } => {
            mono_runtime_type_diagnostic("list", value)
        }
        mono_runtime::RuntimeError::ExpectedBytes { value } => {
            mono_runtime_type_diagnostic("bytes", value)
        }
        mono_runtime::RuntimeError::UnsupportedExpr { feature }
        | mono_runtime::RuntimeError::UnsupportedPattern { feature }
        | mono_runtime::RuntimeError::UnsupportedBoundary { feature } => {
            RuntimeSourceDiagnostic::new(
                Some("yulang.unsupported-runtime-feature"),
                format!("unsupported runtime feature: {feature}"),
                Some("try the interpreter oracle or reduce this source to a smaller report"),
            )
        }
        mono_runtime::RuntimeError::MissingPrimitiveContext { op }
        | mono_runtime::RuntimeError::UnsupportedPrimitive { op } => RuntimeSourceDiagnostic::new(
            Some("yulang.unsupported-runtime-feature"),
            format!("unsupported primitive in runtime: {op:?}"),
            Some("this primitive is not available in the selected runtime"),
        ),
        mono_runtime::RuntimeError::ExpectedFunctionType
        | mono_runtime::RuntimeError::NotThunk { .. }
        | mono_runtime::RuntimeError::MissingInstance { .. }
        | mono_runtime::RuntimeError::MismatchedInstanceSlot { .. }
        | mono_runtime::RuntimeError::RecursiveInstance { .. }
        | mono_runtime::RuntimeError::UnboundLocal { .. }
        | mono_runtime::RuntimeError::MissingContinuation { .. }
        | mono_runtime::RuntimeError::UnresolvedSelect { .. } => RuntimeSourceDiagnostic::new(
            Some("yulang.runtime-internal"),
            error.to_string(),
            Some("report this with the source program if it came from normal `yulang run`"),
        ),
    }
}

fn mono_runtime_type_diagnostic(
    expected: &str,
    value: &mono_runtime::Value,
) -> RuntimeSourceDiagnostic {
    RuntimeSourceDiagnostic::new(
        Some("yulang.runtime-type"),
        format!(
            "expected {expected}, got {}",
            format_mono_runtime_value(value)
        ),
        Some("check the value passed to this operation"),
    )
}

fn format_mono_runtime_value(value: &mono_runtime::Value) -> String {
    let text = yulang::format_run_mono_values(std::slice::from_ref(value));
    text.strip_prefix("run roots [")
        .and_then(|text| text.strip_suffix("]\n"))
        .unwrap_or(text.trim())
        .to_string()
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct RunOutput {
    pub ok: bool,
    pub file_count: usize,
    pub text: String,
    pub results: Vec<RunResult>,
    pub stdout: String,
    pub types: Vec<TypeResult>,
    pub timings: Option<RunTimings>,
    pub diagnostics: Vec<Diagnostic>,
    pub errors: Vec<String>,
    #[serde(skip)]
    cache_safe: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct RunResult {
    pub index: usize,
    pub value: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct TypeResult {
    pub name: String,
    pub ty: String,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct RunTimings {
    pub source_set_ms: f64,
    pub infer_lower_ms: f64,
    pub type_render_ms: f64,
    pub diagnostics_ms: f64,
    pub export_core_ms: f64,
    pub runtime_lower_ms: f64,
    pub monomorphize_ms: f64,
    pub vm_compile_ms: f64,
    pub evidence_plan_ms: f64,
    pub vm_eval_ms: f64,
    pub artifact_decode_ms: f64,
    pub artifact_decode_cache_hit: bool,
    pub total_ms: f64,
    pub worker_wall_ms: f64,
    pub files: usize,
    pub entry_files: usize,
    pub std_files: usize,
    pub user_files: usize,
    pub source_cache_hits: usize,
    pub source_cache_misses: usize,
    pub source_cache_clone_ms: f64,
    pub source_cache_build_ms: f64,
    pub compiled_std_artifacts: usize,
    pub compiled_std_runtime_bindings: usize,
    pub compiled_std_cache_hit: bool,
    pub compiled_std_fallback_reason: Option<String>,
    pub vm_eval_expr_calls: usize,
    pub vm_max_eval_depth: usize,
    pub vm_continuation_steps: usize,
    pub vm_max_continuation_frames: usize,
    pub used_embedded_std: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CheckOutput {
    pub ok: bool,
    pub file_count: usize,
    pub text: String,
    pub diagnostics: Vec<Diagnostic>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DumpOutput {
    pub ok: bool,
    pub file_count: usize,
    pub text: String,
    pub diagnostics: Vec<Diagnostic>,
    pub errors: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Diagnostic {
    pub severity: DiagnosticSeverity,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub code: Option<String>,
    pub message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub hint: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub start: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub end: Option<usize>,
    pub related: Vec<DiagnosticRelated>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub label: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DiagnosticRelated {
    pub message: String,
    pub start: usize,
    pub end: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub origin: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum DiagnosticSeverity {
    Error,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ColorizeOutput {
    pub ok: bool,
    pub spans: Vec<HighlightSpan>,
    pub diagnostics: Vec<Diagnostic>,
    pub source_len: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct HighlightSpan {
    pub start: usize,
    pub end: usize,
    pub kind: HighlightKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum HighlightKind {
    Comment,
    Colon,
    Delimiter,
    Function,
    Keyword,
    Namespace,
    Number,
    Operator,
    Parameter,
    Pattern,
    Property,
    String,
    Type,
    TypeParameter,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct WarmupOutput {
    pub source_cache_hits: usize,
    pub source_cache_misses: usize,
    pub source_cache_clone_ms: f64,
    pub source_cache_build_ms: f64,
    pub embedded_std_artifacts: usize,
    pub embedded_std_runtime_bindings: usize,
    pub embedded_std_artifacts_bytes: usize,
    pub embedded_std_artifacts_valid: bool,
    pub embedded_std_artifacts_fallback_reason: Option<String>,
    pub artifact_decode_ms: f64,
    pub prefix_import_ms: f64,
    pub total_ms: f64,
    pub worker_wall_ms: f64,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct EmbeddedStdArtifactsOutput {
    pub artifacts: usize,
    pub runtime_bindings: usize,
    pub bytes: usize,
    pub valid: bool,
    pub fallback_reason: Option<String>,
    pub cache_hits: usize,
    pub cache_misses: usize,
    pub decode_ms: f64,
    pub clone_ms: f64,
}

impl RunOutput {
    fn from_check_output(output: yulang::CheckPolyOutput, source: &str) -> Self {
        let diagnostics_started = ClockInstant::now();
        let diagnostics = diagnostics_from_source_diagnostics(&output.diagnostics, source.len());
        let errors = diagnostics
            .iter()
            .map(|diagnostic| diagnostic.message.clone())
            .collect();
        Self {
            ok: diagnostics.is_empty(),
            file_count: output.file_count,
            text: output.text,
            results: Vec::new(),
            stdout: String::new(),
            types: Vec::new(),
            timings: Some(RunTimings::diagnostic_only(
                output.file_count,
                diagnostics_started.elapsed_ms(),
                true,
            )),
            diagnostics,
            errors,
            cache_safe: true,
        }
    }

    fn from_runtime_output(
        output: WasmRuntimeOutput,
        source: &str,
        used_embedded_std: bool,
    ) -> Self {
        let diagnostics_started = ClockInstant::now();
        let diagnostics = diagnostics_from_messages(&output.errors, source.len());
        let results = output
            .results
            .into_iter()
            .enumerate()
            .map(|(index, value)| RunResult { index, value })
            .collect::<Vec<_>>();
        let vm_continuation_steps = evidence_vm_continuation_steps(&output.stats);
        let cache_safe = output.stats.is_cache_safe();
        let timings = RunTimings::from_runtime(
            output.file_count,
            output.timing,
            &output.stats,
            vm_continuation_steps,
            diagnostics_started.elapsed_ms(),
            used_embedded_std,
        );
        Self {
            ok: diagnostics.is_empty(),
            file_count: output.file_count,
            text: output.text,
            results,
            stdout: output.stdout,
            types: output.types,
            timings: Some(timings),
            diagnostics,
            errors: output.errors,
            cache_safe,
        }
    }

    fn from_runtime_error(error: WasmRuntimeError, source_len: usize) -> Self {
        let RuntimeSourceDiagnostic {
            diagnostic,
            range_offset,
        } = error.into_source_diagnostic();
        let diagnostic = diagnostic_from_source_diagnostic(&diagnostic, source_len, range_offset);
        let message = diagnostic.message.clone();
        Self {
            ok: false,
            file_count: 0,
            text: String::new(),
            results: Vec::new(),
            stdout: String::new(),
            types: Vec::new(),
            timings: Some(RunTimings::diagnostic_only(0, 0.0, false)),
            diagnostics: vec![diagnostic],
            errors: vec![message],
            cache_safe: false,
        }
    }

    fn cache_safe(&self) -> bool {
        self.cache_safe
    }
}

impl RunTimings {
    fn from_runtime(
        files: usize,
        phase: RunPhaseTimings,
        stats: &evidence_vm::RuntimeEvidenceRunStats,
        vm_continuation_steps: usize,
        diagnostics_ms: f64,
        used_embedded_std: bool,
    ) -> Self {
        Self {
            source_set_ms: phase.source_set_ms,
            infer_lower_ms: phase.infer_lower_ms,
            type_render_ms: phase.type_render_ms,
            diagnostics_ms,
            // The evidence-runtime path has no separate export-core or mono-VM phase.
            export_core_ms: 0.0,
            runtime_lower_ms: phase.runtime_lower_ms,
            monomorphize_ms: 0.0,
            vm_compile_ms: phase.evidence_plan_ms,
            evidence_plan_ms: phase.evidence_plan_ms,
            vm_eval_ms: phase.vm_eval_ms,
            artifact_decode_ms: phase.artifact_decode_ms,
            artifact_decode_cache_hit: phase.artifact_decode_cache_hit,
            total_ms: 0.0,
            worker_wall_ms: 0.0,
            files,
            entry_files: usize::from(files != 0),
            std_files: if used_embedded_std {
                files.saturating_sub(1)
            } else {
                0
            },
            user_files: usize::from(files != 0),
            source_cache_hits: 0,
            source_cache_misses: 0,
            source_cache_clone_ms: 0.0,
            source_cache_build_ms: 0.0,
            compiled_std_artifacts: phase.compiled_std_artifacts,
            compiled_std_runtime_bindings: 0,
            compiled_std_cache_hit: phase.compiled_std_cache_hit,
            compiled_std_fallback_reason: (used_embedded_std && phase.compiled_std_artifacts == 0)
                .then(|| "embedded compiled std artifact unavailable".to_string()),
            vm_eval_expr_calls: stats.expr_evals,
            vm_max_eval_depth: stats.max_env_depth,
            vm_continuation_steps,
            vm_max_continuation_frames: stats.max_continuation_frames,
            used_embedded_std,
        }
    }

    fn diagnostic_only(files: usize, diagnostics_ms: f64, used_embedded_std: bool) -> Self {
        Self {
            source_set_ms: 0.0,
            infer_lower_ms: 0.0,
            type_render_ms: 0.0,
            diagnostics_ms,
            export_core_ms: 0.0,
            runtime_lower_ms: 0.0,
            monomorphize_ms: 0.0,
            vm_compile_ms: 0.0,
            evidence_plan_ms: 0.0,
            vm_eval_ms: 0.0,
            artifact_decode_ms: 0.0,
            artifact_decode_cache_hit: false,
            total_ms: 0.0,
            worker_wall_ms: 0.0,
            files,
            entry_files: usize::from(files != 0),
            std_files: if used_embedded_std {
                files.saturating_sub(1)
            } else {
                0
            },
            user_files: usize::from(files != 0),
            source_cache_hits: 0,
            source_cache_misses: 0,
            source_cache_clone_ms: 0.0,
            source_cache_build_ms: 0.0,
            compiled_std_artifacts: 0,
            compiled_std_runtime_bindings: 0,
            compiled_std_cache_hit: false,
            compiled_std_fallback_reason: None,
            vm_eval_expr_calls: 0,
            vm_max_eval_depth: 0,
            vm_continuation_steps: 0,
            vm_max_continuation_frames: 0,
            used_embedded_std,
        }
    }

    fn mark_source_cache_miss(&mut self, elapsed_ms: f64) {
        self.source_cache_hits = 0;
        self.source_cache_misses = 1;
        self.source_cache_clone_ms = 0.0;
        self.source_cache_build_ms = elapsed_ms;
        self.total_ms = elapsed_ms;
    }

    fn mark_source_cache_hit(&mut self, elapsed_ms: f64) {
        self.source_set_ms = 0.0;
        self.infer_lower_ms = 0.0;
        self.type_render_ms = 0.0;
        self.diagnostics_ms = 0.0;
        self.runtime_lower_ms = 0.0;
        self.vm_compile_ms = 0.0;
        self.evidence_plan_ms = 0.0;
        self.vm_eval_ms = 0.0;
        self.artifact_decode_ms = 0.0;
        self.artifact_decode_cache_hit = false;
        self.source_cache_hits = 1;
        self.source_cache_misses = 0;
        self.source_cache_clone_ms = elapsed_ms;
        self.source_cache_build_ms = 0.0;
        self.vm_eval_expr_calls = 0;
        self.vm_max_eval_depth = 0;
        self.vm_continuation_steps = 0;
        self.vm_max_continuation_frames = 0;
        self.total_ms = elapsed_ms;
    }
}

fn evidence_vm_continuation_steps(stats: &evidence_vm::RuntimeEvidenceRunStats) -> usize {
    stats.continuation_append_steps
        + stats.continuation_resume_steps
        + stats.request_continuation_steps
}

impl CheckOutput {
    fn from_error(message: String, source_len: usize) -> Self {
        Self {
            ok: false,
            file_count: 0,
            text: String::new(),
            diagnostics: vec![Diagnostic::error(message, source_len)],
        }
    }
}

impl DumpOutput {
    fn from_dump(file_count: usize, text: String, errors: Vec<String>, source: &str) -> Self {
        let diagnostics = diagnostics_from_messages(&errors, source.len());
        Self {
            ok: diagnostics.is_empty(),
            file_count,
            text,
            diagnostics,
            errors,
        }
    }

    fn from_error(message: String, source_len: usize) -> Self {
        Self {
            ok: false,
            file_count: 0,
            text: String::new(),
            diagnostics: vec![Diagnostic::error(message.clone(), source_len)],
            errors: vec![message],
        }
    }
}

fn diagnostics_from_source_diagnostics(
    diagnostics: &[yulang::SourceDiagnostic],
    source_len: usize,
) -> Vec<Diagnostic> {
    diagnostics
        .iter()
        .map(|diagnostic| {
            diagnostic_from_source_diagnostic(
                diagnostic,
                source_len,
                yulang::IMPLICIT_STD_SOURCE_PREFIX_LEN,
            )
        })
        .collect()
}

fn diagnostic_from_source_diagnostic(
    diagnostic: &yulang::SourceDiagnostic,
    source_len: usize,
    range_offset: usize,
) -> Diagnostic {
    let diagnostic = editor_diagnostic_for_source_diagnostic(diagnostic);
    Diagnostic::from_editor_diagnostic(&diagnostic, source_len, range_offset)
}

impl Diagnostic {
    fn error(message: String, source_len: usize) -> Self {
        Self {
            severity: DiagnosticSeverity::Error,
            code: None,
            message,
            hint: None,
            start: Some(0),
            end: Some(source_len),
            related: Vec::new(),
            label: None,
        }
    }

    fn from_editor_diagnostic(
        diagnostic: &editor_diagnostics::Diagnostic,
        source_len: usize,
        range_offset: usize,
    ) -> Self {
        let range = diagnostic
            .range
            .map(|range| playground_diagnostic_range(range, source_len, range_offset));
        Self {
            severity: DiagnosticSeverity::from_editor(diagnostic.severity),
            code: diagnostic.code.clone(),
            message: diagnostic.message.clone(),
            hint: diagnostic.hint.clone(),
            start: range.map(|(start, _)| start),
            end: range.map(|(_, end)| end),
            related: diagnostic
                .related
                .iter()
                .map(|related| {
                    let (start, end) =
                        playground_diagnostic_range(related.range, source_len, range_offset);
                    DiagnosticRelated {
                        message: related.message.clone(),
                        start,
                        end,
                        origin: related.origin.map(diagnostic_origin_code),
                    }
                })
                .collect(),
            label: diagnostic.label.clone(),
        }
    }
}

fn editor_diagnostic_for_source_diagnostic(
    diagnostic: &yulang::SourceDiagnostic,
) -> editor_diagnostics::Diagnostic {
    editor_diagnostics::Diagnostic {
        severity: editor_diagnostic_severity(diagnostic.severity),
        code: diagnostic.code.clone(),
        label: diagnostic.label.clone(),
        range: diagnostic.range.map(byte_range_for_source_range),
        message: diagnostic.message.clone(),
        hint: diagnostic.hint.clone(),
        related: diagnostic
            .related
            .iter()
            .map(editor_related_diagnostic_for_source_related)
            .collect(),
    }
}

fn editor_related_diagnostic_for_source_related(
    related: &yulang::source::SourceDiagnosticRelated,
) -> editor_diagnostics::RelatedDiagnostic {
    editor_diagnostics::RelatedDiagnostic {
        message: related.message.clone(),
        range: byte_range_for_source_range(related.range),
        origin: related
            .origin
            .as_ref()
            .map(editor_related_origin_for_source_origin),
    }
}

fn editor_diagnostic_severity(
    severity: yulang::SourceDiagnosticSeverity,
) -> editor_diagnostics::DiagnosticSeverity {
    match severity {
        yulang::SourceDiagnosticSeverity::Error => editor_diagnostics::DiagnosticSeverity::Error,
    }
}

fn editor_related_origin_for_source_origin(
    origin: &yulang::SourceDiagnosticRelatedOrigin,
) -> editor_diagnostics::RelatedOrigin {
    match origin {
        yulang::SourceDiagnosticRelatedOrigin::TypeAnnotation => {
            editor_diagnostics::RelatedOrigin::TypeAnnotation
        }
        yulang::SourceDiagnosticRelatedOrigin::Expression => {
            editor_diagnostics::RelatedOrigin::Expression
        }
        yulang::SourceDiagnosticRelatedOrigin::ImplCandidate => {
            editor_diagnostics::RelatedOrigin::ImplCandidate
        }
    }
}

impl DiagnosticSeverity {
    fn from_editor(severity: editor_diagnostics::DiagnosticSeverity) -> Self {
        match severity {
            editor_diagnostics::DiagnosticSeverity::Error => DiagnosticSeverity::Error,
        }
    }
}

fn diagnostic_origin_code(origin: editor_diagnostics::RelatedOrigin) -> String {
    origin.playground_code().to_string()
}

fn playground_diagnostic_range(
    range: editor_text::ByteRange,
    source_len: usize,
    range_offset: usize,
) -> (usize, usize) {
    let range = editor_text::subtract_prefix_saturating(range, range_offset);
    let range = editor_text::clamp_byte_range_to_len(range, source_len);
    (range.start, range.end)
}

fn byte_range_for_source_range(range: yulang::SourceRange) -> editor_text::ByteRange {
    editor_text::ByteRange {
        start: range.start,
        end: range.end,
    }
}

fn diagnostics_from_messages(messages: &[String], source_len: usize) -> Vec<Diagnostic> {
    messages
        .iter()
        .cloned()
        .map(|message| Diagnostic::error(message, source_len))
        .collect()
}

fn source_likely_needs_embedded_std(source: &str) -> bool {
    source.contains("std::")
        || source.contains("use std")
        || source.contains('$')
        || source.contains(".list")
        || source.contains(".show")
        || source.contains(".map")
        || source.contains(".filter")
        || source.contains(".rev")
        || source.contains("for ")
        || source.contains("..")
        || source_has_identifier(source, "all")
        || source_has_identifier(source, "any")
}

fn should_retry_with_embedded_std(source: &str, errors: &[String]) -> bool {
    errors.iter().any(|error| {
        error.contains("unresolved value name")
            || error.contains("unresolved type name")
            || error.contains("UnresolvedName")
            || error.contains("UnresolvedTypeName")
            || error.contains("unsupported VM boundary") && source_likely_needs_embedded_std(source)
    })
}

fn source_has_identifier(source: &str, name: &str) -> bool {
    source
        .split(|ch: char| ch != '_' && !ch.is_ascii_alphanumeric())
        .any(|token| token == name)
}

fn highlight_kind_from_token_type(token_type: u32) -> Option<HighlightKind> {
    match token_type {
        0 => Some(HighlightKind::Function),
        1 => Some(HighlightKind::Type),
        2 => Some(HighlightKind::TypeParameter),
        3 => Some(HighlightKind::Namespace),
        4 => Some(HighlightKind::Parameter),
        5 => Some(HighlightKind::Keyword),
        6 => Some(HighlightKind::String),
        7 => Some(HighlightKind::Number),
        8 => Some(HighlightKind::Comment),
        9 => Some(HighlightKind::Operator),
        10 => Some(HighlightKind::Delimiter),
        11 => Some(HighlightKind::Colon),
        12 => Some(HighlightKind::Property),
        13 => Some(HighlightKind::Pattern),
        _ => None,
    }
}

fn line_utf16_starts(source: &str) -> Vec<usize> {
    let mut starts = vec![0];
    let mut offset = 0;
    for ch in source.chars() {
        offset += ch.len_utf16();
        if ch == '\n' {
            starts.push(offset);
        }
    }
    starts
}

fn to_js_value<T: Serialize>(value: &T) -> JsValue {
    serde_wasm_bindgen::to_value(value).unwrap_or_else(|error| {
        JsValue::from_str(&format!(
            "{{\"ok\":false,\"diagnostics\":[{{\"severity\":\"error\",\"message\":\"serialize wasm output: {error}\",\"start\":0,\"end\":0}}]}}"
        ))
    })
}

fn set_panic_hook() {
    #[cfg(target_arch = "wasm32")]
    console_error_panic_hook::set_once();
}

#[cfg(test)]
mod run_cache_tests {
    use super::*;

    fn on_test_stack<T>(work: impl FnOnce() -> T + Send + 'static) -> T
    where
        T: Send + 'static,
    {
        std::thread::Builder::new()
            .name("wasm-run-cache-test-stack".to_string())
            .stack_size(16 * 1024 * 1024)
            .spawn(work)
            .unwrap()
            .join()
            .unwrap()
    }

    #[test]
    fn run_inner_caches_console_only_repeated_source() {
        clear_std_cache();
        let first = run_inner("println \"hello\"\n");
        let second = run_inner("println \"hello\"\n");

        assert!(first.ok, "{first:?}");
        assert!(second.ok, "{second:?}");
        assert_eq!(first.stdout, "Out 1: hello\n");
        assert_eq!(second.stdout, "Out 1: hello\n");
        assert_eq!(
            second
                .timings
                .as_ref()
                .map(|timing| timing.source_cache_hits),
            Some(1)
        );
    }

    #[test]
    fn run_inner_reports_real_phase_and_cache_timings() {
        clear_std_cache();
        let first = run_inner("1 + 2\n");
        let first_timing = first.timings.as_ref().expect("run timings");

        assert!(first.ok, "{first:?}");
        assert!(first_timing.infer_lower_ms > 0.0, "{first_timing:?}");
        assert!(first_timing.runtime_lower_ms > 0.0, "{first_timing:?}");
        assert!(first_timing.evidence_plan_ms > 0.0, "{first_timing:?}");
        assert!(first_timing.vm_eval_ms > 0.0, "{first_timing:?}");
        assert!(first_timing.total_ms > 0.0, "{first_timing:?}");
        assert_eq!(first_timing.source_cache_hits, 0);
        assert_eq!(first_timing.source_cache_misses, 1);
        assert_eq!(first_timing.source_cache_build_ms, first_timing.total_ms);

        let second = run_inner("1 + 2\n");
        let second_timing = second.timings.as_ref().expect("cached run timings");
        assert!(second.ok, "{second:?}");
        assert_eq!(second_timing.source_cache_hits, 1);
        assert_eq!(second_timing.source_cache_misses, 0);
        assert_eq!(second_timing.infer_lower_ms, 0.0);
        assert_eq!(second_timing.runtime_lower_ms, 0.0);
        assert_eq!(second_timing.vm_eval_ms, 0.0);
        assert!(second_timing.source_cache_clone_ms > 0.0);
        assert_eq!(second_timing.source_cache_clone_ms, second_timing.total_ms);
    }

    #[test]
    fn run_inner_skips_cache_for_clock_now_runs() {
        let source = "std::time::clock::now()\n".to_string();
        let (first, second) = on_test_stack(move || {
            clear_std_cache();
            let first = run_inner(&source);
            std::thread::sleep(std::time::Duration::from_millis(2));
            let second = run_inner(&source);
            (first, second)
        });

        assert!(first.ok, "{first:?}");
        assert!(second.ok, "{second:?}");
        assert_eq!(
            first
                .timings
                .as_ref()
                .map(|timing| (timing.source_cache_hits, timing.source_cache_misses)),
            Some((0, 1))
        );
        assert_eq!(
            second
                .timings
                .as_ref()
                .map(|timing| (timing.source_cache_hits, timing.source_cache_misses)),
            Some((0, 1))
        );
        assert_ne!(
            first.results.first().map(|result| result.value.as_str()),
            second.results.first().map(|result| result.value.as_str())
        );
        assert!(!first.cache_safe, "{first:?}");
        assert!(!second.cache_safe, "{second:?}");
    }
}

#[cfg(test)]
mod playground_tests;
