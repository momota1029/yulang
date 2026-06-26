use std::cell::RefCell;
use std::collections::HashMap;

use parser::sink::YulangLanguage;
use poly::expr::{Def, Vis};
use rowan::SyntaxNode;
use serde::Serialize;
use wasm_bindgen::prelude::*;
use yulang_editor::semantic_tokens;

const PLAYGROUND_ENTRY: &str = "playground.yu";
const PLAYGROUND_STD_ARTIFACT_ENTRY: &str = "<embedded-playground-std-root>";
const FULL_STD_ARTIFACT_ENTRY: &str = "<embedded-std-root>";
const EMBEDDED_PLAYGROUND_STD_ARTIFACT: &[u8] =
    include_bytes!(concat!(env!("OUT_DIR"), "/embedded_playground_std.yucu"));
const EMBEDDED_FULL_STD_ARTIFACT: &[u8] =
    include_bytes!(concat!(env!("OUT_DIR"), "/embedded_full_std.yucu"));

thread_local! {
    static RUN_CACHE: RefCell<HashMap<String, RunOutput>> = RefCell::new(HashMap::new());
    static PLAYGROUND_STD_ARTIFACT: RefCell<Option<Option<yulang::cache::CachedCompiledUnitArtifact>>> =
        const { RefCell::new(None) };
    static FULL_STD_ARTIFACT: RefCell<Option<Option<yulang::cache::CachedCompiledUnitArtifact>>> =
        const { RefCell::new(None) };
}

#[wasm_bindgen]
pub fn run(source: &str) -> JsValue {
    set_panic_hook();
    to_js_value(&run_inner(source))
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
    let status = embedded_std_status_inner();
    WarmupOutput {
        source_cache_hits: 0,
        source_cache_misses: 0,
        source_cache_clone_ms: 0.0,
        source_cache_build_ms: 0.0,
        embedded_std_artifacts: status.artifacts,
        embedded_std_runtime_bindings: status.runtime_bindings,
        embedded_std_artifacts_bytes: status.bytes,
        embedded_std_artifacts_valid: status.valid,
        embedded_std_artifacts_fallback_reason: status.fallback_reason,
        total_ms: 0.0,
    }
}

pub fn embedded_std_status_inner() -> EmbeddedStdArtifactsOutput {
    let playground = embedded_playground_std_artifact();
    let full = embedded_full_std_artifact();
    let valid = playground.is_some() && full.is_some();
    EmbeddedStdArtifactsOutput {
        artifacts: usize::from(playground.is_some()) + usize::from(full.is_some()),
        runtime_bindings: 0,
        bytes: EMBEDDED_PLAYGROUND_STD_ARTIFACT.len() + EMBEDDED_FULL_STD_ARTIFACT.len(),
        valid,
        fallback_reason: (!valid).then(|| "embedded std artifact failed validation".to_string()),
    }
}

pub fn run_inner(source: &str) -> RunOutput {
    let cached = RUN_CACHE.with(|cache| cache.borrow().get(source).cloned());
    if let Some(mut output) = cached {
        if let Some(timings) = output.timings.as_mut() {
            timings.source_cache_hits += 1;
        }
        return output;
    }

    let output = run_inner_uncached(source);
    RUN_CACHE.with(|cache| {
        cache
            .borrow_mut()
            .insert(source.to_string(), output.clone());
    });
    output
}

pub fn check_inner(source: &str) -> CheckOutput {
    match yulang::check_poly_from_source_text_with_embedded_std(PLAYGROUND_ENTRY, source) {
        Ok(output) => {
            let diagnostics = output
                .diagnostics
                .iter()
                .map(|diagnostic| Diagnostic::from_source_diagnostic(diagnostic, source.len()))
                .collect::<Vec<_>>();
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

fn run_inner_uncached(source: &str) -> RunOutput {
    match run_control_from_source_text_without_std(source) {
        Ok(output) if output.errors.is_empty() => {
            return RunOutput::from_control_output(output, source, false);
        }
        Ok(output) if should_retry_with_embedded_std(source, &output.errors) => {
            return run_with_embedded_std_fallback(source, None);
        }
        Ok(output) => return RunOutput::from_control_output(output, source, false),
        Err(_) if source_likely_needs_embedded_std(source) => {
            return run_with_embedded_std_fallback(source, None);
        }
        Err(no_std_error) => {
            return run_with_embedded_std_fallback(source, Some(no_std_error));
        }
    }
}

fn run_with_embedded_std_fallback(
    source: &str,
    no_std_error: Option<yulang::RouteError>,
) -> RunOutput {
    match run_control_from_source_text_with_playground_std(source) {
        Ok(output) if output.errors.is_empty() => {
            return RunOutput::from_control_output(output, source, true);
        }
        Ok(_) | Err(_) => {}
    }

    match run_control_from_source_text_with_embedded_std(source) {
        Ok(output) => RunOutput::from_control_output(output, source, true),
        Err(std_error) => {
            let message = match no_std_error {
                Some(no_std_error) => format!(
                    "{std_error}\n\nwithout embedded std, the earlier error was: {no_std_error}"
                ),
                None => std_error.to_string(),
            };
            RunOutput::from_error(message, source.len())
        }
    }
}

fn run_control_from_source_text_without_std(
    source: &str,
) -> Result<WasmControlOutput, yulang::RouteError> {
    let files = yulang::collect_local_source_text(PLAYGROUND_ENTRY, source.to_string())?;
    let output = build_named_control_from_collected_sources(files)?;
    run_built_control_program_with_host(output)
}

fn run_control_from_source_text_with_embedded_std(
    source: &str,
) -> Result<WasmControlOutput, yulang::RouteError> {
    let output = match embedded_full_std_artifact() {
        Some(artifact) => {
            let poly = yulang::build_poly_from_embedded_std_compiled_unit_artifact(
                artifact,
                source.to_string(),
            )?;
            build_named_control_from_poly(poly)?
        }
        None => {
            let files = yulang::collect_source_text_with_embedded_std(
                PLAYGROUND_ENTRY,
                source.to_string(),
            )?;
            build_named_control_from_collected_sources(files)?
        }
    };
    run_built_control_program_with_host(output)
}

fn run_control_from_source_text_with_playground_std(
    source: &str,
) -> Result<WasmControlOutput, yulang::RouteError> {
    let poly = match embedded_playground_std_artifact() {
        Some(artifact) => yulang::build_poly_from_embedded_playground_std_compiled_unit_artifact(
            artifact,
            source.to_string(),
        )?,
        None => yulang::build_poly_from_source_text_with_embedded_playground_std(
            PLAYGROUND_ENTRY,
            source.to_string(),
        )?,
    };
    let output = build_named_control_from_poly(poly)?;
    run_built_control_program_with_host(output)
}

fn embedded_playground_std_artifact() -> Option<yulang::cache::CachedCompiledUnitArtifact> {
    PLAYGROUND_STD_ARTIFACT.with(|cache| {
        if let Some(cached) = cache.borrow().as_ref() {
            return cached.clone();
        }

        let decoded = decode_embedded_playground_std_artifact();
        *cache.borrow_mut() = Some(decoded.clone());
        decoded
    })
}

fn embedded_full_std_artifact() -> Option<yulang::cache::CachedCompiledUnitArtifact> {
    FULL_STD_ARTIFACT.with(|cache| {
        if let Some(cached) = cache.borrow().as_ref() {
            return cached.clone();
        }

        let decoded = decode_embedded_full_std_artifact();
        *cache.borrow_mut() = Some(decoded.clone());
        decoded
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
struct NamedControlBuild {
    output: yulang::BuildControlOutput,
    constructor_names: ConstructorNames,
    types: Vec<TypeResult>,
}

type ConstructorNames = HashMap<control_vm::DefId, String>;

fn build_named_control_from_collected_sources(
    files: Vec<yulang::CollectedSource>,
) -> Result<NamedControlBuild, yulang::RouteError> {
    let poly = yulang::build_poly_from_collected_sources(files)?;
    build_named_control_from_poly(poly)
}

fn build_named_control_from_poly(
    poly: yulang::BuildPolyOutput,
) -> Result<NamedControlBuild, yulang::RouteError> {
    let constructor_names = constructor_display_names(&poly);
    let types = exported_type_results(&poly);
    let output = yulang::build_control_from_poly_output(&poly)?;
    Ok(NamedControlBuild {
        output,
        constructor_names,
        types,
    })
}

fn constructor_display_names(poly: &yulang::BuildPolyOutput) -> ConstructorNames {
    poly.arena
        .constructors
        .iter()
        .map(|(def, constructor)| (control_vm::DefId(def.0), constructor.name.clone()))
        .collect()
}

fn exported_type_results(poly: &yulang::BuildPolyOutput) -> Vec<TypeResult> {
    poly.arena
        .roots
        .iter()
        .filter_map(|def| exported_type_result(poly, *def))
        .collect()
}

fn exported_type_result(
    poly: &yulang::BuildPolyOutput,
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
    let ty = poly::dump::format_scheme(&poly.arena.typ, scheme);
    Some(TypeResult { name, ty })
}

fn run_built_control_program_with_host(
    build: NamedControlBuild,
) -> Result<WasmControlOutput, yulang::RouteError> {
    let mut stdout = String::new();
    let values = control_vm::run_program_with_host(&build.output.program, |path, payload| {
        handle_host_effect(path, payload, &mut stdout)
    })
    .map_err(yulang::RouteError::Control)?;
    let text = format_control_values(&values, &build.constructor_names);
    Ok(WasmControlOutput {
        file_count: build.output.file_count,
        errors: build.output.errors,
        text: format!("run roots {text}\n"),
        values,
        constructor_names: build.constructor_names,
        types: build.types,
        stdout,
    })
}

fn handle_host_effect(
    path: &[String],
    payload: &control_vm::Value,
    stdout: &mut String,
) -> Option<control_vm::Value> {
    if path == ["std", "io", "console", "out", "write"] {
        push_host_string_payload(payload, stdout)?;
        return Some(control_vm::Value::Unit);
    }
    None
}

fn push_host_string_payload(value: &control_vm::Value, out: &mut String) -> Option<()> {
    match value {
        control_vm::Value::Str(value) => {
            value.push_to_string(out);
            Some(())
        }
        control_vm::Value::Marked { value, .. } => push_host_string_payload(value, out),
        _ => None,
    }
}

#[derive(Debug, Clone, PartialEq)]
struct WasmControlOutput {
    file_count: usize,
    errors: Vec<String>,
    text: String,
    values: Vec<control_vm::Value>,
    constructor_names: ConstructorNames,
    types: Vec<TypeResult>,
    stdout: String,
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

#[derive(Debug, Clone, Copy, PartialEq, Serialize)]
pub struct RunTimings {
    pub vm_continuation_steps: usize,
    pub source_cache_hits: usize,
    pub source_cache_misses: usize,
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
    pub start: usize,
    pub end: usize,
    pub related: Vec<DiagnosticRelated>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub label: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DiagnosticRelated {
    pub message: String,
    pub start: usize,
    pub end: usize,
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
    pub total_ms: f64,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct EmbeddedStdArtifactsOutput {
    pub artifacts: usize,
    pub runtime_bindings: usize,
    pub bytes: usize,
    pub valid: bool,
    pub fallback_reason: Option<String>,
}

impl RunOutput {
    fn from_control_output(
        output: WasmControlOutput,
        source: &str,
        used_embedded_std: bool,
    ) -> Self {
        let diagnostics = diagnostics_from_messages(&output.errors, source.len());
        let results = output
            .values
            .iter()
            .enumerate()
            .map(|(index, value)| RunResult {
                index,
                value: format_single_control_value(value, &output.constructor_names),
            })
            .collect::<Vec<_>>();
        Self {
            ok: diagnostics.is_empty(),
            file_count: output.file_count,
            text: output.text,
            results,
            stdout: output.stdout,
            types: output.types,
            timings: Some(RunTimings {
                vm_continuation_steps: 0,
                source_cache_hits: 0,
                source_cache_misses: 1,
                used_embedded_std,
            }),
            diagnostics,
            errors: output.errors,
        }
    }

    fn from_error(message: String, source_len: usize) -> Self {
        Self {
            ok: false,
            file_count: 0,
            text: String::new(),
            results: Vec::new(),
            stdout: String::new(),
            types: Vec::new(),
            timings: Some(RunTimings {
                vm_continuation_steps: 0,
                source_cache_hits: 0,
                source_cache_misses: 1,
                used_embedded_std: false,
            }),
            diagnostics: vec![Diagnostic::error(message.clone(), source_len)],
            errors: vec![message],
        }
    }
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

impl Diagnostic {
    fn error(message: String, source_len: usize) -> Self {
        Self {
            severity: DiagnosticSeverity::Error,
            code: None,
            message,
            start: 0,
            end: source_len,
            related: Vec::new(),
            label: None,
        }
    }

    fn from_source_diagnostic(diagnostic: &yulang::SourceDiagnostic, source_len: usize) -> Self {
        Self {
            severity: DiagnosticSeverity::Error,
            code: None,
            message: diagnostic.message.clone(),
            start: 0,
            end: source_len,
            related: Vec::new(),
            label: diagnostic.label.clone(),
        }
    }
}

fn diagnostics_from_messages(messages: &[String], source_len: usize) -> Vec<Diagnostic> {
    messages
        .iter()
        .cloned()
        .map(|message| Diagnostic::error(message, source_len))
        .collect()
}

fn format_control_values(
    values: &[control_vm::Value],
    constructor_names: &ConstructorNames,
) -> String {
    let mut out = String::new();
    out.push('[');
    for (index, value) in values.iter().enumerate() {
        if index > 0 {
            out.push_str(", ");
        }
        out.push_str(&format_single_control_value(value, constructor_names));
    }
    out.push(']');
    out
}

fn format_single_control_value(
    value: &control_vm::Value,
    constructor_names: &ConstructorNames,
) -> String {
    match value {
        control_vm::Value::Int(value) => value.to_string(),
        control_vm::Value::BigInt(value) => value.to_string(),
        control_vm::Value::Float(value) => value.to_string(),
        control_vm::Value::Str(value) => format!("{:?}", value.to_flat_string()),
        control_vm::Value::Bytes(value) => format!("<bytes len={}>", value.len()),
        control_vm::Value::Bool(value) => value.to_string(),
        control_vm::Value::Unit => "()".to_string(),
        control_vm::Value::Tuple(values) => {
            format_control_delimited_values("(", ")", values, constructor_names, true)
        }
        control_vm::Value::List(values) => {
            let values = values
                .to_vec()
                .into_iter()
                .map(|value| (*value).clone())
                .collect::<Vec<_>>();
            format_control_delimited_values("[", "]", &values, constructor_names, false)
        }
        control_vm::Value::Record(fields) => {
            let mut out = String::new();
            out.push('{');
            for (index, field) in fields.iter().enumerate() {
                if index > 0 {
                    out.push_str(", ");
                }
                out.push_str(&field.name);
                out.push_str(": ");
                out.push_str(&format_single_control_value(
                    &field.value,
                    constructor_names,
                ));
            }
            out.push('}');
            out
        }
        control_vm::Value::PolyVariant { tag, payloads } => {
            if payloads.is_empty() {
                return tag.clone();
            }
            format!(
                "{tag}{}",
                format_control_delimited_values("(", ")", payloads, constructor_names, true)
            )
        }
        control_vm::Value::DataConstructor { def, payloads } => {
            if let Some(name) = constructor_names.get(def) {
                return format_named_constructor(name, payloads, constructor_names);
            }
            if payloads.is_empty() {
                return format!("<ctor d{}>", def.0);
            }
            format!(
                "<ctor d{}>{}",
                def.0,
                format_control_delimited_values("(", ")", payloads, constructor_names, true)
            )
        }
        control_vm::Value::ConstructorFunction(constructor) => {
            let name = constructor_names
                .get(&constructor.def)
                .map(String::as_str)
                .unwrap_or("<ctor>");
            format!(
                "<ctor-fn {name} d{} {}/{}>",
                constructor.def.0,
                constructor.args.len(),
                constructor.arity
            )
        }
        control_vm::Value::PrimitiveOp(primitive) => {
            format!(
                "<prim {:?} {}/{}>",
                primitive.op,
                primitive.args.len(),
                primitive.op.arity()
            )
        }
        control_vm::Value::Closure(_) | control_vm::Value::RecursiveClosure { .. } => {
            "<closure>".to_string()
        }
        control_vm::Value::Thunk(_) => "<thunk>".to_string(),
        control_vm::Value::FunctionAdapter(_) => "<function-adapter>".to_string(),
        control_vm::Value::EffectOp { path, .. } => format!("<effect-op {}>", path.join("::")),
        control_vm::Value::Continuation(id) => format!("<continuation {}>", id.0),
        control_vm::Value::Marked { value, .. } => {
            format_single_control_value(value, constructor_names)
        }
    }
}

fn format_named_constructor(
    name: &str,
    payloads: &[control_vm::Value],
    constructor_names: &ConstructorNames,
) -> String {
    match payloads {
        [] => name.to_string(),
        [payload] => format!(
            "{name} {}",
            format_single_control_value(payload, constructor_names)
        ),
        payloads => format!(
            "{name}{}",
            format_control_delimited_values("(", ")", payloads, constructor_names, false)
        ),
    }
}

fn format_control_delimited_values(
    open: &str,
    close: &str,
    values: &[control_vm::Value],
    constructor_names: &ConstructorNames,
    tuple_singleton: bool,
) -> String {
    let mut out = String::new();
    out.push_str(open);
    for (index, value) in values.iter().enumerate() {
        if index > 0 {
            out.push_str(", ");
        }
        out.push_str(&format_single_control_value(value, constructor_names));
    }
    if tuple_singleton && values.len() == 1 && open == "(" {
        out.push(',');
    }
    out.push_str(close);
    out
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
mod playground_tests;
