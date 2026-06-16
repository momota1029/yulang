use std::cell::RefCell;
use std::collections::HashMap;

use parser::sink::YulangLanguage;
use rowan::SyntaxNode;
use serde::Serialize;
use sources::SourceFile;
use wasm_bindgen::prelude::*;
use yulang_editor::semantic_tokens;

const PLAYGROUND_ENTRY: &str = "playground.yu";

thread_local! {
    static RUN_CACHE: RefCell<HashMap<String, RunOutput>> = RefCell::new(HashMap::new());
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
    let files = yulang::collect_source_text_with_embedded_playground_std(
        PLAYGROUND_ENTRY,
        source.to_owned(),
    )
    .ok()?
    .into_iter()
    .map(|file| SourceFile {
        module_path: file.module_path,
        source: file.source,
    })
    .collect::<Vec<_>>();
    let root = sources::load(files)
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
    WarmupOutput {
        source_cache_hits: 0,
        source_cache_misses: 0,
        source_cache_clone_ms: 0.0,
        source_cache_build_ms: 0.0,
        embedded_std_artifacts: yulang::stdlib::embedded_std_files().len(),
        embedded_std_runtime_bindings: 0,
        embedded_std_artifacts_bytes: embedded_std_source_bytes(),
        embedded_std_artifacts_valid: true,
        embedded_std_artifacts_fallback_reason: None,
        total_ms: 0.0,
    }
}

pub fn embedded_std_status_inner() -> EmbeddedStdArtifactsOutput {
    EmbeddedStdArtifactsOutput {
        artifacts: yulang::stdlib::embedded_std_files().len(),
        runtime_bindings: 0,
        bytes: embedded_std_source_bytes(),
        valid: true,
        fallback_reason: None,
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
        Ok(output) if should_retry_with_embedded_std(&output.errors) => {
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
    let files =
        yulang::collect_source_text_with_embedded_std(PLAYGROUND_ENTRY, source.to_string())?;
    let output = build_named_control_from_collected_sources(files)?;
    run_built_control_program_with_host(output)
}

fn run_control_from_source_text_with_playground_std(
    source: &str,
) -> Result<WasmControlOutput, yulang::RouteError> {
    let files = yulang::collect_source_text_with_embedded_playground_std(
        PLAYGROUND_ENTRY,
        source.to_string(),
    )?;
    let output = build_named_control_from_collected_sources(files)?;
    run_built_control_program_with_host(output)
}

#[derive(Debug, Clone, PartialEq)]
struct NamedControlBuild {
    output: yulang::BuildControlOutput,
    constructor_names: ConstructorNames,
}

type ConstructorNames = HashMap<control_vm::DefId, String>;

fn build_named_control_from_collected_sources(
    files: Vec<yulang::CollectedSource>,
) -> Result<NamedControlBuild, yulang::RouteError> {
    let poly = yulang::build_poly_from_collected_sources(files)?;
    let constructor_names = constructor_display_names(&poly);
    let output = yulang::build_control_from_poly_output(&poly)?;
    Ok(NamedControlBuild {
        output,
        constructor_names,
    })
}

fn constructor_display_names(poly: &yulang::BuildPolyOutput) -> ConstructorNames {
    poly.arena
        .constructors
        .iter()
        .map(|(def, constructor)| (control_vm::DefId(def.0), constructor.name.clone()))
        .collect()
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
        stdout,
    })
}

fn handle_host_effect(
    path: &[String],
    payload: &control_vm::Value,
    stdout: &mut String,
) -> Option<control_vm::Value> {
    if path == ["std", "io", "console", "out", "write"] {
        let text = host_string_payload(payload)?;
        stdout.push_str(text);
        return Some(control_vm::Value::Unit);
    }
    None
}

fn host_string_payload(value: &control_vm::Value) -> Option<&str> {
    match value {
        control_vm::Value::Str(value) => Some(value.as_str()),
        control_vm::Value::Marked { value, .. } => host_string_payload(value),
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
            types: Vec::new(),
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
        control_vm::Value::Str(value) => format!("{value:?}"),
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
        control_vm::Value::EffectOp { path } => format!("<effect-op {}>", path.join("::")),
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

fn embedded_std_source_bytes() -> usize {
    yulang::stdlib::embedded_std_files()
        .iter()
        .map(|file| file.source.len())
        .sum()
}

fn source_likely_needs_embedded_std(source: &str) -> bool {
    source.contains("std::")
        || source.contains("use std")
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

fn should_retry_with_embedded_std(errors: &[String]) -> bool {
    errors.iter().any(|error| {
        error.contains("unresolved value name")
            || error.contains("unresolved type name")
            || error.contains("UnresolvedName")
            || error.contains("UnresolvedTypeName")
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
mod tests {
    use super::*;

    #[test]
    fn run_inner_uses_no_std_fast_path_for_core_source() {
        clear_std_cache();
        let output = run_inner("my id x = x\nid(42)\n");

        assert!(output.ok, "{output:?}");
        assert_eq!(output.file_count, 1);
        assert_eq!(
            output
                .timings
                .as_ref()
                .map(|timing| timing.used_embedded_std),
            Some(false)
        );
        assert_eq!(
            output.results.first().map(|result| result.value.as_str()),
            Some("42")
        );
        assert_eq!(output.text, "run roots [42]\n");
    }

    #[test]
    fn run_inner_retries_unresolved_core_names_with_embedded_std() {
        clear_std_cache();
        let output = run_inner("1 + 2\n");

        assert!(output.ok, "{output:?}");
        assert_eq!(
            output
                .timings
                .as_ref()
                .map(|timing| timing.used_embedded_std),
            Some(true)
        );
        assert_eq!(
            output.results.first().map(|result| result.value.as_str()),
            Some("3")
        );
    }

    #[test]
    fn run_inner_uses_compact_playground_std_for_mixed_numeric_add() {
        clear_std_cache();
        let output = run_inner("1 + 1.2\n");

        assert!(output.ok, "{output:?}");
        assert_eq!(
            output
                .timings
                .as_ref()
                .map(|timing| timing.used_embedded_std),
            Some(true)
        );
        assert_eq!(
            output.results.first().map(|result| result.value.as_str()),
            Some("2.2")
        );
        assert!(output.file_count < yulang::stdlib::embedded_std_files().len() + 1);
    }

    #[test]
    fn run_inner_uses_compact_playground_std_for_struct_method_example() {
        clear_std_cache();
        let output = run_inner(
            "\
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

point { x: 3, y: 4 } .norm2 + 1.12
",
        );

        assert!(output.ok, "{output:?}");
        assert_eq!(
            output
                .timings
                .as_ref()
                .map(|timing| timing.used_embedded_std),
            Some(true)
        );
        assert_eq!(
            output.results.first().map(|result| result.value.as_str()),
            Some("26.12")
        );
        assert!(output.file_count < yulang::stdlib::embedded_std_files().len() + 1);
    }

    #[test]
    fn run_inner_uses_compact_playground_std_for_list_update_example() {
        clear_std_cache();
        let output = run_inner(
            "\
{
    my $xs = [
        2
        3
        4
    ]
    &xs[1] = 6
    $xs
}
",
        );

        assert!(output.ok, "{output:?}");
        assert_eq!(
            output
                .timings
                .as_ref()
                .map(|timing| timing.used_embedded_std),
            Some(true)
        );
        assert_eq!(
            output.results.first().map(|result| result.value.as_str()),
            Some("[2, 6, 4]")
        );
        assert!(output.file_count < yulang::stdlib::embedded_std_files().len() + 1);
    }

    #[test]
    fn run_inner_uses_embedded_std_only_when_needed() {
        clear_std_cache();
        let output = run_inner("each(1..3).list\n");

        assert!(output.ok, "{output:?}");
        assert_eq!(
            output
                .timings
                .as_ref()
                .map(|timing| timing.used_embedded_std),
            Some(true)
        );
        assert_eq!(output.text, "run roots [[1, 2, 3]]\n");
    }

    #[test]
    fn run_inner_routes_junction_prelude_names_to_embedded_std() {
        clear_std_cache();
        let output = run_inner("if all [1, 2, 3] < any [2, 3, 4]:\n  1\nelse:\n  0\n");

        assert!(output.ok, "{output:?}");
        assert_eq!(
            output
                .timings
                .as_ref()
                .map(|timing| timing.used_embedded_std),
            Some(true)
        );
        assert_eq!(output.text, "run roots [1]\n");
    }

    #[test]
    fn run_inner_handles_console_out_as_stdout() {
        clear_std_cache();
        let output = run_inner("println \"hello\"\n1 + 2\n");

        assert!(output.ok, "{output:?}");
        assert_eq!(output.stdout, "hello\n");
        assert_eq!(
            output.results.first().map(|result| result.value.as_str()),
            Some("()")
        );
        assert_eq!(
            output.results.get(1).map(|result| result.value.as_str()),
            Some("3")
        );
    }

    #[test]
    fn run_inner_keeps_sub_return_through_for_callback_before_println() {
        clear_std_cache();
        let source = "\
our g h = sub:
    for i in 0..3:
        h i
    return 1

sub:
    my b = g \\i -> if i == 0: return i
    println b.show
    2
";
        let output = run_inner(source);
        let full_std_output = run_control_from_source_text_with_embedded_std(source).unwrap();

        assert_eq!(full_std_output.stdout, "");
        assert_eq!(full_std_output.text, "run roots [0]\n");

        assert!(output.ok, "{output:?}");
        assert_eq!(output.stdout, full_std_output.stdout);
        assert_eq!(
            output.results.first().map(|result| result.value.as_str()),
            Some("0")
        );
        assert_eq!(output.text, full_std_output.text);
    }

    #[test]
    fn run_inner_runs_nondet_once_triple() {
        clear_std_cache();
        let source = "\
{
    my a = each 1..
    my b = each a<..
    my c = each b<..

    guard: a * a + b * b == c * c

    (a, b, c)
} .once
";
        let output = run_inner(source);
        let full_std_output = run_control_from_source_text_with_embedded_std(source).unwrap();

        assert_eq!(full_std_output.text, "run roots [just (3, 4, 5)]\n");
        assert!(output.ok, "{output:?}");
        assert_eq!(
            output.results.first().map(|result| result.value.as_str()),
            Some("just (3, 4, 5)")
        );
        assert_eq!(output.text, full_std_output.text);
    }

    #[test]
    fn colorize_inner_reports_token_spans() {
        let output = colorize_inner("// note\nmy x = \"日本語\"\n");

        assert!(output.ok, "{output:?}");
        assert!(output.spans.iter().any(|span| {
            span.kind == HighlightKind::Comment && span.start == 0 && span.end == 7
        }));
        assert!(output.spans.iter().any(|span| {
            span.kind == HighlightKind::Keyword && span.start == 8 && span.end == 10
        }));
        assert!(
            output
                .spans
                .iter()
                .any(|span| { span.kind == HighlightKind::String && span.start >= 15 })
        );
    }

    #[test]
    fn colorize_inner_uses_playground_prelude_ops() {
        let source = "my y = x<..\n";
        let output = colorize_inner(source);

        assert!(output.ok, "{output:?}");
        assert!(output.spans.iter().any(|span| {
            span.kind == HighlightKind::Keyword && &source[span.start..span.end] == "my"
        }));
        assert!(output.spans.iter().any(|span| {
            span.kind == HighlightKind::Operator && &source[span.start..span.end] == "<.."
        }));
        assert!(
            !output
                .spans
                .iter()
                .any(|span| &source[span.start..span.end] == "<")
        );
    }

    #[test]
    fn colorize_inner_uses_editor_semantic_token_kinds() {
        let source = "\
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

point { x: 3, y: 4 } .norm2
";
        let output = colorize_inner(source);

        assert!(output.ok, "{output:?}");
        assert!(output.spans.iter().any(|span| {
            span.kind == HighlightKind::Type && &source[span.start..span.end] == "point"
        }));
        assert!(output.spans.iter().any(|span| {
            span.kind == HighlightKind::Function && &source[span.start..span.end] == "norm2"
        }));
        assert!(!output.spans.iter().any(|span| {
            span.kind == HighlightKind::Property && &source[span.start..span.end] == "norm2"
        }));
    }

    #[test]
    fn run_inner_caches_repeated_source() {
        clear_std_cache();
        let first = run_inner("my id x = x\nid(42)\n");
        let second = run_inner("my id x = x\nid(42)\n");

        assert!(first.ok, "{first:?}");
        assert!(second.ok, "{second:?}");
        assert_eq!(
            second
                .timings
                .as_ref()
                .map(|timing| timing.source_cache_hits),
            Some(1)
        );
    }

    #[test]
    fn check_inner_returns_structured_diagnostic() {
        let output = check_inner("my x: int = true\n");

        assert!(!output.ok, "{output:?}");
        assert_eq!(output.diagnostics.len(), 1);
        assert_eq!(output.diagnostics[0].label.as_deref(), Some("x"));
        assert_eq!(
            output.diagnostics[0].message,
            "type mismatch: bool is not int"
        );
    }

    #[test]
    fn dump_poly_inner_reports_lowering_errors() {
        let output = dump_poly_inner("my x: int = true\n");

        assert!(!output.ok, "{output:?}");
        assert!(output.text.contains("my d"));
        assert_eq!(output.errors, vec!["type mismatch: bool is not int"]);
    }
}
