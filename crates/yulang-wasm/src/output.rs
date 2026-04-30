use serde::Serialize;
use yulang_core_ir as core_ir;
use yulang_runtime as runtime;

#[derive(Debug, Clone, Serialize)]
pub struct RunOutput {
    pub ok: bool,
    pub results: Vec<RunResult>,
    pub types: Vec<TypeResult>,
    pub diagnostics: Vec<Diagnostic>,
}

#[derive(Debug, Clone, Serialize)]
pub struct RunResult {
    pub index: usize,
    pub value: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct TypeResult {
    pub name: String,
    pub ty: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct Diagnostic {
    pub severity: DiagnosticSeverity,
    pub message: String,
    pub start: usize,
    pub end: usize,
}

impl Diagnostic {
    pub fn error(message: impl Into<String>, source_len: usize) -> Self {
        Self {
            severity: DiagnosticSeverity::Error,
            message: message.into(),
            start: 0,
            end: source_len,
        }
    }
}

#[derive(Debug, Clone, Copy, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum DiagnosticSeverity {
    Error,
}

pub fn format_vm_result(result: &runtime::VmResult) -> String {
    match result {
        runtime::VmResult::Value(value) => format_vm_value(value),
        runtime::VmResult::Request(request) => format!(
            "request {} {} blocked={:?}",
            format_core_path(&request.effect),
            format_vm_value(&request.payload),
            request.blocked_id
        ),
    }
}

fn format_vm_value(value: &runtime::VmValue) -> String {
    match value {
        runtime::VmValue::Int(value) | runtime::VmValue::Float(value) => value.clone(),
        runtime::VmValue::String(value) => format!("{:?}", value.to_flat_string()),
        runtime::VmValue::Bool(value) => value.to_string(),
        runtime::VmValue::Unit => "()".to_string(),
        runtime::VmValue::List(items) => format!(
            "[{}]",
            items
                .to_vec()
                .iter()
                .map(format_vm_value)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        runtime::VmValue::Tuple(items) => format!(
            "({})",
            items
                .iter()
                .map(format_vm_value)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        runtime::VmValue::Record(fields) => format!(
            "{{{}}}",
            fields
                .iter()
                .map(|(name, value)| format!("{} = {}", name.0, format_vm_value(value)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        runtime::VmValue::Variant { tag, value } => match value {
            Some(value) => format!("{} {}", tag.0, format_vm_value(value)),
            None => tag.0.clone(),
        },
        runtime::VmValue::EffectOp(path) => format!("<effect-op {}>", format_core_path(path)),
        runtime::VmValue::PrimitiveOp(_) => "<primitive>".to_string(),
        runtime::VmValue::Resume(_) => "<resume>".to_string(),
        runtime::VmValue::Closure(_) => "<closure>".to_string(),
        runtime::VmValue::Thunk(_) => "<thunk>".to_string(),
        runtime::VmValue::EffectId(id) => format!("<effect-id {id}>"),
    }
}

fn format_core_path(path: &core_ir::Path) -> String {
    if path.segments.is_empty() {
        "<root>".to_string()
    } else {
        path.segments
            .iter()
            .map(|segment| segment.0.as_str())
            .collect::<Vec<_>>()
            .join("::")
    }
}
