use serde::Serialize;
use std::fmt::Write as _;
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
    let mut out = String::new();
    format_vm_value_into(&mut out, value);
    out
}

fn format_vm_value_into(out: &mut String, value: &runtime::VmValue) {
    match value {
        runtime::VmValue::Int(value) | runtime::VmValue::Float(value) => out.push_str(value),
        runtime::VmValue::String(value) => {
            let _ = write!(out, "{:?}", value.to_flat_string());
        }
        runtime::VmValue::Bool(value) => out.push_str(if *value { "true" } else { "false" }),
        runtime::VmValue::Unit => out.push_str("()"),
        runtime::VmValue::List(items) => format_vm_list_into(out, items),
        runtime::VmValue::Tuple(items) => {
            out.push('(');
            format_vm_values(out, items.iter());
            out.push(')');
        }
        runtime::VmValue::Record(fields) => {
            out.push('{');
            let mut first = true;
            for (name, value) in fields {
                push_separator(out, &mut first);
                let _ = write!(out, "{} = ", name.0);
                format_vm_value_into(out, value);
            }
            out.push('}');
        }
        runtime::VmValue::Variant { tag, value } => match value {
            Some(value) => {
                out.push_str(&tag.0);
                out.push(' ');
                format_vm_value_into(out, value);
            }
            None => out.push_str(&tag.0),
        },
        runtime::VmValue::EffectOp(path) => {
            let _ = write!(out, "<effect-op {}>", format_core_path(path));
        }
        runtime::VmValue::PrimitiveOp(_) => out.push_str("<primitive>"),
        runtime::VmValue::Resume(_) => out.push_str("<resume>"),
        runtime::VmValue::Closure(_) => out.push_str("<closure>"),
        runtime::VmValue::Thunk(_) => out.push_str("<thunk>"),
        runtime::VmValue::EffectId(id) => {
            let _ = write!(out, "<effect-id {id}>");
        }
    }
}

fn format_vm_list_into(
    out: &mut String,
    items: &runtime::runtime::list_tree::ListTree<runtime::VmValue>,
) {
    out.push('[');
    let mut first = true;
    format_vm_list_items(out, items, &mut first);
    out.push(']');
}

fn format_vm_list_items(
    out: &mut String,
    items: &runtime::runtime::list_tree::ListTree<runtime::VmValue>,
    first: &mut bool,
) {
    match items {
        runtime::runtime::list_tree::ListTree::Empty => {}
        runtime::runtime::list_tree::ListTree::Leaf(value) => {
            push_separator(out, first);
            format_vm_value_into(out, value);
        }
        runtime::runtime::list_tree::ListTree::Node(node) => {
            format_vm_list_items(out, &node.left, first);
            format_vm_list_items(out, &node.right, first);
        }
    }
}

fn format_vm_values<'a>(out: &mut String, values: impl Iterator<Item = &'a runtime::VmValue>) {
    let mut first = true;
    for value in values {
        push_separator(out, &mut first);
        format_vm_value_into(out, value);
    }
}

fn push_separator(out: &mut String, first: &mut bool) {
    if *first {
        *first = false;
    } else {
        out.push_str(", ");
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
