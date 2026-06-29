use control_vm::DefId;

use list_tree::ListTree;

use super::{RuntimeEvidenceValue, SharedValue};

pub(super) fn format_values_with_labels(
    values: &[RuntimeEvidenceValue],
    labels: Option<&poly::dump::DumpLabels>,
) -> String {
    let values = values
        .iter()
        .map(|value| format_value_with_labels(value, labels))
        .collect::<Vec<_>>();
    format!("[{}]", values.join(", "))
}

pub(super) fn format_value(value: &RuntimeEvidenceValue) -> String {
    format_value_with_labels(value, None)
}

pub(super) fn format_float(value: f64) -> String {
    let text = value.to_string();
    if text.contains('.') || text.contains('e') || text.contains('E') {
        text
    } else {
        format!("{text}.0")
    }
}

pub(super) fn format_value_with_labels(
    value: &RuntimeEvidenceValue,
    labels: Option<&poly::dump::DumpLabels>,
) -> String {
    match value {
        RuntimeEvidenceValue::Int(value) => value.to_string(),
        RuntimeEvidenceValue::BigInt(value) => value.clone(),
        RuntimeEvidenceValue::Float(value) => value.to_string(),
        RuntimeEvidenceValue::Str(value) => format!("{value:?}"),
        RuntimeEvidenceValue::Bytes(value) => format!("<bytes len={}>", value.len()),
        RuntimeEvidenceValue::Bool(value) => value.to_string(),
        RuntimeEvidenceValue::Unit => "()".to_string(),
        RuntimeEvidenceValue::Tuple(values) => format_delimited("(", ")", values, labels),
        RuntimeEvidenceValue::List(values) => format_list(values, labels),
        RuntimeEvidenceValue::Record(fields) => {
            let fields = fields
                .iter()
                .map(|field| {
                    format!(
                        "{}: {}",
                        field.name,
                        format_value_with_labels(&field.value, labels)
                    )
                })
                .collect::<Vec<_>>();
            format!("{{{}}}", fields.join(", "))
        }
        RuntimeEvidenceValue::PolyVariant { tag, payloads } => {
            if payloads.is_empty() {
                tag.clone()
            } else {
                format!("{tag}({})", format_shared_values(payloads, labels))
            }
        }
        RuntimeEvidenceValue::DataConstructor { def, payloads } => {
            let constructor = format_constructor_name(labels, *def);
            if payloads.is_empty() {
                constructor
            } else {
                format!("{constructor}({})", format_shared_values(payloads, labels))
            }
        }
        RuntimeEvidenceValue::ConstructorFunction { def, args, arity } => {
            let constructor = format_constructor_name(labels, *def);
            format!("<ctor-fn {constructor} {}/{arity}>", args.len())
        }
        RuntimeEvidenceValue::PrimitiveOp { op, .. } => format!("<primitive {op:?}>"),
        RuntimeEvidenceValue::FunctionAdapter { .. } => "<function-adapter>".to_string(),
        RuntimeEvidenceValue::Marked { value, .. } => format_value_with_labels(value, labels),
        RuntimeEvidenceValue::Closure(_) | RuntimeEvidenceValue::RecursiveClosure { .. } => {
            "<closure>".to_string()
        }
        RuntimeEvidenceValue::EffectOp { path, .. } => {
            format!("<effect-op {}>", path.join("::"))
        }
        RuntimeEvidenceValue::Continuation(_) => "<continuation>".to_string(),
        RuntimeEvidenceValue::Thunk(_) => "<thunk>".to_string(),
    }
}

fn format_delimited(
    open: &str,
    close: &str,
    values: &[SharedValue],
    labels: Option<&poly::dump::DumpLabels>,
) -> String {
    let mut out = String::new();
    out.push_str(open);
    out.push_str(&format_shared_values(values, labels));
    if values.len() == 1 && open == "(" {
        out.push(',');
    }
    out.push_str(close);
    out
}

fn format_list(values: &ListTree<SharedValue>, labels: Option<&poly::dump::DumpLabels>) -> String {
    let mut items = Vec::with_capacity(values.len());
    values.for_each_ref(&mut |value| items.push(value.clone()));
    format_delimited("[", "]", &items, labels)
}

fn format_shared_values(values: &[SharedValue], labels: Option<&poly::dump::DumpLabels>) -> String {
    values
        .iter()
        .map(|value| format_value_with_labels(value.as_ref(), labels))
        .collect::<Vec<_>>()
        .join(", ")
}

fn format_constructor_name(labels: Option<&poly::dump::DumpLabels>, def: DefId) -> String {
    let Some(label) = labels.and_then(|labels| labels.def_label(poly::expr::DefId(def.0))) else {
        return format!("<ctor d{}>", def.0);
    };
    shorten_constructor_label(label)
}

fn shorten_constructor_label(label: &str) -> String {
    let mut parts = label.rsplit('.').filter(|part| !part.is_empty());
    let Some(last) = parts.next() else {
        return label.to_string();
    };
    let Some(parent) = parts.next() else {
        return last.to_string();
    };
    format!("{parent}::{last}")
}
