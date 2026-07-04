use control_vm::DefId;

use list_tree::ListTree;

use super::{RuntimeEvidenceDisplayContext, RuntimeEvidenceValue, SharedValue};

pub(super) fn format_values_with_labels(
    values: &[RuntimeEvidenceValue],
    labels: Option<&poly::dump::DumpLabels>,
) -> String {
    let values = values
        .iter()
        .map(|value| format_value_in_context(value, labels, None, ConstructorSyntax::Canonical))
        .collect::<Vec<_>>();
    format!("[{}]", values.join(", "))
}

pub(super) fn format_values_with_display_context(
    values: &[RuntimeEvidenceValue],
    labels: Option<&poly::dump::DumpLabels>,
    display: &RuntimeEvidenceDisplayContext,
) -> String {
    let values = values
        .iter()
        .map(|value| {
            format_value_in_context(value, labels, Some(display), ConstructorSyntax::Surface)
        })
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
    format_value_in_context(value, labels, None, ConstructorSyntax::Canonical)
}

pub(super) fn format_value_with_display_context(
    value: &RuntimeEvidenceValue,
    labels: Option<&poly::dump::DumpLabels>,
    display: &RuntimeEvidenceDisplayContext,
) -> String {
    format_value_in_context(value, labels, Some(display), ConstructorSyntax::Surface)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ConstructorSyntax {
    Canonical,
    Surface,
}

fn format_value_in_context(
    value: &RuntimeEvidenceValue,
    labels: Option<&poly::dump::DumpLabels>,
    display: Option<&RuntimeEvidenceDisplayContext>,
    constructor_syntax: ConstructorSyntax,
) -> String {
    match value {
        RuntimeEvidenceValue::Int(value) => value.to_string(),
        RuntimeEvidenceValue::BigInt(value) => value.clone(),
        RuntimeEvidenceValue::Float(value) => value.to_string(),
        RuntimeEvidenceValue::Str(value) => format!("{value:?}"),
        RuntimeEvidenceValue::Bytes(value) => format!("<bytes len={}>", value.len()),
        RuntimeEvidenceValue::Bool(value) => value.to_string(),
        RuntimeEvidenceValue::Unit => "()".to_string(),
        RuntimeEvidenceValue::HostHandle { type_id, handle } => {
            format!("<host-handle type={type_id} handle={handle}>")
        }
        RuntimeEvidenceValue::Tuple(values) => {
            format_delimited("(", ")", values, labels, display, constructor_syntax)
        }
        RuntimeEvidenceValue::List(values) => {
            format_list(values, labels, display, constructor_syntax)
        }
        RuntimeEvidenceValue::Record(fields) => {
            let fields = fields
                .iter()
                .map(|field| {
                    format!(
                        "{}: {}",
                        field.name,
                        format_value_in_context(&field.value, labels, display, constructor_syntax)
                    )
                })
                .collect::<Vec<_>>();
            format!("{{{}}}", fields.join(", "))
        }
        RuntimeEvidenceValue::PolyVariant { tag, payloads } => {
            if payloads.is_empty() {
                tag.clone()
            } else {
                format!(
                    "{tag}({})",
                    format_shared_values(payloads, labels, display, constructor_syntax)
                )
            }
        }
        RuntimeEvidenceValue::DataConstructor { def, payloads } => {
            let constructor = format_constructor_name(labels, display, *def);
            format_data_constructor(&constructor, payloads, labels, display, constructor_syntax)
        }
        RuntimeEvidenceValue::ConstructorFunction { def, args, arity } => {
            let constructor = format_constructor_name(labels, display, *def);
            format!("<ctor-fn {constructor} {}/{arity}>", args.len())
        }
        RuntimeEvidenceValue::PrimitiveOp { op, .. } => format!("<primitive {op:?}>"),
        RuntimeEvidenceValue::FunctionAdapter { .. } => "<function-adapter>".to_string(),
        RuntimeEvidenceValue::Marked { value, .. } => {
            format_value_in_context(value, labels, display, constructor_syntax)
        }
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
    display: Option<&RuntimeEvidenceDisplayContext>,
    constructor_syntax: ConstructorSyntax,
) -> String {
    let mut out = String::new();
    out.push_str(open);
    out.push_str(&format_shared_values(
        values,
        labels,
        display,
        constructor_syntax,
    ));
    if values.len() == 1 && open == "(" {
        out.push(',');
    }
    out.push_str(close);
    out
}

fn format_list(
    values: &ListTree<SharedValue>,
    labels: Option<&poly::dump::DumpLabels>,
    display: Option<&RuntimeEvidenceDisplayContext>,
    constructor_syntax: ConstructorSyntax,
) -> String {
    let mut items = Vec::with_capacity(values.len());
    values.for_each_ref(&mut |value| items.push(value.clone()));
    format_delimited("[", "]", &items, labels, display, constructor_syntax)
}

fn format_shared_values(
    values: &[SharedValue],
    labels: Option<&poly::dump::DumpLabels>,
    display: Option<&RuntimeEvidenceDisplayContext>,
    constructor_syntax: ConstructorSyntax,
) -> String {
    values
        .iter()
        .map(|value| format_value_in_context(value.as_ref(), labels, display, constructor_syntax))
        .collect::<Vec<_>>()
        .join(", ")
}

fn format_data_constructor(
    constructor: &str,
    payloads: &[SharedValue],
    labels: Option<&poly::dump::DumpLabels>,
    display: Option<&RuntimeEvidenceDisplayContext>,
    constructor_syntax: ConstructorSyntax,
) -> String {
    if constructor_syntax == ConstructorSyntax::Canonical {
        return if payloads.is_empty() {
            constructor.to_string()
        } else {
            format!(
                "{constructor}({})",
                format_shared_values(payloads, labels, display, constructor_syntax)
            )
        };
    }

    match payloads {
        [] => constructor.to_string(),
        [payload] => {
            let payload =
                format_value_in_context(payload.as_ref(), labels, display, constructor_syntax);
            if has_top_level_whitespace(&payload) {
                format!("{constructor}({payload})")
            } else {
                format!("{constructor} {payload}")
            }
        }
        payloads => format!(
            "{constructor}({})",
            format_shared_values(payloads, labels, display, constructor_syntax)
        ),
    }
}

fn has_top_level_whitespace(text: &str) -> bool {
    let mut depth = 0usize;
    let mut chars = text.chars().peekable();
    while let Some(ch) = chars.next() {
        match ch {
            '"' => {
                while let Some(inner) = chars.next() {
                    if inner == '\\' {
                        chars.next();
                    } else if inner == '"' {
                        break;
                    }
                }
            }
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth = depth.saturating_sub(1),
            ch if depth == 0 && ch.is_whitespace() => return true,
            _ => {}
        }
    }
    false
}

fn format_constructor_name(
    labels: Option<&poly::dump::DumpLabels>,
    display: Option<&RuntimeEvidenceDisplayContext>,
    def: DefId,
) -> String {
    if let Some(name) = display.and_then(|display| display.constructor_name(def)) {
        return name.to_string();
    }
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

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use control_vm::DefId;

    use super::*;

    fn labels() -> poly::dump::DumpLabels {
        let mut labels = poly::dump::DumpLabels::new();
        labels.set_def_label(poly::expr::DefId(1), "std.data.opt.opt.just");
        labels.set_def_label(poly::expr::DefId(2), "local.wrapper.wrap");
        labels
    }

    fn int(value: i64) -> SharedValue {
        Rc::new(RuntimeEvidenceValue::Int(value))
    }

    fn constructor(def: u32, payloads: Vec<SharedValue>) -> RuntimeEvidenceValue {
        RuntimeEvidenceValue::DataConstructor {
            def: DefId(def),
            payloads,
        }
    }

    #[test]
    fn canonical_constructor_display_keeps_family_and_c_style_payload() {
        let value = constructor(
            1,
            vec![Rc::new(RuntimeEvidenceValue::Tuple(vec![
                int(3),
                int(4),
                int(5),
            ]))],
        );

        assert_eq!(
            format_value_with_labels(&value, Some(&labels())),
            "opt::just((3, 4, 5))"
        );
    }

    #[test]
    fn surface_constructor_display_uses_context_name_and_ml_application() {
        let mut display = RuntimeEvidenceDisplayContext::new();
        display.set_constructor_name(DefId(1), "just");
        let value = constructor(
            1,
            vec![Rc::new(RuntimeEvidenceValue::Tuple(vec![
                int(3),
                int(4),
                int(5),
            ]))],
        );

        assert_eq!(
            format_value_with_display_context(&value, Some(&labels()), &display),
            "just (3, 4, 5)"
        );
    }

    #[test]
    fn surface_constructor_display_uses_c_style_when_payload_has_top_level_space() {
        let mut display = RuntimeEvidenceDisplayContext::new();
        display
            .set_constructor_name(DefId(1), "just")
            .set_constructor_name(DefId(2), "wrap");
        let inner = Rc::new(constructor(1, vec![int(1)]));
        let value = constructor(2, vec![inner]);

        assert_eq!(
            format_value_with_display_context(&value, Some(&labels()), &display),
            "wrap(just 1)"
        );
    }
}
