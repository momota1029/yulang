//! Text formatting for control VM runtime values.

use crate::runtime::{Value, ValueField};

pub fn format_values(values: &[Value]) -> String {
    let mut out = String::new();
    out.push('[');
    for (index, value) in values.iter().enumerate() {
        if index > 0 {
            out.push_str(", ");
        }
        out.push_str(&format_value(value));
    }
    out.push(']');
    out
}

fn format_value(value: &Value) -> String {
    if let Some(fraction) = format_fraction_value(value) {
        return fraction;
    }

    match value {
        Value::Int(value) => value.to_string(),
        Value::BigInt(value) => value.to_string(),
        Value::Float(value) => value.to_string(),
        Value::Str(value) => format!("{:?}", value.to_flat_string()),
        Value::Bytes(value) => format!("<bytes len={}>", value.len()),
        Value::Bool(value) => value.to_string(),
        Value::Unit => "()".to_string(),
        Value::Tuple(values) => format_delimited_values("(", ")", values),
        Value::List(values) => {
            let values = values
                .to_vec()
                .into_iter()
                .map(|value| (*value).clone())
                .collect::<Vec<_>>();
            format_delimited_values("[", "]", &values)
        }
        Value::Record(fields) => {
            let mut out = String::new();
            out.push('{');
            for (index, field) in fields.iter().enumerate() {
                if index > 0 {
                    out.push_str(", ");
                }
                out.push_str(&field.name);
                out.push_str(": ");
                out.push_str(&format_value(&field.value));
            }
            out.push('}');
            out
        }
        Value::PolyVariant { tag, payloads } => {
            if payloads.is_empty() {
                return tag.clone();
            }
            format!("{tag}{}", format_delimited_values("(", ")", payloads))
        }
        Value::DataConstructor { def, payloads } => {
            if payloads.is_empty() {
                return format!("<ctor d{}>", def.0);
            }
            format!(
                "<ctor d{}>{}",
                def.0,
                format_delimited_values("(", ")", payloads)
            )
        }
        Value::ConstructorFunction(constructor) => {
            format!(
                "<ctor-fn d{} {}/{}>",
                constructor.def.0,
                constructor.args.len(),
                constructor.arity
            )
        }
        Value::PrimitiveOp(primitive) => {
            format!(
                "<prim {:?} {}/{}>",
                primitive.op,
                primitive.args.len(),
                primitive.op.arity()
            )
        }
        Value::Closure(_) | Value::RecursiveClosure { .. } => "<closure>".to_string(),
        Value::Thunk(_) => "<thunk>".to_string(),
        Value::FunctionAdapter(_) => "<function-adapter>".to_string(),
        Value::EffectOp { path } => format!("<effect-op {}>", path.join("::")),
        Value::Continuation(id) => format!("<continuation {}>", id.0),
        Value::Marked { value, .. } => format_value(value),
    }
}

fn format_fraction_value(value: &Value) -> Option<String> {
    // Runtime values erase struct identity, so raw root formatting recognizes
    // std::num::frac by its canonical lowered shape.
    match value {
        Value::Record(fields) => format_fraction_record(fields),
        Value::DataConstructor { payloads, .. } if payloads.len() == 1 => {
            format_fraction_payload(&payloads[0])
        }
        Value::Marked { value, .. } => format_fraction_value(value),
        _ => None,
    }
}

fn format_fraction_payload(value: &Value) -> Option<String> {
    match value {
        Value::Record(fields) => format_fraction_record(fields),
        Value::Marked { value, .. } => format_fraction_payload(value),
        _ => None,
    }
}

fn format_fraction_record(fields: &[ValueField]) -> Option<String> {
    if fields.len() != 2 {
        return None;
    }

    let num = int_field(fields, "num")?;
    let den = int_field(fields, "den")?;
    if den == 1 {
        Some(num.to_string())
    } else {
        Some(format!("{num}/{den}"))
    }
}

fn int_field(fields: &[ValueField], name: &str) -> Option<i64> {
    fields
        .iter()
        .find(|field| field.name.as_str() == name)
        .and_then(|field| int_value(&field.value))
}

fn int_value(value: &Value) -> Option<i64> {
    match value {
        Value::Int(value) => Some(*value),
        Value::Marked { value, .. } => int_value(value),
        _ => None,
    }
}

fn format_delimited_values(open: &str, close: &str, values: &[Value]) -> String {
    let mut out = String::new();
    out.push_str(open);
    for (index, value) in values.iter().enumerate() {
        if index > 0 {
            out.push_str(", ");
        }
        out.push_str(&format_value(value));
    }
    if values.len() == 1 && open == "(" {
        out.push(',');
    }
    out.push_str(close);
    out
}
