//! Text formatting for control VM runtime values.

use crate::runtime::Value;

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
    match value {
        Value::Int(value) => value.to_string(),
        Value::BigInt(value) => value.to_string(),
        Value::Float(value) => value.to_string(),
        Value::Str(value) => format!("{value:?}"),
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
        Value::Closure(_) => "<closure>".to_string(),
        Value::Thunk(_) => "<thunk>".to_string(),
        Value::FunctionAdapter(_) => "<function-adapter>".to_string(),
        Value::EffectOp { path } => format!("<effect-op {}>", path.join("::")),
        Value::Continuation(id) => format!("<continuation {}>", id.0),
        Value::Marked { value, markers } => {
            let mut out = format_value(value);
            out.push_str(" @ [");
            for (index, marker) in markers.iter().enumerate() {
                if index > 0 {
                    out.push_str(", ");
                }
                out.push_str(&marker.path.join("::"));
                out.push('#');
                out.push_str(&marker.id.0.to_string());
                out.push(':');
                out.push_str(&marker.depth.to_string());
            }
            out.push(']');
            out
        }
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
