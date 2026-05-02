use super::*;

pub(super) fn is_role_method_path(path: &core_ir::Path) -> bool {
    let Some(role) = path.segments.iter().rev().nth(1) else {
        return false;
    };
    role.0.chars().next().is_some_and(char::is_uppercase)
}

pub(super) fn is_specialized_path(path: &core_ir::Path) -> bool {
    path.segments
        .last()
        .is_some_and(|segment| segment.0.contains("__mono"))
}

pub(super) fn specialization_suffix(path: &core_ir::Path) -> Option<usize> {
    path.segments
        .last()?
        .0
        .rsplit_once("__mono")?
        .1
        .parse()
        .ok()
}

pub(super) fn unspecialized_path(path: &core_ir::Path) -> Option<core_ir::Path> {
    let mut path = path.clone();
    let name = &mut path.segments.last_mut()?.0;
    let index = name.find("__mono")?;
    name.truncate(index);
    Some(path)
}

pub(super) fn canonical_path(path: &core_ir::Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

pub(super) fn canonical_type(ty: &core_ir::Type, out: &mut String) {
    match ty {
        core_ir::Type::Any => out.push('_'),
        core_ir::Type::Never => out.push('!'),
        core_ir::Type::Var(var) => out.push_str(&var.0),
        core_ir::Type::Named { path, args } => {
            out.push_str(&canonical_path(path));
            if !args.is_empty() {
                out.push('<');
                for (index, arg) in args.iter().enumerate() {
                    if index > 0 {
                        out.push(',');
                    }
                    canonical_type_arg(arg, out);
                }
                out.push('>');
            }
        }
        core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            out.push('(');
            canonical_type(param, out);
            out.push('-');
            canonical_type(param_effect, out);
            out.push('/');
            canonical_type(ret_effect, out);
            out.push_str("->");
            canonical_type(ret, out);
            out.push(')');
        }
        core_ir::Type::Tuple(items) => canonical_type_list("(", ")", items, out),
        core_ir::Type::Record(record) => {
            out.push('{');
            for field in &record.fields {
                out.push_str(&field.name.0);
                out.push(':');
                canonical_type(&field.value, out);
                out.push(',');
            }
            out.push('}');
        }
        core_ir::Type::Variant(variant) => {
            out.push('[');
            for case in &variant.cases {
                out.push_str(&case.name.0);
                canonical_type_list("(", ")", &case.payloads, out);
                out.push(',');
            }
            out.push(']');
        }
        core_ir::Type::Row { items, tail } => {
            canonical_type_list("[", "]", items, out);
            out.push('|');
            canonical_type(tail, out);
        }
        core_ir::Type::Union(items) => canonical_type_list("union(", ")", items, out),
        core_ir::Type::Inter(items) => canonical_type_list("inter(", ")", items, out),
        core_ir::Type::Recursive { var, body } => {
            out.push_str("rec ");
            out.push_str(&var.0);
            out.push('.');
            canonical_type(body, out);
        }
    }
}

fn canonical_type_arg(arg: &core_ir::TypeArg, out: &mut String) {
    match arg {
        core_ir::TypeArg::Type(ty) => canonical_type(ty, out),
        core_ir::TypeArg::Bounds(bounds) => {
            out.push_str("bounds(");
            if let Some(lower) = bounds.lower.as_deref() {
                canonical_type(lower, out);
            }
            out.push_str("..");
            if let Some(upper) = bounds.upper.as_deref() {
                canonical_type(upper, out);
            }
            out.push(')');
        }
    }
}

fn canonical_type_list(open: &str, close: &str, items: &[core_ir::Type], out: &mut String) {
    out.push_str(open);
    for (index, item) in items.iter().enumerate() {
        if index > 0 {
            out.push(',');
        }
        canonical_type(item, out);
    }
    out.push_str(close);
}
