use super::*;

pub(crate) fn substitute_role_sig_type(
    sig: &SigType,
    bindings: &HashMap<String, SigType>,
) -> SigType {
    match sig {
        SigType::Prim { path, .. } => {
            if let [segment] = path.segments.as_slice() {
                if let Some(bound) = bindings.get(&segment.0) {
                    return bound.clone();
                }
            }
            sig.clone()
        }
        SigType::Unit { .. } => sig.clone(),
        SigType::Apply { path, args, span } => SigType::Apply {
            path: path.clone(),
            args: args
                .iter()
                .map(|arg| substitute_role_sig_type(arg, bindings))
                .collect(),
            span: *span,
        },
        SigType::Tuple { items, span } => SigType::Tuple {
            items: items
                .iter()
                .map(|item| substitute_role_sig_type(item, bindings))
                .collect(),
            span: *span,
        },
        SigType::Var(SigVar { name, .. }) => {
            bindings.get(name).cloned().unwrap_or_else(|| sig.clone())
        }
        SigType::Record { fields, span } => SigType::Record {
            fields: fields
                .iter()
                .map(|field| SigRecordField {
                    name: field.name.clone(),
                    ty: substitute_role_sig_type(&field.ty, bindings),
                    optional: field.optional,
                })
                .collect(),
            span: *span,
        },
        SigType::RecordTailSpread { fields, tail, span } => SigType::RecordTailSpread {
            fields: fields
                .iter()
                .map(|field| SigRecordField {
                    name: field.name.clone(),
                    ty: substitute_role_sig_type(&field.ty, bindings),
                    optional: field.optional,
                })
                .collect(),
            tail: Box::new(substitute_role_sig_type(tail, bindings)),
            span: *span,
        },
        SigType::RecordHeadSpread { tail, fields, span } => SigType::RecordHeadSpread {
            tail: Box::new(substitute_role_sig_type(tail, bindings)),
            fields: fields
                .iter()
                .map(|field| SigRecordField {
                    name: field.name.clone(),
                    ty: substitute_role_sig_type(&field.ty, bindings),
                    optional: field.optional,
                })
                .collect(),
            span: *span,
        },
        SigType::Fun {
            arg,
            ret_eff,
            ret,
            span,
        } => SigType::Fun {
            arg: Box::new(substitute_role_sig_type(arg, bindings)),
            ret_eff: ret_eff
                .as_ref()
                .map(|row| substitute_role_sig_row(row, bindings)),
            ret: Box::new(substitute_role_sig_type(ret, bindings)),
            span: *span,
        },
    }
}

fn substitute_role_sig_row(row: &SigRow, bindings: &HashMap<String, SigType>) -> SigRow {
    SigRow {
        items: row
            .items
            .iter()
            .map(|item| substitute_role_sig_type(item, bindings))
            .collect(),
        tail: row.tail.clone(),
    }
}
