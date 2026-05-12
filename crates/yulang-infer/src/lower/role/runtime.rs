use super::*;

pub(super) fn runtime_export_scheme(
    state: &LowerState,
    receiver_sig: &SigType,
    expected_sig: &SigType,
) -> typed_ir::Scheme {
    typed_ir::Scheme {
        requirements: Vec::new(),
        body: typed_ir::Type::Fun {
            param: Box::new(export_runtime_sig_type(state, receiver_sig)),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(typed_ir::Type::Never),
            ret: Box::new(export_runtime_sig_type(state, expected_sig)),
        },
    }
}

pub(super) fn runtime_export_role_method_scheme(
    state: &LowerState,
    role_path: &Path,
    receiver_sig: &SigType,
    expected_sig: &SigType,
) -> typed_ir::Scheme {
    let role_arg_infos = state.infer.role_arg_infos_of(role_path);
    let requirements = if role_arg_infos.is_empty() {
        Vec::new()
    } else {
        vec![typed_ir::RoleRequirement {
            role: export_runtime_path(role_path),
            args: role_arg_infos
                .into_iter()
                .map(|info| {
                    let bounds = typed_ir::TypeBounds::exact(typed_ir::Type::Var(
                        typed_ir::TypeVar(info.name.clone()),
                    ));
                    if info.is_input {
                        typed_ir::RoleRequirementArg::Input(bounds)
                    } else {
                        typed_ir::RoleRequirementArg::Associated {
                            name: typed_ir::Name(info.name),
                            bounds,
                        }
                    }
                })
                .collect(),
        }]
    };
    typed_ir::Scheme {
        requirements,
        body: typed_ir::Type::Fun {
            param: Box::new(export_runtime_sig_type(state, receiver_sig)),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(typed_ir::Type::Never),
            ret: Box::new(export_runtime_sig_type(state, expected_sig)),
        },
    }
}

pub(crate) fn export_runtime_sig_type(state: &LowerState, sig: &SigType) -> typed_ir::Type {
    match sig {
        SigType::Prim { path, .. } => typed_ir::Type::Named {
            path: export_runtime_type_path(state, path),
            args: Vec::new(),
        },
        SigType::Apply { path, args, .. } => typed_ir::Type::Named {
            path: export_runtime_type_path(state, path),
            args: args
                .iter()
                .map(|arg| typed_ir::TypeArg::Type(export_runtime_sig_type(state, arg)))
                .collect(),
        },
        SigType::Var(var) => typed_ir::Type::Var(typed_ir::TypeVar(var.name.clone())),
        SigType::Unit { .. } => typed_ir::Type::Named {
            path: typed_ir::Path::from_name(typed_ir::Name("unit".to_string())),
            args: Vec::new(),
        },
        SigType::Tuple { items, .. } => typed_ir::Type::Tuple(
            items
                .iter()
                .map(|item| export_runtime_sig_type(state, item))
                .collect(),
        ),
        SigType::Record { fields, .. } => typed_ir::Type::Record(typed_ir::RecordType {
            fields: fields
                .iter()
                .map(|field| typed_ir::RecordField {
                    name: typed_ir::Name(field.name.0.clone()),
                    value: export_runtime_sig_type(state, &field.ty),
                    optional: field.optional,
                })
                .collect(),
            spread: None,
        }),
        SigType::RecordTailSpread { fields, tail, .. } => {
            typed_ir::Type::Record(typed_ir::RecordType {
                fields: fields
                    .iter()
                    .map(|field| typed_ir::RecordField {
                        name: typed_ir::Name(field.name.0.clone()),
                        value: export_runtime_sig_type(state, &field.ty),
                        optional: field.optional,
                    })
                    .collect(),
                spread: Some(typed_ir::RecordSpread::Tail(Box::new(
                    export_runtime_sig_type(state, tail),
                ))),
            })
        }
        SigType::RecordHeadSpread { tail, fields, .. } => {
            typed_ir::Type::Record(typed_ir::RecordType {
                fields: fields
                    .iter()
                    .map(|field| typed_ir::RecordField {
                        name: typed_ir::Name(field.name.0.clone()),
                        value: export_runtime_sig_type(state, &field.ty),
                        optional: field.optional,
                    })
                    .collect(),
                spread: Some(typed_ir::RecordSpread::Head(Box::new(
                    export_runtime_sig_type(state, tail),
                ))),
            })
        }
        SigType::Fun {
            arg, ret_eff, ret, ..
        } => typed_ir::Type::Fun {
            param: Box::new(export_runtime_sig_type(state, arg)),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(export_runtime_sig_row(state, ret_eff.as_ref())),
            ret: Box::new(export_runtime_sig_type(state, ret)),
        },
    }
}

pub(crate) fn export_runtime_sig_row(state: &LowerState, row: Option<&SigRow>) -> typed_ir::Type {
    let Some(row) = row else {
        return typed_ir::Type::Never;
    };
    let tail = row
        .tail
        .as_ref()
        .map(|tail| typed_ir::Type::Var(typed_ir::TypeVar(tail.name.clone())))
        .unwrap_or(typed_ir::Type::Never);
    if row.items.is_empty() {
        return tail;
    }
    typed_ir::Type::Row {
        items: row
            .items
            .iter()
            .map(|item| export_runtime_sig_type(state, item))
            .collect(),
        tail: Box::new(tail),
    }
}

fn export_runtime_type_path(state: &LowerState, path: &Path) -> typed_ir::Path {
    export_runtime_path(&state.ctx.canonical_current_type_path(path))
}

pub(crate) fn export_runtime_path(path: &Path) -> typed_ir::Path {
    typed_ir::Path {
        segments: path
            .segments
            .iter()
            .map(|segment| typed_ir::Name(segment.0.clone()))
            .collect(),
    }
}
