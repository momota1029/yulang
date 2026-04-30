use super::*;

pub(super) fn runtime_export_scheme(
    state: &LowerState,
    receiver_sig: &SigType,
    expected_sig: &SigType,
) -> core_ir::Scheme {
    core_ir::Scheme {
        requirements: Vec::new(),
        body: core_ir::Type::Fun {
            param: Box::new(export_runtime_sig_type(state, receiver_sig)),
            param_effect: Box::new(core_ir::Type::Never),
            ret_effect: Box::new(core_ir::Type::Never),
            ret: Box::new(export_runtime_sig_type(state, expected_sig)),
        },
    }
}

pub(super) fn runtime_export_role_method_scheme(
    state: &LowerState,
    role_path: &Path,
    receiver_sig: &SigType,
    expected_sig: &SigType,
) -> core_ir::Scheme {
    let role_arg_infos = state.infer.role_arg_infos_of(role_path);
    let requirements = if role_arg_infos.is_empty() {
        Vec::new()
    } else {
        vec![core_ir::RoleRequirement {
            role: export_runtime_path(role_path),
            args: role_arg_infos
                .into_iter()
                .map(|info| {
                    let bounds = core_ir::TypeBounds::exact(core_ir::Type::Var(core_ir::TypeVar(
                        info.name.clone(),
                    )));
                    if info.is_input {
                        core_ir::RoleRequirementArg::Input(bounds)
                    } else {
                        core_ir::RoleRequirementArg::Associated {
                            name: core_ir::Name(info.name),
                            bounds,
                        }
                    }
                })
                .collect(),
        }]
    };
    core_ir::Scheme {
        requirements,
        body: core_ir::Type::Fun {
            param: Box::new(export_runtime_sig_type(state, receiver_sig)),
            param_effect: Box::new(core_ir::Type::Never),
            ret_effect: Box::new(core_ir::Type::Never),
            ret: Box::new(export_runtime_sig_type(state, expected_sig)),
        },
    }
}

pub(crate) fn export_runtime_sig_type(state: &LowerState, sig: &SigType) -> core_ir::Type {
    match sig {
        SigType::Prim { path, .. } => core_ir::Type::Named {
            path: export_runtime_type_path(state, path),
            args: Vec::new(),
        },
        SigType::Apply { path, args, .. } => core_ir::Type::Named {
            path: export_runtime_type_path(state, path),
            args: args
                .iter()
                .map(|arg| core_ir::TypeArg::Type(export_runtime_sig_type(state, arg)))
                .collect(),
        },
        SigType::Var(var) => core_ir::Type::Var(core_ir::TypeVar(var.name.clone())),
        SigType::Unit { .. } => core_ir::Type::Named {
            path: core_ir::Path::from_name(core_ir::Name("unit".to_string())),
            args: Vec::new(),
        },
        SigType::Tuple { items, .. } => core_ir::Type::Tuple(
            items
                .iter()
                .map(|item| export_runtime_sig_type(state, item))
                .collect(),
        ),
        SigType::Record { fields, .. } => core_ir::Type::Record(core_ir::RecordType {
            fields: fields
                .iter()
                .map(|field| core_ir::RecordField {
                    name: core_ir::Name(field.name.0.clone()),
                    value: export_runtime_sig_type(state, &field.ty),
                    optional: field.optional,
                })
                .collect(),
            spread: None,
        }),
        SigType::RecordTailSpread { fields, tail, .. } => {
            core_ir::Type::Record(core_ir::RecordType {
                fields: fields
                    .iter()
                    .map(|field| core_ir::RecordField {
                        name: core_ir::Name(field.name.0.clone()),
                        value: export_runtime_sig_type(state, &field.ty),
                        optional: field.optional,
                    })
                    .collect(),
                spread: Some(core_ir::RecordSpread::Tail(Box::new(
                    export_runtime_sig_type(state, tail),
                ))),
            })
        }
        SigType::RecordHeadSpread { tail, fields, .. } => {
            core_ir::Type::Record(core_ir::RecordType {
                fields: fields
                    .iter()
                    .map(|field| core_ir::RecordField {
                        name: core_ir::Name(field.name.0.clone()),
                        value: export_runtime_sig_type(state, &field.ty),
                        optional: field.optional,
                    })
                    .collect(),
                spread: Some(core_ir::RecordSpread::Head(Box::new(
                    export_runtime_sig_type(state, tail),
                ))),
            })
        }
        SigType::Fun {
            arg, ret_eff, ret, ..
        } => core_ir::Type::Fun {
            param: Box::new(export_runtime_sig_type(state, arg)),
            param_effect: Box::new(core_ir::Type::Never),
            ret_effect: Box::new(export_runtime_sig_row(state, ret_eff.as_ref())),
            ret: Box::new(export_runtime_sig_type(state, ret)),
        },
    }
}

pub(crate) fn export_runtime_sig_row(state: &LowerState, row: Option<&SigRow>) -> core_ir::Type {
    let Some(row) = row else {
        return core_ir::Type::Never;
    };
    let tail = row
        .tail
        .as_ref()
        .map(|tail| core_ir::Type::Var(core_ir::TypeVar(tail.name.clone())))
        .unwrap_or(core_ir::Type::Never);
    if row.items.is_empty() {
        return tail;
    }
    core_ir::Type::Row {
        items: row
            .items
            .iter()
            .map(|item| export_runtime_sig_type(state, item))
            .collect(),
        tail: Box::new(tail),
    }
}

fn export_runtime_type_path(state: &LowerState, path: &Path) -> core_ir::Path {
    export_runtime_path(&state.ctx.canonical_current_type_path(path))
}

pub(crate) fn export_runtime_path(path: &Path) -> core_ir::Path {
    core_ir::Path {
        segments: path
            .segments
            .iter()
            .map(|segment| core_ir::Name(segment.0.clone()))
            .collect(),
    }
}
