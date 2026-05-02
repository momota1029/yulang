use super::*;

pub(crate) fn infer_type_substitutions(
    template: &core_ir::Type,
    actual: &core_ir::Type,
    params: &BTreeSet<core_ir::TypeVar>,
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
) {
    infer_type_substitutions_inner(template, actual, params, substitutions, 128, false, false);
}

pub(crate) fn substitute_type(
    ty: &core_ir::Type,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> core_ir::Type {
    match ty {
        core_ir::Type::Never => core_ir::Type::Never,
        core_ir::Type::Any => core_ir::Type::Any,
        core_ir::Type::Var(var) => substitutions
            .get(var)
            .cloned()
            .unwrap_or_else(|| core_ir::Type::Var(var.clone())),
        core_ir::Type::Named { path, args } => core_ir::Type::Named {
            path: path.clone(),
            args: args
                .iter()
                .map(|arg| substitute_type_arg(arg, substitutions))
                .collect(),
        },
        core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => core_ir::Type::Fun {
            param: Box::new(substitute_type(param, substitutions)),
            param_effect: Box::new(substitute_type(param_effect, substitutions)),
            ret_effect: Box::new(substitute_type(ret_effect, substitutions)),
            ret: Box::new(substitute_type(ret, substitutions)),
        },
        core_ir::Type::Tuple(items) => core_ir::Type::Tuple(
            items
                .iter()
                .map(|item| substitute_type(item, substitutions))
                .collect(),
        ),
        core_ir::Type::Record(record) => core_ir::Type::Record(core_ir::RecordType {
            fields: record
                .fields
                .iter()
                .map(|field| core_ir::RecordField {
                    name: field.name.clone(),
                    value: substitute_type(&field.value, substitutions),
                    optional: field.optional,
                })
                .collect(),
            spread: record.spread.as_ref().map(|spread| match spread {
                core_ir::RecordSpread::Head(ty) => {
                    core_ir::RecordSpread::Head(Box::new(substitute_type(ty, substitutions)))
                }
                core_ir::RecordSpread::Tail(ty) => {
                    core_ir::RecordSpread::Tail(Box::new(substitute_type(ty, substitutions)))
                }
            }),
        }),
        core_ir::Type::Variant(variant) => core_ir::Type::Variant(core_ir::VariantType {
            cases: variant
                .cases
                .iter()
                .map(|case| core_ir::VariantCase {
                    name: case.name.clone(),
                    payloads: case
                        .payloads
                        .iter()
                        .map(|payload| substitute_type(payload, substitutions))
                        .collect(),
                })
                .collect(),
            tail: variant
                .tail
                .as_ref()
                .map(|tail| Box::new(substitute_type(tail, substitutions))),
        }),
        core_ir::Type::Row { items, tail } => core_ir::Type::Row {
            items: items
                .iter()
                .map(|item| substitute_type(item, substitutions))
                .collect(),
            tail: Box::new(substitute_type(tail, substitutions)),
        },
        core_ir::Type::Union(items) => core_ir::Type::Union(
            items
                .iter()
                .map(|item| substitute_type(item, substitutions))
                .collect(),
        ),
        core_ir::Type::Inter(items) => core_ir::Type::Inter(
            items
                .iter()
                .map(|item| substitute_type(item, substitutions))
                .collect(),
        ),
        core_ir::Type::Recursive { var, body } => {
            let mut substitutions = substitutions.clone();
            substitutions.remove(var);
            core_ir::Type::Recursive {
                var: var.clone(),
                body: Box::new(substitute_type(body, &substitutions)),
            }
        }
    }
}

pub(crate) fn substitute_hir_type(
    ty: &RuntimeType,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> RuntimeType {
    match ty {
        RuntimeType::Core(ty) => RuntimeType::core(substitute_type(ty, substitutions)),
        RuntimeType::Fun { param, ret } => RuntimeType::fun(
            substitute_hir_type(param, substitutions),
            substitute_hir_type(ret, substitutions),
        ),
        RuntimeType::Thunk { effect, value } => RuntimeType::thunk(
            substitute_type(effect, substitutions),
            substitute_hir_type(value, substitutions),
        ),
    }
}

pub(crate) fn substitute_scheme(
    scheme: core_ir::Scheme,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> core_ir::Scheme {
    core_ir::Scheme {
        requirements: scheme
            .requirements
            .into_iter()
            .map(|requirement| substitute_role_requirement(requirement, substitutions))
            .collect(),
        body: substitute_type(&scheme.body, substitutions),
    }
}

pub(crate) fn substitute_role_requirement(
    requirement: core_ir::RoleRequirement,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> core_ir::RoleRequirement {
    core_ir::RoleRequirement {
        role: requirement.role,
        args: requirement
            .args
            .into_iter()
            .map(|arg| match arg {
                core_ir::RoleRequirementArg::Input(bounds) => {
                    core_ir::RoleRequirementArg::Input(substitute_bounds(bounds, substitutions))
                }
                core_ir::RoleRequirementArg::Associated { name, bounds } => {
                    core_ir::RoleRequirementArg::Associated {
                        name,
                        bounds: substitute_bounds(bounds, substitutions),
                    }
                }
            })
            .collect(),
    }
}

pub(crate) fn substitute_apply_evidence(
    evidence: core_ir::ApplyEvidence,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> core_ir::ApplyEvidence {
    core_ir::ApplyEvidence {
        callee: substitute_bounds(evidence.callee, substitutions),
        arg: substitute_bounds(evidence.arg, substitutions),
        result: substitute_bounds(evidence.result, substitutions),
        principal_callee: evidence
            .principal_callee
            .map(|ty| substitute_type(&ty, substitutions)),
        substitutions: evidence
            .substitutions
            .into_iter()
            .map(|substitution| core_ir::TypeSubstitution {
                var: substitution.var,
                ty: substitute_type(&substitution.ty, substitutions),
            })
            .collect(),
        role_method: evidence.role_method,
    }
}

pub(crate) fn substitute_join_evidence(
    evidence: JoinEvidence,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> JoinEvidence {
    JoinEvidence {
        result: substitute_type(&evidence.result, substitutions),
    }
}

pub(crate) fn substitute_bounds(
    bounds: core_ir::TypeBounds,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> core_ir::TypeBounds {
    core_ir::TypeBounds {
        lower: bounds
            .lower
            .map(|lower| Box::new(substitute_type(&lower, substitutions))),
        upper: bounds
            .upper
            .map(|upper| Box::new(substitute_type(&upper, substitutions))),
    }
}

pub(super) fn infer_type_substitutions_inner(
    template: &core_ir::Type,
    actual: &core_ir::Type,
    params: &BTreeSet<core_ir::TypeVar>,
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
    depth: usize,
    include_function_effects: bool,
    prefer_non_never: bool,
) {
    if depth == 0 {
        return;
    }
    match (template, actual) {
        (core_ir::Type::Var(var), actual) if params.contains(var) => {
            insert_substitution(substitutions, var.clone(), actual.clone(), prefer_non_never);
        }
        (
            core_ir::Type::Named { path, args },
            core_ir::Type::Named {
                path: actual_path,
                args: actual_args,
            },
        ) if path == actual_path && args.len() == actual_args.len() => {
            for (template_arg, actual_arg) in args.iter().zip(actual_args) {
                infer_type_arg_substitutions(
                    template_arg,
                    actual_arg,
                    params,
                    substitutions,
                    depth - 1,
                    include_function_effects,
                    prefer_non_never,
                );
            }
        }
        (
            core_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            },
            core_ir::Type::Fun {
                param: actual_param,
                param_effect: actual_param_effect,
                ret_effect: actual_ret_effect,
                ret: actual_ret,
            },
        ) => {
            infer_type_substitutions_inner(
                param,
                actual_param,
                params,
                substitutions,
                depth - 1,
                include_function_effects,
                prefer_non_never,
            );
            if include_function_effects {
                infer_type_substitutions_inner(
                    param_effect,
                    actual_param_effect,
                    params,
                    substitutions,
                    depth - 1,
                    include_function_effects,
                    prefer_non_never,
                );
                infer_type_substitutions_inner(
                    ret_effect,
                    actual_ret_effect,
                    params,
                    substitutions,
                    depth - 1,
                    include_function_effects,
                    prefer_non_never,
                );
            }
            infer_type_substitutions_inner(
                ret,
                actual_ret,
                params,
                substitutions,
                depth - 1,
                include_function_effects,
                prefer_non_never,
            );
        }
        (core_ir::Type::Tuple(items), core_ir::Type::Tuple(actual_items))
            if items.len() == actual_items.len() =>
        {
            for (item, actual_item) in items.iter().zip(actual_items) {
                infer_type_substitutions_inner(
                    item,
                    actual_item,
                    params,
                    substitutions,
                    depth - 1,
                    include_function_effects,
                    prefer_non_never,
                );
            }
        }
        (core_ir::Type::Union(items) | core_ir::Type::Inter(items), actual) => {
            for item in items {
                infer_type_substitutions_inner(
                    item,
                    actual,
                    params,
                    substitutions,
                    depth - 1,
                    include_function_effects,
                    prefer_non_never,
                );
            }
        }
        (core_ir::Type::Record(record), core_ir::Type::Record(actual_record)) => {
            for field in &record.fields {
                if let Some(actual_field) = actual_record
                    .fields
                    .iter()
                    .find(|actual| actual.name == field.name)
                {
                    infer_type_substitutions_inner(
                        &field.value,
                        &actual_field.value,
                        params,
                        substitutions,
                        depth - 1,
                        include_function_effects,
                        prefer_non_never,
                    );
                }
            }
        }
        (
            core_ir::Type::Row { items, tail },
            core_ir::Type::Row {
                items: actual_items,
                tail: actual_tail,
            },
        ) => {
            infer_effect_row_substitutions(
                items,
                tail,
                actual_items,
                actual_tail,
                params,
                substitutions,
                depth - 1,
                include_function_effects,
                prefer_non_never,
            );
        }
        (core_ir::Type::Row { items, tail }, actual) => {
            infer_effect_row_substitutions(
                items,
                tail,
                std::slice::from_ref(actual),
                &core_ir::Type::Never,
                params,
                substitutions,
                depth - 1,
                include_function_effects,
                prefer_non_never,
            );
        }
        (core_ir::Type::Variant(variant), core_ir::Type::Variant(actual_variant)) => {
            for case in &variant.cases {
                let Some(actual_case) = actual_variant
                    .cases
                    .iter()
                    .find(|actual| actual.name == case.name)
                else {
                    continue;
                };
                if case.payloads.len() == actual_case.payloads.len() {
                    for (payload, actual_payload) in case.payloads.iter().zip(&actual_case.payloads)
                    {
                        infer_type_substitutions_inner(
                            payload,
                            actual_payload,
                            params,
                            substitutions,
                            depth - 1,
                            include_function_effects,
                            prefer_non_never,
                        );
                    }
                }
            }
        }
        (core_ir::Type::Recursive { body, .. }, actual) => {
            infer_type_substitutions_inner(
                body,
                actual,
                params,
                substitutions,
                depth - 1,
                include_function_effects,
                prefer_non_never,
            );
        }
        (template, core_ir::Type::Recursive { body, .. }) => {
            infer_type_substitutions_inner(
                template,
                body,
                params,
                substitutions,
                depth - 1,
                include_function_effects,
                prefer_non_never,
            );
        }
        _ => {}
    }
}

pub(super) fn infer_effect_row_substitutions(
    template_items: &[core_ir::Type],
    template_tail: &core_ir::Type,
    actual_items: &[core_ir::Type],
    actual_tail: &core_ir::Type,
    params: &BTreeSet<core_ir::TypeVar>,
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
    depth: usize,
    include_function_effects: bool,
    prefer_non_never: bool,
) {
    let mut matched_actual = vec![false; actual_items.len()];
    let mut row_vars = Vec::new();

    for template in template_items {
        match template {
            core_ir::Type::Var(var) if params.contains(var) => {
                row_vars.push(var.clone());
            }
            _ => {
                for (index, actual) in actual_items.iter().enumerate() {
                    if matched_actual[index] || !same_effect_head(template, actual) {
                        continue;
                    }
                    infer_type_substitutions_inner(
                        template,
                        actual,
                        params,
                        substitutions,
                        depth,
                        include_function_effects,
                        prefer_non_never,
                    );
                    matched_actual[index] = true;
                    break;
                }
            }
        }
    }

    let residual_items = actual_items
        .iter()
        .enumerate()
        .filter_map(|(index, item)| (!matched_actual[index]).then_some(item.clone()))
        .collect::<Vec<_>>();
    let residual = effect_row_from_items_and_tail(residual_items, actual_tail.clone());

    for var in row_vars {
        insert_substitution(substitutions, var, residual.clone(), prefer_non_never);
    }
    infer_type_substitutions_inner(
        template_tail,
        &residual,
        params,
        substitutions,
        depth,
        include_function_effects,
        prefer_non_never,
    );
}

pub(crate) fn same_effect_head(left: &core_ir::Type, right: &core_ir::Type) -> bool {
    match (left, right) {
        (
            core_ir::Type::Named { path, .. },
            core_ir::Type::Named {
                path: actual_path, ..
            },
        ) => path == actual_path,
        _ => false,
    }
}

pub(super) fn effect_row_from_items_and_tail(
    items: Vec<core_ir::Type>,
    tail: core_ir::Type,
) -> core_ir::Type {
    if items.is_empty() {
        return tail;
    }
    if effect_is_empty(&tail) && items.len() == 1 {
        return items.into_iter().next().unwrap();
    }
    core_ir::Type::Row {
        items,
        tail: Box::new(tail),
    }
}

pub(super) fn infer_type_arg_substitutions(
    template: &core_ir::TypeArg,
    actual: &core_ir::TypeArg,
    params: &BTreeSet<core_ir::TypeVar>,
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
    depth: usize,
    include_function_effects: bool,
    prefer_non_never: bool,
) {
    match (template, actual) {
        (core_ir::TypeArg::Type(template), core_ir::TypeArg::Type(actual)) => {
            infer_type_substitutions_inner(
                template,
                actual,
                params,
                substitutions,
                depth,
                include_function_effects,
                prefer_non_never,
            );
        }
        (core_ir::TypeArg::Type(template), core_ir::TypeArg::Bounds(actual)) => {
            if let Some(actual) = tir_evidence_bound(actual) {
                infer_type_substitutions_inner(
                    template,
                    &actual,
                    params,
                    substitutions,
                    depth,
                    include_function_effects,
                    prefer_non_never,
                );
            }
        }
        (core_ir::TypeArg::Bounds(template), core_ir::TypeArg::Type(actual)) => {
            if let Some(template) = tir_evidence_bound(template) {
                infer_type_substitutions_inner(
                    &template,
                    actual,
                    params,
                    substitutions,
                    depth,
                    include_function_effects,
                    prefer_non_never,
                );
            }
        }
        (core_ir::TypeArg::Bounds(template), core_ir::TypeArg::Bounds(actual)) => {
            if let (Some(template), Some(actual)) =
                (tir_evidence_bound(template), tir_evidence_bound(actual))
            {
                infer_type_substitutions_inner(
                    &template,
                    &actual,
                    params,
                    substitutions,
                    depth,
                    include_function_effects,
                    prefer_non_never,
                );
            }
        }
    }
}

pub(super) fn insert_substitution(
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
    var: core_ir::TypeVar,
    ty: core_ir::Type,
    prefer_non_never: bool,
) {
    if matches!(ty, core_ir::Type::Any) {
        return;
    }
    if matches!(&ty, core_ir::Type::Var(actual) if actual == &var) || type_contains_var(&ty, &var) {
        return;
    }
    match substitutions.get(&var).cloned() {
        Some(existing) if prefer_non_never => {
            substitutions.insert(
                var,
                choose_core_type(existing, ty, TypeChoice::Substitution),
            );
        }
        Some(existing) if type_has_vars(&existing) && !type_has_vars(&ty) => {
            substitutions.insert(var, ty);
        }
        Some(existing) if !type_has_vars(&existing) && type_has_vars(&ty) => {
            substitutions.insert(var, existing);
        }
        Some(existing) if type_compatible(&existing, &ty) => {
            substitutions.insert(
                var,
                choose_core_type(existing, ty, TypeChoice::Substitution),
            );
        }
        Some(_) => {}
        None => {
            substitutions.insert(var, ty);
        }
    }
}

pub(super) fn type_has_vars(ty: &core_ir::Type) -> bool {
    let mut vars = BTreeSet::new();
    collect_type_vars(ty, &mut vars);
    !vars.is_empty()
}

pub(super) fn type_contains_var(ty: &core_ir::Type, var: &core_ir::TypeVar) -> bool {
    let mut vars = BTreeSet::new();
    collect_type_vars(ty, &mut vars);
    vars.contains(var)
}

pub(super) fn tir_evidence_bound(bounds: &core_ir::TypeBounds) -> Option<core_ir::Type> {
    choose_bounds_type(bounds, BoundsChoice::TirEvidence)
}

pub(super) fn substitute_type_arg(
    arg: &core_ir::TypeArg,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> core_ir::TypeArg {
    match arg {
        core_ir::TypeArg::Type(ty) => core_ir::TypeArg::Type(substitute_type(ty, substitutions)),
        core_ir::TypeArg::Bounds(bounds) => core_ir::TypeArg::Bounds(core_ir::TypeBounds {
            lower: bounds
                .lower
                .as_ref()
                .map(|ty| Box::new(substitute_type(ty, substitutions))),
            upper: bounds
                .upper
                .as_ref()
                .map(|ty| Box::new(substitute_type(ty, substitutions))),
        }),
    }
}
