use super::*;

pub(crate) fn infer_type_substitutions(
    template: &core_ir::Type,
    actual: &core_ir::Type,
    params: &BTreeSet<core_ir::TypeVar>,
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
) {
    infer_type_substitutions_inner(template, actual, params, substitutions, 128, false, false);
}

pub(crate) fn infer_type_substitutions_with_effects(
    template: &core_ir::Type,
    actual: &core_ir::Type,
    params: &BTreeSet<core_ir::TypeVar>,
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
) {
    infer_type_substitutions_inner(template, actual, params, substitutions, 128, true, false);
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
    let evidence_substitutions = evidence
        .substitutions
        .into_iter()
        .map(|substitution| core_ir::TypeSubstitution {
            var: substitution.var,
            ty: substitute_type(&substitution.ty, substitutions),
        })
        .collect::<Vec<_>>();
    let substitution_candidates = evidence
        .substitution_candidates
        .into_iter()
        .map(|candidate| core_ir::PrincipalSubstitutionCandidate {
            var: candidate.var,
            relation: candidate.relation,
            ty: substitute_type(&candidate.ty, substitutions),
            source_edge: candidate.source_edge,
            path: candidate.path,
        })
        .collect::<Vec<_>>();
    let principal_elaboration = evidence.principal_elaboration.map(|plan| {
        substitute_principal_elaboration_plan(plan, substitutions, &substitution_candidates)
    });

    core_ir::ApplyEvidence {
        callee_source_edge: evidence.callee_source_edge,
        arg_source_edge: evidence.arg_source_edge,
        callee: substitute_bounds(evidence.callee, substitutions),
        expected_callee: evidence
            .expected_callee
            .map(|bounds| substitute_bounds(bounds, substitutions)),
        arg: substitute_bounds(evidence.arg, substitutions),
        expected_arg: evidence
            .expected_arg
            .map(|bounds| substitute_bounds(bounds, substitutions)),
        result: substitute_bounds(evidence.result, substitutions),
        principal_callee: evidence
            .principal_callee
            .map(|ty| substitute_type(&ty, substitutions)),
        substitutions: evidence_substitutions,
        substitution_candidates,
        role_method: evidence.role_method,
        principal_elaboration,
    }
}

fn substitute_principal_elaboration_plan(
    plan: core_ir::PrincipalElaborationPlan,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
    substitution_candidates: &[core_ir::PrincipalSubstitutionCandidate],
) -> core_ir::PrincipalElaborationPlan {
    let plan = core_ir::PrincipalElaborationPlan {
        target: plan.target,
        principal_callee: substitute_type(&plan.principal_callee, substitutions),
        substitutions: plan
            .substitutions
            .into_iter()
            .map(|substitution| core_ir::TypeSubstitution {
                var: substitution.var,
                ty: substitute_type(&substitution.ty, substitutions),
            })
            .collect(),
        args: plan
            .args
            .into_iter()
            .map(|arg| core_ir::PrincipalElaborationArg {
                index: arg.index,
                intrinsic: substitute_bounds(arg.intrinsic, substitutions),
                contextual: arg
                    .contextual
                    .map(|bounds| substitute_bounds(bounds, substitutions)),
                expected_runtime: arg
                    .expected_runtime
                    .map(|ty| substitute_type(&ty, substitutions)),
                source_edge: arg.source_edge,
            })
            .collect(),
        result: core_ir::PrincipalElaborationResult {
            intrinsic: substitute_bounds(plan.result.intrinsic, substitutions),
            contextual: plan
                .result
                .contextual
                .map(|bounds| substitute_bounds(bounds, substitutions)),
            expected_runtime: plan
                .result
                .expected_runtime
                .map(|ty| substitute_type(&ty, substitutions)),
        },
        adapters: plan
            .adapters
            .into_iter()
            .map(|adapter| core_ir::PrincipalAdapterHole {
                kind: adapter.kind,
                source_edge: adapter.source_edge,
                actual: substitute_type(&adapter.actual, substitutions),
                expected: substitute_type(&adapter.expected, substitutions),
            })
            .collect(),
        complete: plan.complete,
        incomplete_reasons: plan.incomplete_reasons,
    };
    normalize_principal_elaboration_plan(plan, substitution_candidates)
}

pub(crate) fn normalize_principal_elaboration_plan(
    plan: core_ir::PrincipalElaborationPlan,
    substitution_candidates: &[core_ir::PrincipalSubstitutionCandidate],
) -> core_ir::PrincipalElaborationPlan {
    let required_vars = principal_elaboration_required_vars(&plan);
    if required_vars.is_empty() {
        return rebuild_principal_elaboration_plan_status(
            plan,
            BTreeMap::new(),
            BTreeSet::new(),
            substitution_candidates,
        );
    }

    let mut substitutions = BTreeMap::new();
    let mut conflicts = BTreeSet::new();
    for substitution in &plan.substitutions {
        if !principal_plan_substitution_type_usable(&substitution.ty, false) {
            continue;
        }
        insert_exact_projected_substitution(
            &mut substitutions,
            &mut conflicts,
            substitution.var.clone(),
            substitution.ty.clone(),
        );
    }
    project_substitutions_from_candidates(
        substitution_candidates,
        &required_vars,
        &mut substitutions,
        &mut conflicts,
    );

    let substituted_principal = substitute_type(&plan.principal_callee, &substitutions);
    for arg in &plan.args {
        let Some(template) = principal_fun_param_at(&substituted_principal, arg.index) else {
            continue;
        };
        if let Some(actual) = principal_plan_arg_type(arg) {
            project_closed_substitutions_from_type(
                template,
                &actual,
                &required_vars,
                &mut substitutions,
                &mut conflicts,
                false,
                64,
            );
        }
    }

    if let Some(template) = principal_fun_result_after_args(&substituted_principal, plan.args.len())
        && let Some(actual) = principal_plan_result_type(&plan.result)
    {
        project_closed_substitutions_from_type(
            template,
            &actual,
            &required_vars,
            &mut substitutions,
            &mut conflicts,
            false,
            64,
        );
    }

    rebuild_principal_elaboration_plan_status(
        plan,
        substitutions,
        conflicts,
        substitution_candidates,
    )
}

fn rebuild_principal_elaboration_plan_status(
    mut plan: core_ir::PrincipalElaborationPlan,
    substitutions: BTreeMap<core_ir::TypeVar, core_ir::Type>,
    conflicts: BTreeSet<core_ir::TypeVar>,
    substitution_candidates: &[core_ir::PrincipalSubstitutionCandidate],
) -> core_ir::PrincipalElaborationPlan {
    let required_vars = principal_elaboration_required_vars(&plan);
    let mut incomplete_reasons = Vec::new();
    if plan.target.is_none() {
        incomplete_reasons.push(core_ir::PrincipalElaborationIncompleteReason::MissingTarget);
    }
    for var in &required_vars {
        if conflicts.contains(var) {
            incomplete_reasons.push(
                core_ir::PrincipalElaborationIncompleteReason::ConflictingSubstitution(var.clone()),
            );
        } else if !substitutions.contains_key(var) {
            let has_open_candidate = substitution_candidates
                .iter()
                .any(|candidate| candidate.var == *var)
                || plan.incomplete_reasons.iter().any(|reason| {
                    matches!(
                        reason,
                        core_ir::PrincipalElaborationIncompleteReason::OpenCandidate(candidate_var)
                            if candidate_var == var
                    )
                });
            if has_open_candidate {
                incomplete_reasons.push(
                    core_ir::PrincipalElaborationIncompleteReason::OpenCandidate(var.clone()),
                );
            } else {
                incomplete_reasons.push(
                    core_ir::PrincipalElaborationIncompleteReason::MissingSubstitution(var.clone()),
                );
            }
        }
    }
    for arg in &plan.args {
        if principal_plan_arg_type(arg).is_none() {
            incomplete_reasons.push(core_ir::PrincipalElaborationIncompleteReason::OpenArgType(
                arg.index,
            ));
        }
    }
    if principal_plan_result_type(&plan.result).is_none() {
        incomplete_reasons.push(core_ir::PrincipalElaborationIncompleteReason::OpenResultType);
    }

    plan.substitutions = substitutions
        .into_iter()
        .map(|(var, ty)| core_ir::TypeSubstitution { var, ty })
        .collect();
    plan.complete = incomplete_reasons.is_empty();
    plan.incomplete_reasons = incomplete_reasons;
    plan
}

fn principal_elaboration_required_vars(
    plan: &core_ir::PrincipalElaborationPlan,
) -> BTreeSet<core_ir::TypeVar> {
    let mut vars = BTreeSet::new();
    collect_type_vars(&plan.principal_callee, &mut vars);
    vars
}

fn principal_fun_param_at(ty: &core_ir::Type, index: usize) -> Option<&core_ir::Type> {
    let mut current = ty;
    for _ in 0..index {
        current = match current {
            core_ir::Type::Fun { ret, .. } => ret,
            core_ir::Type::Recursive { body, .. } => body,
            _ => return None,
        };
    }
    match current {
        core_ir::Type::Fun { param, .. } => Some(param),
        core_ir::Type::Recursive { body, .. } => principal_fun_param_at(body, 0),
        _ => None,
    }
}

fn principal_fun_result_after_args(ty: &core_ir::Type, arg_count: usize) -> Option<&core_ir::Type> {
    let mut current = ty;
    for _ in 0..arg_count {
        current = match current {
            core_ir::Type::Fun { ret, .. } => ret,
            core_ir::Type::Recursive { body, .. } => body,
            _ => return None,
        };
    }
    Some(current)
}

fn principal_plan_arg_type(arg: &core_ir::PrincipalElaborationArg) -> Option<core_ir::Type> {
    arg.expected_runtime
        .clone()
        .or_else(|| principal_plan_bounds_exact_type(arg.contextual.as_ref()))
        .or_else(|| principal_plan_bounds_exact_type(Some(&arg.intrinsic)))
}

fn principal_plan_result_type(
    result: &core_ir::PrincipalElaborationResult,
) -> Option<core_ir::Type> {
    result
        .expected_runtime
        .clone()
        .or_else(|| principal_plan_bounds_exact_type(result.contextual.as_ref()))
        .or_else(|| principal_plan_bounds_exact_type(Some(&result.intrinsic)))
}

fn principal_plan_bounds_exact_type(bounds: Option<&core_ir::TypeBounds>) -> Option<core_ir::Type> {
    let bounds = bounds?;
    match (bounds.lower.as_deref(), bounds.upper.as_deref()) {
        (Some(lower), Some(upper)) if lower == upper => Some(lower.clone()),
        _ => None,
    }
}

fn insert_exact_projected_substitution(
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
    conflicts: &mut BTreeSet<core_ir::TypeVar>,
    var: core_ir::TypeVar,
    ty: core_ir::Type,
) {
    if let Some(existing) = substitutions.get(&var) {
        if existing != &ty {
            conflicts.insert(var);
        }
    } else {
        substitutions.insert(var, ty);
    }
}

fn project_substitutions_from_candidates(
    candidates: &[core_ir::PrincipalSubstitutionCandidate],
    params: &BTreeSet<core_ir::TypeVar>,
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
    conflicts: &mut BTreeSet<core_ir::TypeVar>,
) {
    let mut by_var = BTreeMap::<
        core_ir::TypeVar,
        Vec<(core_ir::PrincipalCandidateRelation, core_ir::Type)>,
    >::new();
    for candidate in candidates {
        if !params.contains(&candidate.var)
            || !principal_plan_substitution_type_usable(&candidate.ty, false)
        {
            continue;
        }
        by_var
            .entry(candidate.var.clone())
            .or_default()
            .push((candidate.relation, candidate.ty.clone()));
    }

    for (var, candidates) in by_var {
        if substitutions.contains_key(&var) || conflicts.contains(&var) {
            continue;
        }
        let exact = unique_candidate_type(
            candidates
                .iter()
                .filter(|(relation, _)| {
                    matches!(relation, core_ir::PrincipalCandidateRelation::Exact)
                })
                .map(|(_, ty)| ty),
        );
        match exact {
            CandidateTypeChoice::One(ty) => {
                insert_exact_projected_substitution(substitutions, conflicts, var, ty);
                continue;
            }
            CandidateTypeChoice::Conflict => {
                conflicts.insert(var);
                continue;
            }
            CandidateTypeChoice::None => {}
        }

        let lower = unique_candidate_type(
            candidates
                .iter()
                .filter(|(relation, _)| {
                    matches!(relation, core_ir::PrincipalCandidateRelation::Lower)
                })
                .map(|(_, ty)| ty),
        );
        let upper = unique_candidate_type(
            candidates
                .iter()
                .filter(|(relation, _)| {
                    matches!(relation, core_ir::PrincipalCandidateRelation::Upper)
                })
                .map(|(_, ty)| ty),
        );
        if let (CandidateTypeChoice::One(lower), CandidateTypeChoice::One(upper)) = (lower, upper)
            && lower == upper
        {
            insert_exact_projected_substitution(substitutions, conflicts, var, lower);
        }
    }
}

enum CandidateTypeChoice {
    None,
    One(core_ir::Type),
    Conflict,
}

fn unique_candidate_type<'a>(
    candidates: impl Iterator<Item = &'a core_ir::Type>,
) -> CandidateTypeChoice {
    let mut choice: Option<core_ir::Type> = None;
    for candidate in candidates {
        match &choice {
            Some(existing) if existing != candidate => return CandidateTypeChoice::Conflict,
            Some(_) => {}
            None => choice = Some(candidate.clone()),
        }
    }
    choice.map_or(CandidateTypeChoice::None, CandidateTypeChoice::One)
}

fn project_closed_substitutions_from_type(
    template: &core_ir::Type,
    actual: &core_ir::Type,
    params: &BTreeSet<core_ir::TypeVar>,
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
    conflicts: &mut BTreeSet<core_ir::TypeVar>,
    allow_never: bool,
    depth: usize,
) {
    if depth == 0 {
        return;
    }
    match (template, actual) {
        (core_ir::Type::Var(var), actual) if params.contains(var) => {
            if principal_plan_substitution_type_usable(actual, allow_never) {
                insert_exact_projected_substitution(
                    substitutions,
                    conflicts,
                    var.clone(),
                    actual.clone(),
                );
            }
        }
        (
            core_ir::Type::Named { path, args },
            core_ir::Type::Named {
                path: actual_path,
                args: actual_args,
            },
        ) if path == actual_path && args.len() == actual_args.len() => {
            for (template_arg, actual_arg) in args.iter().zip(actual_args) {
                project_closed_substitutions_from_type_arg(
                    template_arg,
                    actual_arg,
                    params,
                    substitutions,
                    conflicts,
                    allow_never,
                    depth - 1,
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
            project_closed_substitutions_from_type(
                param,
                actual_param,
                params,
                substitutions,
                conflicts,
                false,
                depth - 1,
            );
            project_closed_substitutions_from_type(
                param_effect,
                actual_param_effect,
                params,
                substitutions,
                conflicts,
                true,
                depth - 1,
            );
            project_closed_substitutions_from_type(
                ret_effect,
                actual_ret_effect,
                params,
                substitutions,
                conflicts,
                true,
                depth - 1,
            );
            project_closed_substitutions_from_type(
                ret,
                actual_ret,
                params,
                substitutions,
                conflicts,
                false,
                depth - 1,
            );
        }
        (core_ir::Type::Tuple(items), core_ir::Type::Tuple(actual_items))
            if items.len() == actual_items.len() =>
        {
            for (item, actual_item) in items.iter().zip(actual_items) {
                project_closed_substitutions_from_type(
                    item,
                    actual_item,
                    params,
                    substitutions,
                    conflicts,
                    allow_never,
                    depth - 1,
                );
            }
        }
        (core_ir::Type::Record(record), core_ir::Type::Record(actual_record)) => {
            for field in &record.fields {
                let Some(actual_field) = actual_record
                    .fields
                    .iter()
                    .find(|actual| actual.name == field.name)
                else {
                    continue;
                };
                project_closed_substitutions_from_type(
                    &field.value,
                    &actual_field.value,
                    params,
                    substitutions,
                    conflicts,
                    allow_never,
                    depth - 1,
                );
            }
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
                if case.payloads.len() != actual_case.payloads.len() {
                    continue;
                }
                for (payload, actual_payload) in case.payloads.iter().zip(&actual_case.payloads) {
                    project_closed_substitutions_from_type(
                        payload,
                        actual_payload,
                        params,
                        substitutions,
                        conflicts,
                        allow_never,
                        depth - 1,
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
        ) if items.len() == actual_items.len() => {
            for (item, actual_item) in items.iter().zip(actual_items) {
                project_closed_substitutions_from_type(
                    item,
                    actual_item,
                    params,
                    substitutions,
                    conflicts,
                    true,
                    depth - 1,
                );
            }
            project_closed_substitutions_from_type(
                tail,
                actual_tail,
                params,
                substitutions,
                conflicts,
                true,
                depth - 1,
            );
        }
        (core_ir::Type::Recursive { body, .. }, actual) => {
            project_closed_substitutions_from_type(
                body,
                actual,
                params,
                substitutions,
                conflicts,
                allow_never,
                depth - 1,
            );
        }
        (template, core_ir::Type::Recursive { body, .. }) => {
            project_closed_substitutions_from_type(
                template,
                body,
                params,
                substitutions,
                conflicts,
                allow_never,
                depth - 1,
            );
        }
        _ => {}
    }
}

fn project_closed_substitutions_from_type_arg(
    template: &core_ir::TypeArg,
    actual: &core_ir::TypeArg,
    params: &BTreeSet<core_ir::TypeVar>,
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
    conflicts: &mut BTreeSet<core_ir::TypeVar>,
    allow_never: bool,
    depth: usize,
) {
    match (template, actual) {
        (core_ir::TypeArg::Type(template), core_ir::TypeArg::Type(actual)) => {
            project_closed_substitutions_from_type(
                template,
                actual,
                params,
                substitutions,
                conflicts,
                allow_never,
                depth,
            );
        }
        (core_ir::TypeArg::Type(template), core_ir::TypeArg::Bounds(actual)) => {
            if let Some(actual) = principal_plan_bounds_single_closed_type(actual, allow_never) {
                project_closed_substitutions_from_type(
                    template,
                    &actual,
                    params,
                    substitutions,
                    conflicts,
                    allow_never,
                    depth,
                );
            }
        }
        (core_ir::TypeArg::Bounds(template), core_ir::TypeArg::Type(actual)) => {
            if let Some(template) = principal_plan_bounds_single_closed_type(template, allow_never)
            {
                project_closed_substitutions_from_type(
                    &template,
                    actual,
                    params,
                    substitutions,
                    conflicts,
                    allow_never,
                    depth,
                );
            }
        }
        (core_ir::TypeArg::Bounds(template), core_ir::TypeArg::Bounds(actual)) => {
            if let (Some(template), Some(actual)) = (
                principal_plan_bounds_single_closed_type(template, allow_never),
                principal_plan_bounds_single_closed_type(actual, allow_never),
            ) {
                project_closed_substitutions_from_type(
                    &template,
                    &actual,
                    params,
                    substitutions,
                    conflicts,
                    allow_never,
                    depth,
                );
            }
        }
    }
}

fn principal_plan_bounds_single_closed_type(
    bounds: &core_ir::TypeBounds,
    allow_never: bool,
) -> Option<core_ir::Type> {
    let choice = match (bounds.lower.as_deref(), bounds.upper.as_deref()) {
        (Some(lower), Some(upper)) if lower == upper => Some(lower),
        (Some(ty), None) | (None, Some(ty)) => Some(ty),
        _ => None,
    }?;
    principal_plan_substitution_type_usable(choice, allow_never).then(|| choice.clone())
}

fn principal_plan_substitution_type_usable(ty: &core_ir::Type, allow_never: bool) -> bool {
    !matches!(ty, core_ir::Type::Any | core_ir::Type::Var(_))
        && (allow_never || !matches!(ty, core_ir::Type::Never))
        && !type_has_vars(ty)
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn plan_normalization_closes_child_var_after_parent_substitution() {
        let a = tv("a");
        let t = tv("t");
        let mut substitutions = BTreeMap::new();
        substitutions.insert(t.clone(), named("int"));

        let plan = list_plan_for_arg(list_of(core_ir::Type::Var(t)));
        let normalized = substitute_principal_elaboration_plan(plan, &substitutions, &[]);

        assert!(normalized.complete, "{:?}", normalized.incomplete_reasons);
        assert_eq!(
            normalized.substitutions,
            vec![core_ir::TypeSubstitution {
                var: a,
                ty: named("int"),
            }]
        );
    }

    #[test]
    fn plan_normalization_leaves_open_child_var_missing() {
        let plan = list_plan_for_arg(list_of(core_ir::Type::Var(tv("t"))));
        let normalized = substitute_principal_elaboration_plan(plan, &BTreeMap::new(), &[]);

        assert!(!normalized.complete);
        assert!(normalized.incomplete_reasons.contains(
            &core_ir::PrincipalElaborationIncompleteReason::MissingSubstitution(tv("a"))
        ));
    }

    #[test]
    fn plan_normalization_does_not_solve_union_actuals() {
        let plan = list_plan_for_arg(list_of(core_ir::Type::Union(vec![
            core_ir::Type::Var(tv("t")),
            named("int"),
        ])));
        let normalized = substitute_principal_elaboration_plan(plan, &BTreeMap::new(), &[]);

        assert!(!normalized.complete);
        assert!(normalized.incomplete_reasons.contains(
            &core_ir::PrincipalElaborationIncompleteReason::MissingSubstitution(tv("a"))
        ));
    }

    #[test]
    fn plan_normalization_closes_child_var_from_single_closed_type_arg_bound() {
        let plan = list_plan_for_arg(core_ir::Type::Named {
            path: core_ir::Path::from_name(core_ir::Name("list".to_string())),
            args: vec![core_ir::TypeArg::Bounds(core_ir::TypeBounds::upper(named(
                "int",
            )))],
        });
        let normalized = substitute_principal_elaboration_plan(plan, &BTreeMap::new(), &[]);

        assert!(normalized.complete, "{:?}", normalized.incomplete_reasons);
        assert_eq!(
            normalized.substitutions,
            vec![core_ir::TypeSubstitution {
                var: tv("a"),
                ty: named("int"),
            }]
        );
    }

    #[test]
    fn plan_normalization_does_not_project_conflicting_type_arg_bounds() {
        let plan = list_plan_for_arg(core_ir::Type::Named {
            path: core_ir::Path::from_name(core_ir::Name("list".to_string())),
            args: vec![core_ir::TypeArg::Bounds(core_ir::TypeBounds {
                lower: Some(Box::new(named("int"))),
                upper: Some(Box::new(named("bool"))),
            })],
        });
        let normalized = substitute_principal_elaboration_plan(plan, &BTreeMap::new(), &[]);

        assert!(!normalized.complete);
        assert!(normalized.incomplete_reasons.contains(
            &core_ir::PrincipalElaborationIncompleteReason::MissingSubstitution(tv("a"))
        ));
    }

    fn list_plan_for_arg(arg_ty: core_ir::Type) -> core_ir::PrincipalElaborationPlan {
        core_ir::PrincipalElaborationPlan {
            target: Some(core_ir::Path::from_name(core_ir::Name(
                "view_raw".to_string(),
            ))),
            principal_callee: core_ir::Type::Fun {
                param: Box::new(list_of(core_ir::Type::Var(tv("a")))),
                param_effect: Box::new(core_ir::Type::Never),
                ret_effect: Box::new(core_ir::Type::Never),
                ret: Box::new(named("unit")),
            },
            substitutions: Vec::new(),
            args: vec![core_ir::PrincipalElaborationArg {
                index: 0,
                intrinsic: core_ir::TypeBounds::exact(arg_ty),
                contextual: None,
                expected_runtime: None,
                source_edge: None,
            }],
            result: core_ir::PrincipalElaborationResult {
                intrinsic: core_ir::TypeBounds::exact(named("unit")),
                contextual: None,
                expected_runtime: None,
            },
            adapters: Vec::new(),
            complete: false,
            incomplete_reasons: vec![
                core_ir::PrincipalElaborationIncompleteReason::MissingSubstitution(tv("a")),
            ],
        }
    }

    fn list_of(item: core_ir::Type) -> core_ir::Type {
        core_ir::Type::Named {
            path: core_ir::Path::from_name(core_ir::Name("list".to_string())),
            args: vec![core_ir::TypeArg::Type(item)],
        }
    }

    fn named(name: &str) -> core_ir::Type {
        core_ir::Type::Named {
            path: core_ir::Path::from_name(core_ir::Name(name.to_string())),
            args: Vec::new(),
        }
    }

    fn tv(name: &str) -> core_ir::TypeVar {
        core_ir::TypeVar(name.to_string())
    }
}
