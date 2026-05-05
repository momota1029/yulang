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
        core_ir::Type::Unknown => core_ir::Type::Unknown,
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
        RuntimeType::Unknown => RuntimeType::unknown(),
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
    let mut evidence_vars = BTreeSet::new();
    if let Some(principal) = &evidence.principal_callee {
        collect_type_vars(principal, &mut evidence_vars);
    }
    let mut evidence_substitutions = substitutions
        .iter()
        .filter_map(|(var, ty)| {
            evidence_vars
                .contains(var)
                .then(|| core_ir::TypeSubstitution {
                    var: var.clone(),
                    ty: substitute_type(ty, substitutions),
                })
        })
        .collect::<Vec<_>>();
    for substitution in evidence.substitutions {
        if evidence_substitutions
            .iter()
            .any(|existing| existing.var == substitution.var)
        {
            continue;
        }
        evidence_substitutions.push(core_ir::TypeSubstitution {
            var: substitution.var,
            ty: substitute_type(&substitution.ty, substitutions),
        });
    }
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
    let plan = substitute_principal_elaboration_plan_slots(plan, substitutions);
    normalize_principal_elaboration_plan(plan, substitution_candidates)
}

fn substitute_principal_elaboration_plan_slots(
    plan: core_ir::PrincipalElaborationPlan,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> core_ir::PrincipalElaborationPlan {
    let mut plan_vars = BTreeSet::new();
    collect_type_vars(&plan.principal_callee, &mut plan_vars);
    let mut plan_substitutions = substitutions
        .iter()
        .filter_map(|(var, ty)| {
            plan_vars.contains(var).then(|| core_ir::TypeSubstitution {
                var: var.clone(),
                ty: substitute_type(ty, substitutions),
            })
        })
        .collect::<Vec<_>>();
    for substitution in plan.substitutions {
        if plan_substitutions
            .iter()
            .any(|existing| existing.var == substitution.var)
        {
            continue;
        }
        plan_substitutions.push(core_ir::TypeSubstitution {
            var: substitution.var,
            ty: substitute_type(&substitution.ty, substitutions),
        });
    }

    core_ir::PrincipalElaborationPlan {
        target: plan.target,
        principal_callee: substitute_type(&plan.principal_callee, substitutions),
        substitutions: plan_substitutions,
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
    }
}

pub(crate) fn normalize_principal_elaboration_plan(
    plan: core_ir::PrincipalElaborationPlan,
    substitution_candidates: &[core_ir::PrincipalSubstitutionCandidate],
) -> core_ir::PrincipalElaborationPlan {
    normalize_principal_elaboration_plan_with_requirements(plan, substitution_candidates, &[])
}

pub(crate) fn normalize_principal_elaboration_plan_with_requirements(
    plan: core_ir::PrincipalElaborationPlan,
    substitution_candidates: &[core_ir::PrincipalSubstitutionCandidate],
    requirements: &[core_ir::RoleRequirement],
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

    let never_usable_vars = principal_elaboration_never_usable_vars(&plan);
    let mut substitutions = BTreeMap::new();
    let mut conflicts = BTreeSet::new();
    for substitution in &plan.substitutions {
        let allow_never = never_usable_vars.contains(&substitution.var);
        if !principal_plan_substitution_type_usable(&substitution.ty, allow_never) {
            continue;
        }
        insert_exact_projected_substitution(
            &mut substitutions,
            &mut conflicts,
            substitution.var.clone(),
            substitution.ty.clone(),
        );
    }
    for _ in 0..4 {
        let before = (substitutions.len(), conflicts.len());
        project_substitutions_from_candidates(
            substitution_candidates,
            &required_vars,
            &mut substitutions,
            &mut conflicts,
        );
        project_substitutions_from_role_requirements(
            requirements,
            &required_vars,
            &mut substitutions,
            &mut conflicts,
        );
        if before == (substitutions.len(), conflicts.len()) {
            break;
        }
    }

    let substituted_principal = substitute_type(&plan.principal_callee, &substitutions);
    for arg in &plan.args {
        let Some(template) = principal_fun_param_at(&substituted_principal, arg.index) else {
            continue;
        };
        if let Some(actual) =
            principal_plan_arg_type(arg).map(|ty| substitute_type(&ty, &substitutions))
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
    }

    if let Some(template) = principal_fun_result_after_args(&substituted_principal, plan.args.len())
        && let Some(actual) =
            principal_plan_result_type(&plan.result).map(|ty| substitute_type(&ty, &substitutions))
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
    if let Some(core_ir::Type::Var(var)) =
        principal_fun_result_after_args(&substituted_principal, plan.args.len())
        && required_vars.contains(var)
        && !substitutions.contains_key(var)
        && let Some(actual) =
            principal_plan_result_self_closed_type(&plan.result, var, &substitutions)
    {
        insert_exact_projected_substitution(
            &mut substitutions,
            &mut conflicts,
            var.clone(),
            actual,
        );
    }
    for var in &required_vars {
        if substitutions.contains_key(var) || conflicts.contains(var) {
            continue;
        }
        if let Some(actual) =
            principal_plan_result_self_closed_type(&plan.result, var, &substitutions)
        {
            insert_exact_projected_substitution(
                &mut substitutions,
                &mut conflicts,
                var.clone(),
                actual,
            );
        }
    }

    rebuild_principal_elaboration_plan_status(
        plan,
        substitutions,
        conflicts,
        substitution_candidates,
    )
}

fn principal_plan_result_self_closed_type(
    result: &core_ir::PrincipalElaborationResult,
    var: &core_ir::TypeVar,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> Option<core_ir::Type> {
    result
        .contextual
        .as_ref()
        .and_then(|bounds| principal_plan_bounds_self_closed_type(bounds, var, substitutions))
        .or_else(|| principal_plan_bounds_self_closed_type(&result.intrinsic, var, substitutions))
}

fn principal_plan_bounds_self_closed_type(
    bounds: &core_ir::TypeBounds,
    var: &core_ir::TypeVar,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> Option<core_ir::Type> {
    let lower = bounds
        .lower
        .as_deref()
        .map(|ty| substitute_type(ty, substitutions))
        .and_then(|ty| self_or_closed_candidate_type(var, &ty));
    let upper = bounds
        .upper
        .as_deref()
        .map(|ty| substitute_type(ty, substitutions))
        .and_then(|ty| self_or_closed_candidate_type(var, &ty));
    match (lower, upper) {
        (Some(lower), Some(upper)) if lower == upper => Some(lower),
        (Some(ty), None) | (None, Some(ty)) => Some(ty),
        _ => None,
    }
}

fn rebuild_principal_elaboration_plan_status(
    mut plan: core_ir::PrincipalElaborationPlan,
    substitutions: BTreeMap<core_ir::TypeVar, core_ir::Type>,
    conflicts: BTreeSet<core_ir::TypeVar>,
    substitution_candidates: &[core_ir::PrincipalSubstitutionCandidate],
) -> core_ir::PrincipalElaborationPlan {
    if !substitutions.is_empty() {
        let non_conflicting_substitutions = substitutions
            .iter()
            .filter_map(|(var, ty)| (!conflicts.contains(var)).then_some((var.clone(), ty.clone())))
            .collect::<BTreeMap<_, _>>();
        plan = substitute_principal_elaboration_plan_slots(plan, &non_conflicting_substitutions);
    }
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
    incomplete_reasons.extend(
        plan.incomplete_reasons
            .iter()
            .filter_map(|reason| match reason {
                core_ir::PrincipalElaborationIncompleteReason::MissingAdapterHole(kind) => {
                    Some(core_ir::PrincipalElaborationIncompleteReason::MissingAdapterHole(*kind))
                }
                core_ir::PrincipalElaborationIncompleteReason::HandlerBoundaryWithoutPlan => {
                    Some(core_ir::PrincipalElaborationIncompleteReason::HandlerBoundaryWithoutPlan)
                }
                _ => None,
            }),
    );

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

fn principal_elaboration_never_usable_vars(
    plan: &core_ir::PrincipalElaborationPlan,
) -> BTreeSet<core_ir::TypeVar> {
    let mut usage = BTreeMap::<core_ir::TypeVar, PrincipalVarUsage>::new();
    collect_principal_var_usage(&plan.principal_callee, false, &mut usage);
    usage
        .into_iter()
        .filter_map(|(var, usage)| usage.never_usable().then_some(var))
        .collect()
}

#[derive(Default)]
struct PrincipalVarUsage {
    value: bool,
    effect: bool,
    type_arg: bool,
}

impl PrincipalVarUsage {
    fn mark_value(&mut self) {
        self.value = true;
    }

    fn mark_effect(&mut self) {
        self.effect = true;
    }

    fn mark_type_arg(&mut self) {
        self.type_arg = true;
    }

    fn never_usable(&self) -> bool {
        self.effect && !self.value
    }
}

fn collect_principal_var_usage(
    ty: &core_ir::Type,
    effect_slot: bool,
    usage: &mut BTreeMap<core_ir::TypeVar, PrincipalVarUsage>,
) {
    match ty {
        core_ir::Type::Var(var) => {
            let usage = usage.entry(var.clone()).or_default();
            if effect_slot {
                usage.mark_effect();
            } else {
                usage.mark_value();
            }
        }
        core_ir::Type::Named { args, .. } => {
            for arg in args {
                collect_principal_type_arg_usage(arg, usage);
            }
        }
        core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            collect_principal_var_usage(param, false, usage);
            collect_principal_var_usage(param_effect, true, usage);
            collect_principal_var_usage(ret_effect, true, usage);
            collect_principal_var_usage(ret, false, usage);
        }
        core_ir::Type::Tuple(items) | core_ir::Type::Union(items) | core_ir::Type::Inter(items) => {
            for item in items {
                collect_principal_var_usage(item, effect_slot, usage);
            }
        }
        core_ir::Type::Record(record) => {
            for field in &record.fields {
                collect_principal_var_usage(&field.value, false, usage);
            }
            if let Some(spread) = &record.spread {
                match spread {
                    core_ir::RecordSpread::Head(ty) | core_ir::RecordSpread::Tail(ty) => {
                        collect_principal_var_usage(ty, false, usage);
                    }
                }
            }
        }
        core_ir::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_principal_var_usage(payload, false, usage);
                }
            }
            if let Some(tail) = &variant.tail {
                collect_principal_var_usage(tail, false, usage);
            }
        }
        core_ir::Type::Row { items, tail } => {
            for item in items {
                match item {
                    core_ir::Type::Var(var) => {
                        usage.entry(var.clone()).or_default().mark_effect();
                    }
                    core_ir::Type::Named { args, .. } => {
                        for arg in args {
                            collect_principal_type_arg_usage(arg, usage);
                        }
                    }
                    other => collect_principal_var_usage(other, true, usage),
                }
            }
            collect_principal_var_usage(tail, true, usage);
        }
        core_ir::Type::Recursive { var, body } => {
            collect_principal_var_usage(body, effect_slot, usage);
            usage.remove(var);
        }
        core_ir::Type::Unknown | core_ir::Type::Never | core_ir::Type::Any => {}
    }
}

fn collect_principal_type_arg_usage(
    arg: &core_ir::TypeArg,
    usage: &mut BTreeMap<core_ir::TypeVar, PrincipalVarUsage>,
) {
    match arg {
        core_ir::TypeArg::Type(ty) => collect_principal_type_arg_type_usage(ty, usage),
        core_ir::TypeArg::Bounds(bounds) => {
            if let Some(lower) = bounds.lower.as_deref() {
                collect_principal_type_arg_type_usage(lower, usage);
            }
            if let Some(upper) = bounds.upper.as_deref() {
                collect_principal_type_arg_type_usage(upper, usage);
            }
        }
    }
}

fn collect_principal_type_arg_type_usage(
    ty: &core_ir::Type,
    usage: &mut BTreeMap<core_ir::TypeVar, PrincipalVarUsage>,
) {
    match ty {
        core_ir::Type::Var(var) => {
            usage.entry(var.clone()).or_default().mark_type_arg();
        }
        core_ir::Type::Named { args, .. } => {
            for arg in args {
                collect_principal_type_arg_usage(arg, usage);
            }
        }
        core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            collect_principal_var_usage(param, false, usage);
            collect_principal_var_usage(param_effect, true, usage);
            collect_principal_var_usage(ret_effect, true, usage);
            collect_principal_var_usage(ret, false, usage);
        }
        core_ir::Type::Tuple(items) | core_ir::Type::Union(items) | core_ir::Type::Inter(items) => {
            for item in items {
                collect_principal_type_arg_type_usage(item, usage);
            }
        }
        core_ir::Type::Record(record) => {
            for field in &record.fields {
                collect_principal_var_usage(&field.value, false, usage);
            }
            if let Some(spread) = &record.spread {
                match spread {
                    core_ir::RecordSpread::Head(ty) | core_ir::RecordSpread::Tail(ty) => {
                        collect_principal_var_usage(ty, false, usage);
                    }
                }
            }
        }
        core_ir::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_principal_var_usage(payload, false, usage);
                }
            }
            if let Some(tail) = &variant.tail {
                collect_principal_var_usage(tail, false, usage);
            }
        }
        core_ir::Type::Row { items, tail } => {
            for item in items {
                collect_principal_var_usage(item, true, usage);
            }
            collect_principal_var_usage(tail, true, usage);
        }
        core_ir::Type::Recursive { var, body } => {
            collect_principal_type_arg_type_usage(body, usage);
            usage.remove(var);
        }
        core_ir::Type::Unknown | core_ir::Type::Never | core_ir::Type::Any => {}
    }
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
        .or_else(|| principal_plan_bounds_slot_type(arg.contextual.as_ref(), false))
        .or_else(|| principal_plan_bounds_slot_type(Some(&arg.intrinsic), false))
}

fn principal_plan_result_type(
    result: &core_ir::PrincipalElaborationResult,
) -> Option<core_ir::Type> {
    result
        .expected_runtime
        .clone()
        .or_else(|| principal_plan_bounds_slot_type(result.contextual.as_ref(), true))
        .or_else(|| principal_plan_bounds_slot_type(Some(&result.intrinsic), true))
}

fn principal_plan_bounds_slot_type(
    bounds: Option<&core_ir::TypeBounds>,
    allow_never: bool,
) -> Option<core_ir::Type> {
    let bounds = bounds?;
    let lower = bounds
        .lower
        .as_deref()
        .cloned()
        .map(normalize_projected_closed_choice_type);
    let upper = bounds
        .upper
        .as_deref()
        .cloned()
        .map(normalize_projected_closed_choice_type);
    match (lower, upper) {
        (Some(lower), Some(upper)) if lower == upper => {
            principal_plan_slot_type_usable(&lower, allow_never).then_some(lower)
        }
        (Some(ty), None) | (None, Some(ty)) => {
            principal_plan_slot_type_usable(&ty, allow_never).then_some(ty)
        }
        _ => None,
    }
}

fn principal_plan_slot_type_usable(ty: &core_ir::Type, allow_never: bool) -> bool {
    !matches!(ty, core_ir::Type::Var(_))
        && (allow_never || !matches!(ty, core_ir::Type::Never))
        && !type_has_vars(ty)
}

fn insert_exact_projected_substitution(
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
    conflicts: &mut BTreeSet<core_ir::TypeVar>,
    var: core_ir::TypeVar,
    ty: core_ir::Type,
) {
    if type_has_any(&ty) {
        return;
    }
    if let Some(existing) = substitutions.get(&var) {
        if existing == &core_ir::Type::Never && ty != core_ir::Type::Never {
            substitutions.insert(var, ty);
        } else if ty == core_ir::Type::Never {
            // `Never` is the empty effect when it appears in effect positions.
            // Keep a more informative closed effect if one has already been
            // projected. Value positions do not insert `Never` here.
        } else if existing == &core_ir::Type::Any && ty != core_ir::Type::Any {
            substitutions.insert(var, ty);
        } else if ty == core_ir::Type::Any {
            // `Any` is a real top type, but a concrete projection is more useful
            // for a specialization key when both are observed for the same slot.
        } else if let Some(merged) = merge_projected_type_precision(existing, &ty) {
            substitutions.insert(var, merged);
        } else if let Some(merged) = merge_projected_effect_rows(existing, &ty) {
            substitutions.insert(var, merged);
        } else if existing != &ty {
            conflicts.insert(var);
        }
    } else {
        substitutions.insert(var, ty);
    }
}

fn merge_projected_type_precision(
    existing: &core_ir::Type,
    incoming: &core_ir::Type,
) -> Option<core_ir::Type> {
    if existing == incoming {
        return Some(existing.clone());
    }
    match (existing, incoming) {
        (core_ir::Type::Unknown, incoming) => Some(incoming.clone()),
        (existing, core_ir::Type::Unknown) => Some(existing.clone()),
        (core_ir::Type::Any, incoming) => Some(incoming.clone()),
        (existing, core_ir::Type::Any) => Some(existing.clone()),
        (
            core_ir::Type::Named {
                path: existing_path,
                args: existing_args,
            },
            core_ir::Type::Named {
                path: incoming_path,
                args: incoming_args,
            },
        ) if existing_path == incoming_path && existing_args.len() == incoming_args.len() => {
            let args = existing_args
                .iter()
                .zip(incoming_args)
                .map(|(existing, incoming)| merge_projected_type_arg_precision(existing, incoming))
                .collect::<Option<Vec<_>>>()?;
            Some(core_ir::Type::Named {
                path: existing_path.clone(),
                args,
            })
        }
        (existing, core_ir::Type::Union(incoming_items))
            if incoming_items
                .iter()
                .any(|item| merge_projected_type_precision(existing, item).is_some()) =>
        {
            Some(existing.clone())
        }
        (core_ir::Type::Union(existing_items), incoming)
            if existing_items
                .iter()
                .any(|item| merge_projected_type_precision(item, incoming).is_some()) =>
        {
            Some(incoming.clone())
        }
        (existing, core_ir::Type::Inter(incoming_items))
            if incoming_items
                .iter()
                .any(|item| merge_projected_type_precision(existing, item).is_some()) =>
        {
            Some(existing.clone())
        }
        (core_ir::Type::Inter(existing_items), incoming)
            if existing_items
                .iter()
                .any(|item| merge_projected_type_precision(item, incoming).is_some()) =>
        {
            Some(incoming.clone())
        }
        (core_ir::Type::Tuple(existing_items), core_ir::Type::Tuple(incoming_items))
            if existing_items.len() == incoming_items.len() =>
        {
            let items = existing_items
                .iter()
                .zip(incoming_items)
                .map(|(existing, incoming)| merge_projected_type_precision(existing, incoming))
                .collect::<Option<Vec<_>>>()?;
            Some(core_ir::Type::Tuple(items))
        }
        (
            core_ir::Type::Fun {
                param: existing_param,
                param_effect: existing_param_effect,
                ret_effect: existing_ret_effect,
                ret: existing_ret,
            },
            core_ir::Type::Fun {
                param: incoming_param,
                param_effect: incoming_param_effect,
                ret_effect: incoming_ret_effect,
                ret: incoming_ret,
            },
        ) => Some(core_ir::Type::Fun {
            param: Box::new(merge_projected_type_precision(
                existing_param,
                incoming_param,
            )?),
            param_effect: Box::new(merge_projected_type_precision(
                existing_param_effect,
                incoming_param_effect,
            )?),
            ret_effect: Box::new(merge_projected_type_precision(
                existing_ret_effect,
                incoming_ret_effect,
            )?),
            ret: Box::new(merge_projected_type_precision(existing_ret, incoming_ret)?),
        }),
        _ => None,
    }
}

fn merge_projected_type_arg_precision(
    existing: &core_ir::TypeArg,
    incoming: &core_ir::TypeArg,
) -> Option<core_ir::TypeArg> {
    match (existing, incoming) {
        (core_ir::TypeArg::Type(existing), core_ir::TypeArg::Type(incoming)) => Some(
            core_ir::TypeArg::Type(merge_projected_type_precision(existing, incoming)?),
        ),
        (core_ir::TypeArg::Bounds(existing), core_ir::TypeArg::Bounds(incoming)) => Some(
            core_ir::TypeArg::Bounds(merge_projected_bounds_precision(existing, incoming)?),
        ),
        (core_ir::TypeArg::Bounds(existing), core_ir::TypeArg::Type(incoming))
        | (core_ir::TypeArg::Type(incoming), core_ir::TypeArg::Bounds(existing)) => {
            let existing = principal_plan_bounds_single_closed_type(existing, false)?;
            Some(core_ir::TypeArg::Type(merge_projected_type_precision(
                &existing, incoming,
            )?))
        }
    }
}

fn merge_projected_bounds_precision(
    existing: &core_ir::TypeBounds,
    incoming: &core_ir::TypeBounds,
) -> Option<core_ir::TypeBounds> {
    let lower = match (existing.lower.as_deref(), incoming.lower.as_deref()) {
        (Some(existing), Some(incoming)) => Some(Box::new(merge_projected_type_precision(
            existing, incoming,
        )?)),
        (Some(existing), None) => Some(Box::new(existing.clone())),
        (None, Some(incoming)) => Some(Box::new(incoming.clone())),
        (None, None) => None,
    };
    let upper = match (existing.upper.as_deref(), incoming.upper.as_deref()) {
        (Some(existing), Some(incoming)) => Some(Box::new(merge_projected_type_precision(
            existing, incoming,
        )?)),
        (Some(existing), None) => Some(Box::new(existing.clone())),
        (None, Some(incoming)) => Some(Box::new(incoming.clone())),
        (None, None) => None,
    };
    Some(core_ir::TypeBounds { lower, upper })
}

fn normalize_projected_substitution_type(
    ty: &core_ir::Type,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> core_ir::Type {
    normalize_projected_runtime_shape(collapse_repeated_top_choice_type(substitute_type(
        ty,
        substitutions,
    )))
}

fn normalize_projected_runtime_shape(ty: core_ir::Type) -> core_ir::Type {
    match ty {
        core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => core_ir::Type::Fun {
            param: Box::new(normalize_projected_runtime_shape(*param)),
            param_effect: Box::new(normalize_projected_effect_shape(*param_effect)),
            ret_effect: Box::new(normalize_projected_effect_shape(*ret_effect)),
            ret: Box::new(normalize_projected_runtime_shape(*ret)),
        },
        core_ir::Type::Named { path, args } => core_ir::Type::Named {
            path,
            args: args
                .into_iter()
                .map(normalize_projected_runtime_shape_arg)
                .collect(),
        },
        core_ir::Type::Tuple(items) => core_ir::Type::Tuple(
            items
                .into_iter()
                .map(normalize_projected_runtime_shape)
                .collect(),
        ),
        core_ir::Type::Record(record) => core_ir::Type::Record(core_ir::RecordType {
            fields: record
                .fields
                .into_iter()
                .map(|field| core_ir::RecordField {
                    name: field.name,
                    value: normalize_projected_runtime_shape(field.value),
                    optional: field.optional,
                })
                .collect(),
            spread: record.spread.map(|spread| match spread {
                core_ir::RecordSpread::Head(ty) => {
                    core_ir::RecordSpread::Head(Box::new(normalize_projected_runtime_shape(*ty)))
                }
                core_ir::RecordSpread::Tail(ty) => {
                    core_ir::RecordSpread::Tail(Box::new(normalize_projected_runtime_shape(*ty)))
                }
            }),
        }),
        core_ir::Type::Variant(variant) => core_ir::Type::Variant(core_ir::VariantType {
            cases: variant
                .cases
                .into_iter()
                .map(|case| core_ir::VariantCase {
                    name: case.name,
                    payloads: case
                        .payloads
                        .into_iter()
                        .map(normalize_projected_runtime_shape)
                        .collect(),
                })
                .collect(),
            tail: variant
                .tail
                .map(|tail| Box::new(normalize_projected_runtime_shape(*tail))),
        }),
        core_ir::Type::Union(items) => core_ir::Type::Union(
            items
                .into_iter()
                .map(normalize_projected_runtime_shape)
                .collect(),
        ),
        core_ir::Type::Inter(items) => core_ir::Type::Inter(
            items
                .into_iter()
                .map(normalize_projected_runtime_shape)
                .collect(),
        ),
        core_ir::Type::Row { items, tail } => normalize_projected_effect_row_shape(items, *tail),
        core_ir::Type::Recursive { var, body } => core_ir::Type::Recursive {
            var,
            body: Box::new(normalize_projected_runtime_shape(*body)),
        },
        other => other,
    }
}

fn normalize_projected_effect_shape(ty: core_ir::Type) -> core_ir::Type {
    match ty {
        core_ir::Type::Unknown => core_ir::Type::Never,
        core_ir::Type::Row { items, tail } => normalize_projected_effect_row_shape(items, *tail),
        core_ir::Type::Named { .. } => ty,
        core_ir::Type::Never | core_ir::Type::Any | core_ir::Type::Var(_) => ty,
        _ => core_ir::Type::Never,
    }
}

fn normalize_projected_effect_row_shape(
    items: Vec<core_ir::Type>,
    tail: core_ir::Type,
) -> core_ir::Type {
    let tail = match normalize_projected_effect_shape(tail) {
        core_ir::Type::Row {
            items: nested_items,
            tail: nested_tail,
        } if nested_items.is_empty() => *nested_tail,
        core_ir::Type::Row { items, tail } => core_ir::Type::Row { items, tail },
        tail @ (core_ir::Type::Never
        | core_ir::Type::Any
        | core_ir::Type::Unknown
        | core_ir::Type::Var(_)) => tail,
        _ => core_ir::Type::Never,
    };
    core_ir::Type::Row {
        items: items
            .into_iter()
            .map(normalize_projected_runtime_shape)
            .collect(),
        tail: Box::new(tail),
    }
}

fn normalize_projected_runtime_shape_arg(arg: core_ir::TypeArg) -> core_ir::TypeArg {
    match arg {
        core_ir::TypeArg::Type(ty) => core_ir::TypeArg::Type(normalize_projected_runtime_shape(ty)),
        core_ir::TypeArg::Bounds(bounds) => core_ir::TypeArg::Bounds(core_ir::TypeBounds {
            lower: bounds
                .lower
                .map(|ty| Box::new(normalize_projected_runtime_shape(*ty))),
            upper: bounds
                .upper
                .map(|ty| Box::new(normalize_projected_runtime_shape(*ty))),
        }),
    }
}

fn collapse_repeated_top_choice_type(ty: core_ir::Type) -> core_ir::Type {
    match ty {
        core_ir::Type::Union(items) => {
            collapse_repeated_top_choice_items(items, core_ir::Type::Union)
        }
        core_ir::Type::Inter(items) => {
            collapse_repeated_top_choice_items(items, core_ir::Type::Inter)
        }
        other => other,
    }
}

fn collapse_repeated_top_choice_items(
    items: Vec<core_ir::Type>,
    rebuild: impl FnOnce(Vec<core_ir::Type>) -> core_ir::Type,
) -> core_ir::Type {
    let mut unique = Vec::<core_ir::Type>::new();
    for item in items {
        if !unique.iter().any(|existing| existing == &item) {
            unique.push(item);
        }
    }
    if unique.len() == 1 {
        unique.pop().expect("single projected choice item")
    } else {
        rebuild(unique)
    }
}

fn merge_projected_effect_rows(
    left: &core_ir::Type,
    right: &core_ir::Type,
) -> Option<core_ir::Type> {
    if !matches!(left, core_ir::Type::Row { .. }) && !matches!(right, core_ir::Type::Row { .. }) {
        return None;
    }
    let (mut items, left_tail) = projected_effect_row_parts(left.clone());
    let (right_items, right_tail) = projected_effect_row_parts(right.clone());
    for item in right_items {
        if !matches!(item, core_ir::Type::Never) && !items.iter().any(|existing| existing == &item)
        {
            items.push(item);
        }
    }
    let tail = if matches!(left_tail, core_ir::Type::Never) || left_tail == right_tail {
        right_tail
    } else if matches!(right_tail, core_ir::Type::Never) {
        left_tail
    } else {
        core_ir::Type::Union(vec![left_tail, right_tail])
    };
    if items.is_empty() {
        return Some(tail);
    }
    Some(core_ir::Type::Row {
        items,
        tail: Box::new(tail),
    })
}

fn projected_effect_row_parts(effect: core_ir::Type) -> (Vec<core_ir::Type>, core_ir::Type) {
    match effect {
        core_ir::Type::Never => (Vec::new(), core_ir::Type::Never),
        core_ir::Type::Row { items, tail } => (items, *tail),
        other => (vec![other], core_ir::Type::Never),
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
        if !params.contains(&candidate.var) {
            continue;
        }
        let ty = substitute_type(&candidate.ty, substitutions);
        let ty = self_or_closed_candidate_type(&candidate.var, &ty).unwrap_or(ty);
        if !principal_plan_substitution_type_usable(&ty, false) {
            continue;
        }
        by_var
            .entry(candidate.var.clone())
            .or_default()
            .push((candidate.relation, ty));
    }

    for (var, candidates) in by_var {
        if substitutions.contains_key(&var) || conflicts.contains(&var) {
            continue;
        }
        let self_closed = unique_owned_candidate_type(
            candidates
                .iter()
                .filter_map(|(_, ty)| self_or_closed_candidate_type(&var, ty)),
        );
        match self_closed {
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

fn unique_owned_candidate_type(
    candidates: impl Iterator<Item = core_ir::Type>,
) -> CandidateTypeChoice {
    let mut choice: Option<core_ir::Type> = None;
    for candidate in candidates {
        match &choice {
            Some(existing) if existing != &candidate => return CandidateTypeChoice::Conflict,
            Some(_) => {}
            None => choice = Some(candidate),
        }
    }
    choice.map_or(CandidateTypeChoice::None, CandidateTypeChoice::One)
}

fn self_or_closed_candidate_type(
    var: &core_ir::TypeVar,
    ty: &core_ir::Type,
) -> Option<core_ir::Type> {
    let items = match ty {
        core_ir::Type::Union(items) | core_ir::Type::Inter(items) => items,
        _ => return None,
    };
    let mut closed = None::<core_ir::Type>;
    for item in items {
        if matches!(item, core_ir::Type::Var(item_var) if item_var == var) {
            continue;
        }
        if !principal_plan_substitution_type_usable(item, false) {
            return None;
        }
        match &closed {
            Some(existing) if existing != item => return None,
            Some(_) => {}
            None => closed = Some(item.clone()),
        }
    }
    closed
}

fn project_substitutions_from_role_requirements(
    requirements: &[core_ir::RoleRequirement],
    params: &BTreeSet<core_ir::TypeVar>,
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
    conflicts: &mut BTreeSet<core_ir::TypeVar>,
) {
    for _ in 0..4 {
        let before = (substitutions.len(), conflicts.len());
        for requirement in requirements {
            let Some(input) = first_requirement_input(requirement)
                .map(|bounds| substitute_bounds(bounds.clone(), substitutions))
                .and_then(|bounds| principal_plan_bounds_slot_type(Some(&bounds), false))
            else {
                continue;
            };
            let Some(item) = list_item_type(&input) else {
                continue;
            };
            for associated in requirement.args.iter().filter_map(requirement_associated) {
                project_list_item_associated_substitution(
                    associated,
                    &item,
                    params,
                    substitutions,
                    conflicts,
                );
            }
        }
        if before == (substitutions.len(), conflicts.len()) {
            break;
        }
    }
}

fn project_list_item_associated_substitution(
    associated: (&core_ir::Name, &core_ir::TypeBounds),
    item: &core_ir::Type,
    params: &BTreeSet<core_ir::TypeVar>,
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
    conflicts: &mut BTreeSet<core_ir::TypeVar>,
) {
    let (name, bounds) = associated;
    if name.0 != "item" || !principal_plan_substitution_type_usable(item, false) {
        return;
    }
    let bounds = substitute_bounds(bounds.clone(), substitutions);
    if let Some(lower) = bounds.lower.as_deref() {
        project_closed_substitutions_from_type(
            lower,
            item,
            params,
            substitutions,
            conflicts,
            false,
            32,
        );
    }
    if let Some(upper) = bounds.upper.as_deref() {
        project_closed_substitutions_from_type(
            upper,
            item,
            params,
            substitutions,
            conflicts,
            false,
            32,
        );
    }
}

fn first_requirement_input(requirement: &core_ir::RoleRequirement) -> Option<&core_ir::TypeBounds> {
    requirement.args.iter().find_map(|arg| match arg {
        core_ir::RoleRequirementArg::Input(bounds) => Some(bounds),
        core_ir::RoleRequirementArg::Associated { .. } => None,
    })
}

fn requirement_associated(
    arg: &core_ir::RoleRequirementArg,
) -> Option<(&core_ir::Name, &core_ir::TypeBounds)> {
    match arg {
        core_ir::RoleRequirementArg::Associated { name, bounds } => Some((name, bounds)),
        core_ir::RoleRequirementArg::Input(_) => None,
    }
}

fn list_item_type(ty: &core_ir::Type) -> Option<core_ir::Type> {
    let core_ir::Type::Named { path, args } = ty else {
        return None;
    };
    if path.segments.last().map(|name| name.0.as_str()) != Some("list") {
        return None;
    }
    match args.first()? {
        core_ir::TypeArg::Type(ty) => {
            principal_plan_substitution_type_usable(ty, false).then(|| ty.clone())
        }
        core_ir::TypeArg::Bounds(bounds) => principal_plan_bounds_slot_type(Some(bounds), false),
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

pub(crate) fn project_closed_substitutions_from_type(
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
            let actual = if allow_never {
                normalize_projected_effect_shape(substitute_type(actual, substitutions))
            } else {
                normalize_projected_substitution_type(actual, substitutions)
            };
            if principal_plan_substitution_type_usable(&actual, allow_never) {
                insert_exact_projected_substitution(substitutions, conflicts, var.clone(), actual);
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
        (core_ir::Type::Union(items) | core_ir::Type::Inter(items), actual)
            if principal_plan_substitution_type_usable(
                &normalize_projected_substitution_type(actual, substitutions),
                allow_never,
            ) =>
        {
            let actual = normalize_projected_substitution_type(actual, substitutions);
            for item in items {
                if !projection_choice_item_matches_actual(item, &actual, allow_never) {
                    continue;
                }
                project_closed_substitutions_from_type(
                    item,
                    &actual,
                    params,
                    substitutions,
                    conflicts,
                    allow_never,
                    depth - 1,
                );
            }
        }
        (
            core_ir::Type::Row { items, tail },
            core_ir::Type::Row {
                items: actual_items,
                tail: actual_tail,
            },
        ) => {
            project_closed_effect_row_substitutions(
                items,
                tail,
                actual_items,
                actual_tail,
                params,
                substitutions,
                conflicts,
                depth - 1,
            );
        }
        (core_ir::Type::Row { items, tail }, actual) if allow_never => {
            project_closed_effect_row_substitutions(
                items,
                tail,
                std::slice::from_ref(actual),
                &core_ir::Type::Never,
                params,
                substitutions,
                conflicts,
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

fn projection_choice_item_matches_actual(
    template: &core_ir::Type,
    actual: &core_ir::Type,
    allow_never: bool,
) -> bool {
    match (template, actual) {
        (core_ir::Type::Var(_), _) => false,
        (core_ir::Type::Unknown | core_ir::Type::Any, _) => false,
        (_, core_ir::Type::Unknown | core_ir::Type::Any) => false,
        (_, core_ir::Type::Never) => allow_never && matches!(template, core_ir::Type::Never),
        (core_ir::Type::Never, _) => false,
        (
            core_ir::Type::Named { path, args },
            core_ir::Type::Named {
                path: actual_path,
                args: actual_args,
            },
        ) => path == actual_path && args.len() == actual_args.len(),
        (core_ir::Type::Fun { .. }, core_ir::Type::Fun { .. }) => true,
        (core_ir::Type::Tuple(items), core_ir::Type::Tuple(actual_items)) => {
            items.len() == actual_items.len()
        }
        (core_ir::Type::Record(_), core_ir::Type::Record(_)) => true,
        (core_ir::Type::Variant(_), core_ir::Type::Variant(_)) => true,
        (core_ir::Type::Row { .. }, core_ir::Type::Row { .. }) => true,
        (core_ir::Type::Row { .. }, _) => allow_never,
        (core_ir::Type::Recursive { body, .. }, actual) => {
            projection_choice_item_matches_actual(body, actual, allow_never)
        }
        (template, core_ir::Type::Recursive { body, .. }) => {
            projection_choice_item_matches_actual(template, body, allow_never)
        }
        (template, actual) => template == actual,
    }
}

pub(crate) fn project_closed_substitutions_from_type_bounds(
    template: &core_ir::Type,
    actual: &core_ir::TypeBounds,
    params: &BTreeSet<core_ir::TypeVar>,
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
    conflicts: &mut BTreeSet<core_ir::TypeVar>,
    allow_never: bool,
    depth: usize,
) {
    let actual = substitute_bounds(actual.clone(), substitutions);
    if let Some(actual) = principal_plan_bounds_single_closed_type(&actual, allow_never) {
        project_closed_substitutions_from_type(
            template,
            &actual,
            params,
            substitutions,
            conflicts,
            allow_never,
            depth,
        );
        return;
    }
    if let Some(lower) = actual.lower.as_deref() {
        project_closed_substitutions_from_type(
            template,
            lower,
            params,
            substitutions,
            conflicts,
            allow_never,
            depth,
        );
    }
    if let Some(upper) = actual.upper.as_deref() {
        project_closed_substitutions_from_type(
            template,
            upper,
            params,
            substitutions,
            conflicts,
            allow_never,
            depth,
        );
    }
}

fn project_closed_effect_row_substitutions(
    template_items: &[core_ir::Type],
    template_tail: &core_ir::Type,
    actual_items: &[core_ir::Type],
    actual_tail: &core_ir::Type,
    params: &BTreeSet<core_ir::TypeVar>,
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
    conflicts: &mut BTreeSet<core_ir::TypeVar>,
    depth: usize,
) {
    if depth == 0 {
        return;
    }
    let mut matched_actual = vec![false; actual_items.len()];
    let mut row_vars = Vec::new();

    for template in template_items {
        match template {
            core_ir::Type::Var(var) if params.contains(var) => row_vars.push(var.clone()),
            _ => {
                for (index, actual) in actual_items.iter().enumerate() {
                    if matched_actual[index] || !same_effect_head(template, actual) {
                        continue;
                    }
                    project_closed_substitutions_from_type(
                        template,
                        actual,
                        params,
                        substitutions,
                        conflicts,
                        true,
                        depth - 1,
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
        if principal_plan_substitution_type_usable(&residual, true) {
            insert_exact_projected_substitution(substitutions, conflicts, var, residual.clone());
        }
    }
    project_closed_substitutions_from_type(
        template_tail,
        &residual,
        params,
        substitutions,
        conflicts,
        true,
        depth - 1,
    );
}

fn project_closed_substitutions_from_type_arg(
    template: &core_ir::TypeArg,
    actual: &core_ir::TypeArg,
    params: &BTreeSet<core_ir::TypeVar>,
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
    conflicts: &mut BTreeSet<core_ir::TypeVar>,
    _allow_never: bool,
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
                false,
                depth,
            );
        }
        (core_ir::TypeArg::Type(template), core_ir::TypeArg::Bounds(actual)) => {
            let actual_bounds = substitute_bounds(actual.clone(), substitutions);
            if let Some(actual) = principal_plan_bounds_single_closed_type(&actual_bounds, false) {
                project_closed_substitutions_from_type(
                    template,
                    &actual,
                    params,
                    substitutions,
                    conflicts,
                    false,
                    depth,
                );
            }
        }
        (core_ir::TypeArg::Bounds(template), core_ir::TypeArg::Type(actual)) => {
            let actual = normalize_projected_substitution_type(actual, substitutions);
            if !principal_plan_substitution_type_usable(&actual, false) {
                return;
            }
            project_closed_substitutions_from_bounds(
                template,
                &actual,
                params,
                substitutions,
                conflicts,
                false,
                depth,
            );
        }
        (core_ir::TypeArg::Bounds(template), core_ir::TypeArg::Bounds(actual)) => {
            let actual_bounds = substitute_bounds(actual.clone(), substitutions);
            if let Some(actual) = principal_plan_bounds_single_closed_type(&actual_bounds, false) {
                project_closed_substitutions_from_bounds(
                    template,
                    &actual,
                    params,
                    substitutions,
                    conflicts,
                    false,
                    depth,
                );
            }
        }
    }
}

fn project_closed_substitutions_from_bounds(
    template: &core_ir::TypeBounds,
    actual: &core_ir::Type,
    params: &BTreeSet<core_ir::TypeVar>,
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
    conflicts: &mut BTreeSet<core_ir::TypeVar>,
    allow_never: bool,
    depth: usize,
) {
    if !principal_plan_substitution_type_usable(actual, allow_never) {
        return;
    }

    if let Some(lower) = template.lower.as_deref() {
        project_closed_substitutions_from_type(
            lower,
            actual,
            params,
            substitutions,
            conflicts,
            allow_never,
            depth,
        );
        project_choice_var_items_from_bound(
            lower,
            actual,
            params,
            substitutions,
            conflicts,
            allow_never,
            BoundChoicePolarity::Lower,
            depth,
        );
    }
    if let Some(upper) = template.upper.as_deref() {
        project_closed_substitutions_from_type(
            upper,
            actual,
            params,
            substitutions,
            conflicts,
            allow_never,
            depth,
        );
        project_choice_var_items_from_bound(
            upper,
            actual,
            params,
            substitutions,
            conflicts,
            allow_never,
            BoundChoicePolarity::Upper,
            depth,
        );
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BoundChoicePolarity {
    Lower,
    Upper,
}

fn project_choice_var_items_from_bound(
    template: &core_ir::Type,
    actual: &core_ir::Type,
    params: &BTreeSet<core_ir::TypeVar>,
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
    conflicts: &mut BTreeSet<core_ir::TypeVar>,
    allow_never: bool,
    polarity: BoundChoicePolarity,
    depth: usize,
) {
    if depth == 0 {
        return;
    }
    let actual = if allow_never {
        normalize_projected_effect_shape(substitute_type(actual, substitutions))
    } else {
        normalize_projected_substitution_type(actual, substitutions)
    };
    if !principal_plan_substitution_type_usable(&actual, allow_never) {
        return;
    }
    match (polarity, template) {
        (BoundChoicePolarity::Lower, core_ir::Type::Union(items)) => {
            for item in items {
                if let core_ir::Type::Var(var) = item
                    && params.contains(var)
                {
                    insert_exact_projected_substitution(
                        substitutions,
                        conflicts,
                        var.clone(),
                        actual.clone(),
                    );
                    continue;
                }
                project_choice_var_items_from_bound(
                    item,
                    &actual,
                    params,
                    substitutions,
                    conflicts,
                    allow_never,
                    polarity,
                    depth - 1,
                );
            }
        }
        (BoundChoicePolarity::Lower, core_ir::Type::Inter(items))
        | (BoundChoicePolarity::Upper, core_ir::Type::Union(items))
        | (BoundChoicePolarity::Upper, core_ir::Type::Inter(items)) => {
            for item in items {
                project_choice_var_items_from_bound(
                    item,
                    &actual,
                    params,
                    substitutions,
                    conflicts,
                    allow_never,
                    polarity,
                    depth - 1,
                );
            }
        }
        (_, core_ir::Type::Recursive { body, .. }) => {
            project_choice_var_items_from_bound(
                body,
                &actual,
                params,
                substitutions,
                conflicts,
                allow_never,
                polarity,
                depth - 1,
            );
        }
        _ => {}
    }
}

fn principal_plan_bounds_single_closed_type(
    bounds: &core_ir::TypeBounds,
    allow_never: bool,
) -> Option<core_ir::Type> {
    let lower = bounds
        .lower
        .as_deref()
        .cloned()
        .map(normalize_projected_closed_choice_type);
    let upper = bounds
        .upper
        .as_deref()
        .cloned()
        .map(normalize_projected_closed_choice_type);
    let choice = match (lower, upper) {
        (Some(lower), Some(upper)) if lower == upper => lower,
        (Some(ty), None) | (None, Some(ty)) => ty,
        _ => return None,
    };
    principal_plan_substitution_type_usable(&choice, allow_never).then_some(choice)
}

fn normalize_projected_closed_choice_type(ty: core_ir::Type) -> core_ir::Type {
    collapse_repeated_top_choice_type(collapse_single_bound_type_args(
        normalize_projected_runtime_shape(ty),
    ))
}

fn collapse_single_bound_type_args(ty: core_ir::Type) -> core_ir::Type {
    match ty {
        core_ir::Type::Named { path, args } => core_ir::Type::Named {
            path,
            args: args
                .into_iter()
                .map(collapse_single_bound_type_arg)
                .collect(),
        },
        core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => core_ir::Type::Fun {
            param: Box::new(collapse_single_bound_type_args(*param)),
            param_effect: Box::new(collapse_single_bound_type_args(*param_effect)),
            ret_effect: Box::new(collapse_single_bound_type_args(*ret_effect)),
            ret: Box::new(collapse_single_bound_type_args(*ret)),
        },
        core_ir::Type::Tuple(items) => core_ir::Type::Tuple(
            items
                .into_iter()
                .map(collapse_single_bound_type_args)
                .collect(),
        ),
        core_ir::Type::Record(record) => core_ir::Type::Record(core_ir::RecordType {
            fields: record
                .fields
                .into_iter()
                .map(|field| core_ir::RecordField {
                    name: field.name,
                    value: collapse_single_bound_type_args(field.value),
                    optional: field.optional,
                })
                .collect(),
            spread: record.spread.map(|spread| match spread {
                core_ir::RecordSpread::Head(ty) => {
                    core_ir::RecordSpread::Head(Box::new(collapse_single_bound_type_args(*ty)))
                }
                core_ir::RecordSpread::Tail(ty) => {
                    core_ir::RecordSpread::Tail(Box::new(collapse_single_bound_type_args(*ty)))
                }
            }),
        }),
        core_ir::Type::Variant(variant) => core_ir::Type::Variant(core_ir::VariantType {
            cases: variant
                .cases
                .into_iter()
                .map(|case| core_ir::VariantCase {
                    name: case.name,
                    payloads: case
                        .payloads
                        .into_iter()
                        .map(collapse_single_bound_type_args)
                        .collect(),
                })
                .collect(),
            tail: variant
                .tail
                .map(|tail| Box::new(collapse_single_bound_type_args(*tail))),
        }),
        core_ir::Type::Union(items) => core_ir::Type::Union(
            items
                .into_iter()
                .map(collapse_single_bound_type_args)
                .collect(),
        ),
        core_ir::Type::Inter(items) => core_ir::Type::Inter(
            items
                .into_iter()
                .map(collapse_single_bound_type_args)
                .collect(),
        ),
        core_ir::Type::Row { items, tail } => core_ir::Type::Row {
            items: items
                .into_iter()
                .map(collapse_single_bound_type_args)
                .collect(),
            tail: Box::new(collapse_single_bound_type_args(*tail)),
        },
        core_ir::Type::Recursive { var, body } => core_ir::Type::Recursive {
            var,
            body: Box::new(collapse_single_bound_type_args(*body)),
        },
        other => other,
    }
}

fn collapse_single_bound_type_arg(arg: core_ir::TypeArg) -> core_ir::TypeArg {
    match arg {
        core_ir::TypeArg::Type(ty) => core_ir::TypeArg::Type(collapse_single_bound_type_args(ty)),
        core_ir::TypeArg::Bounds(bounds) => {
            let bounds = core_ir::TypeBounds {
                lower: bounds
                    .lower
                    .map(|ty| Box::new(collapse_single_bound_type_args(*ty))),
                upper: bounds
                    .upper
                    .map(|ty| Box::new(collapse_single_bound_type_args(*ty))),
            };
            principal_plan_bounds_single_closed_type(&bounds, false)
                .map(core_ir::TypeArg::Type)
                .unwrap_or(core_ir::TypeArg::Bounds(bounds))
        }
    }
}

fn principal_plan_substitution_type_usable(ty: &core_ir::Type, allow_never: bool) -> bool {
    !matches!(
        ty,
        core_ir::Type::Unknown | core_ir::Type::Any | core_ir::Type::Var(_)
    ) && (allow_never || !matches!(ty, core_ir::Type::Never))
        && !type_has_vars(ty)
        && !type_has_any(ty)
        && (allow_never || !core_type_contains_unknown(ty))
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
    if matches!(ty, core_ir::Type::Unknown | core_ir::Type::Any) {
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

fn type_has_any(ty: &core_ir::Type) -> bool {
    match ty {
        core_ir::Type::Any => true,
        core_ir::Type::Unknown | core_ir::Type::Never | core_ir::Type::Var(_) => false,
        core_ir::Type::Named { args, .. } => args.iter().any(type_arg_has_any),
        core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            type_has_any(param)
                || type_has_any(param_effect)
                || type_has_any(ret_effect)
                || type_has_any(ret)
        }
        core_ir::Type::Tuple(items) | core_ir::Type::Union(items) | core_ir::Type::Inter(items) => {
            items.iter().any(type_has_any)
        }
        core_ir::Type::Row { items, tail } => items.iter().any(type_has_any) || type_has_any(tail),
        core_ir::Type::Record(record) => {
            record.fields.iter().any(|field| type_has_any(&field.value))
        }
        core_ir::Type::Variant(variant) => {
            variant
                .cases
                .iter()
                .flat_map(|case| &case.payloads)
                .any(type_has_any)
                || variant.tail.as_deref().is_some_and(type_has_any)
        }
        core_ir::Type::Recursive { body, .. } => type_has_any(body),
    }
}

fn type_arg_has_any(arg: &core_ir::TypeArg) -> bool {
    match arg {
        core_ir::TypeArg::Type(ty) => type_has_any(ty),
        core_ir::TypeArg::Bounds(bounds) => {
            bounds.lower.as_deref().is_some_and(type_has_any)
                || bounds.upper.as_deref().is_some_and(type_has_any)
        }
    }
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
    fn plan_normalization_closes_alias_candidate_after_known_substitution() {
        let a = tv("a");
        let t = tv("t");
        let mut plan = list_plan_for_arg(list_of(named("int")));
        plan.substitutions = vec![core_ir::TypeSubstitution {
            var: t.clone(),
            ty: named("int"),
        }];
        let candidates = vec![core_ir::PrincipalSubstitutionCandidate {
            var: a.clone(),
            relation: core_ir::PrincipalCandidateRelation::Exact,
            ty: core_ir::Type::Var(t),
            source_edge: None,
            path: vec![core_ir::PrincipalSlotPathSegment::Result],
        }];

        let normalized = normalize_principal_elaboration_plan(plan, &candidates);

        assert!(normalized.complete, "{:?}", normalized.incomplete_reasons);
        assert_eq!(
            normalized.substitutions,
            vec![
                core_ir::TypeSubstitution {
                    var: a,
                    ty: named("int"),
                },
                core_ir::TypeSubstitution {
                    var: tv("t"),
                    ty: named("int"),
                },
            ]
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
    fn plan_normalization_closes_child_var_from_repeated_choice_bound_args() {
        let list_int = list_of(named("int"));
        let list_bounded_int = core_ir::Type::Named {
            path: core_ir::Path::from_name(core_ir::Name("list".to_string())),
            args: vec![core_ir::TypeArg::Bounds(core_ir::TypeBounds {
                lower: Some(Box::new(core_ir::Type::Union(vec![
                    named("int"),
                    named("int"),
                ]))),
                upper: Some(Box::new(named("int"))),
            })],
        };
        let plan = list_plan_for_arg(core_ir::Type::Union(vec![
            list_int.clone(),
            list_bounded_int,
            list_int,
        ]));
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
    fn plan_normalization_projects_list_item_role_requirement() {
        let mut plan = core_ir::PrincipalElaborationPlan {
            target: Some(core_ir::Path::from_name(core_ir::Name("all".to_string()))),
            principal_callee: core_ir::Type::Fun {
                param: Box::new(core_ir::Type::Var(tv("container"))),
                param_effect: Box::new(core_ir::Type::Never),
                ret_effect: Box::new(core_ir::Type::Never),
                ret: Box::new(core_ir::Type::Var(tv("item"))),
            },
            substitutions: vec![core_ir::TypeSubstitution {
                var: tv("container"),
                ty: list_of(named("int")),
            }],
            args: vec![core_ir::PrincipalElaborationArg {
                index: 0,
                intrinsic: core_ir::TypeBounds::exact(list_of(named("int"))),
                contextual: None,
                expected_runtime: None,
                source_edge: None,
            }],
            result: core_ir::PrincipalElaborationResult {
                intrinsic: core_ir::TypeBounds::default(),
                contextual: None,
                expected_runtime: None,
            },
            adapters: Vec::new(),
            complete: false,
            incomplete_reasons: Vec::new(),
        };
        plan.result.contextual = Some(core_ir::TypeBounds::exact(core_ir::Type::Var(tv("item"))));

        let normalized = normalize_principal_elaboration_plan_with_requirements(
            plan,
            &[],
            &[core_ir::RoleRequirement {
                role: core_ir::Path::from_name(core_ir::Name("Fold".to_string())),
                args: vec![
                    core_ir::RoleRequirementArg::Input(core_ir::TypeBounds::exact(
                        core_ir::Type::Var(tv("container")),
                    )),
                    core_ir::RoleRequirementArg::Associated {
                        name: core_ir::Name("item".to_string()),
                        bounds: core_ir::TypeBounds::exact(core_ir::Type::Var(tv("item"))),
                    },
                ],
            }],
        );

        assert!(normalized.complete, "{:?}", normalized.incomplete_reasons);
        assert!(
            normalized
                .substitutions
                .contains(&core_ir::TypeSubstitution {
                    var: tv("item"),
                    ty: named("int"),
                })
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

    #[test]
    fn plan_normalization_does_not_invent_adapter_holes() {
        let plan = list_plan_for_arg(list_of(named("int")));
        let normalized = substitute_principal_elaboration_plan(plan, &BTreeMap::new(), &[]);

        assert!(normalized.complete, "{:?}", normalized.incomplete_reasons);
        assert!(normalized.adapters.is_empty());
    }

    #[test]
    fn plan_normalization_preserves_missing_adapter_hole_reason() {
        let mut plan = list_plan_for_arg(list_of(named("int")));
        plan.incomplete_reasons = vec![
            core_ir::PrincipalElaborationIncompleteReason::MissingAdapterHole(
                core_ir::PrincipalAdapterKind::ValueToThunk,
            ),
        ];
        let normalized = substitute_principal_elaboration_plan(plan, &BTreeMap::new(), &[]);

        assert!(!normalized.complete);
        assert!(normalized.adapters.is_empty());
        assert!(normalized.incomplete_reasons.contains(
            &core_ir::PrincipalElaborationIncompleteReason::MissingAdapterHole(
                core_ir::PrincipalAdapterKind::ValueToThunk,
            )
        ));
    }

    #[test]
    fn closed_projection_matches_effect_row_residuals_without_graph_solving() {
        let item = tv("item");
        let residual = tv("residual");
        let template = core_ir::Type::Row {
            items: vec![named_with_args(
                "sub",
                vec![core_ir::TypeArg::Type(core_ir::Type::Var(item.clone()))],
            )],
            tail: Box::new(core_ir::Type::Var(residual.clone())),
        };
        let actual = core_ir::Type::Row {
            items: vec![
                named_with_args("sub", vec![core_ir::TypeArg::Type(named("int"))]),
                named("junction"),
            ],
            tail: Box::new(core_ir::Type::Never),
        };
        let params = BTreeSet::from([item.clone(), residual.clone()]);
        let mut substitutions = BTreeMap::new();
        let mut conflicts = BTreeSet::new();

        project_closed_substitutions_from_type(
            &template,
            &actual,
            &params,
            &mut substitutions,
            &mut conflicts,
            true,
            64,
        );

        assert!(conflicts.is_empty(), "{conflicts:?}");
        assert_eq!(substitutions.get(&item), Some(&named("int")));
        assert_eq!(substitutions.get(&residual), Some(&named("junction")));
    }

    #[test]
    fn closed_projection_does_not_solve_principal_var_union_from_closed_actual() {
        let left = tv("left");
        let right = tv("right");
        let template = core_ir::Type::Union(vec![
            core_ir::Type::Var(left.clone()),
            core_ir::Type::Var(right.clone()),
        ]);
        let actual = named("int");
        let params = BTreeSet::from([left.clone(), right.clone()]);
        let mut substitutions = BTreeMap::new();
        let mut conflicts = BTreeSet::new();

        project_closed_substitutions_from_type(
            &template,
            &actual,
            &params,
            &mut substitutions,
            &mut conflicts,
            false,
            64,
        );

        assert!(conflicts.is_empty(), "{conflicts:?}");
        assert_eq!(substitutions.get(&left), None);
        assert_eq!(substitutions.get(&right), None);
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

    fn named_with_args(name: &str, args: Vec<core_ir::TypeArg>) -> core_ir::Type {
        core_ir::Type::Named {
            path: core_ir::Path::from_name(core_ir::Name(name.to_string())),
            args,
        }
    }

    fn tv(name: &str) -> core_ir::TypeVar {
        core_ir::TypeVar(name.to_string())
    }
}
