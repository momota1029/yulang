use super::*;

const MAX_INFER_SUBSTITUTION_DEPTH: usize = 128;

#[derive(Debug, Clone, Copy, Default)]
pub(super) struct TypeSubstitutionInferOptions {
    include_function_effects: bool,
    prefer_non_never: bool,
    skip_empty_effect_residual: bool,
}

impl TypeSubstitutionInferOptions {
    fn prefer_non_never() -> Self {
        Self {
            prefer_non_never: true,
            ..Self::default()
        }
    }

    fn prefer_non_never_skip_empty_effects() -> Self {
        Self {
            prefer_non_never: true,
            skip_empty_effect_residual: true,
            ..Self::default()
        }
    }
}

pub(crate) fn infer_type_substitutions(
    template: &typed_ir::Type,
    actual: &typed_ir::Type,
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) {
    infer_type_substitutions_inner(
        template,
        actual,
        params,
        substitutions,
        MAX_INFER_SUBSTITUTION_DEPTH,
        TypeSubstitutionInferOptions::default(),
    );
}

pub(crate) fn infer_type_substitutions_prefer_non_never(
    template: &typed_ir::Type,
    actual: &typed_ir::Type,
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) {
    infer_type_substitutions_inner(
        template,
        actual,
        params,
        substitutions,
        MAX_INFER_SUBSTITUTION_DEPTH,
        TypeSubstitutionInferOptions::prefer_non_never(),
    );
}

pub(crate) fn infer_type_substitutions_prefer_non_never_skip_empty_effects(
    template: &typed_ir::Type,
    actual: &typed_ir::Type,
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) {
    infer_type_substitutions_inner(
        template,
        actual,
        params,
        substitutions,
        MAX_INFER_SUBSTITUTION_DEPTH,
        TypeSubstitutionInferOptions::prefer_non_never_skip_empty_effects(),
    );
}

pub(crate) fn substitute_type(
    ty: &typed_ir::Type,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> typed_ir::Type {
    substitute_type_inner(ty, substitutions, &mut BTreeSet::new(), &BTreeSet::new())
}

fn substitute_type_inner(
    ty: &typed_ir::Type,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    active: &mut BTreeSet<typed_ir::TypeVar>,
    bound: &BTreeSet<typed_ir::TypeVar>,
) -> typed_ir::Type {
    match ty {
        typed_ir::Type::Unknown => typed_ir::Type::Unknown,
        typed_ir::Type::Never => typed_ir::Type::Never,
        typed_ir::Type::Any => typed_ir::Type::Any,
        typed_ir::Type::Var(var) => {
            if bound.contains(var) {
                return typed_ir::Type::Var(var.clone());
            }
            let Some(replacement) = substitutions.get(var) else {
                return typed_ir::Type::Var(var.clone());
            };
            if !active.insert(var.clone()) {
                return typed_ir::Type::Var(var.clone());
            }
            let substituted = substitute_type_inner(replacement, substitutions, active, bound);
            active.remove(var);
            substituted
        }
        typed_ir::Type::Named { path, args } => typed_ir::Type::Named {
            path: path.clone(),
            args: args
                .iter()
                .map(|arg| substitute_type_arg(arg, substitutions, active, bound))
                .collect(),
        },
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => typed_ir::Type::Fun {
            param: Box::new(substitute_type_inner(param, substitutions, active, bound)),
            param_effect: Box::new(substitute_type_inner(
                param_effect,
                substitutions,
                active,
                bound,
            )),
            ret_effect: Box::new(substitute_type_inner(
                ret_effect,
                substitutions,
                active,
                bound,
            )),
            ret: Box::new(substitute_type_inner(ret, substitutions, active, bound)),
        },
        typed_ir::Type::Tuple(items) => typed_ir::Type::Tuple(
            items
                .iter()
                .map(|item| substitute_type_inner(item, substitutions, active, bound))
                .collect(),
        ),
        typed_ir::Type::Record(record) => typed_ir::Type::Record(typed_ir::RecordType {
            fields: record
                .fields
                .iter()
                .map(|field| typed_ir::RecordField {
                    name: field.name.clone(),
                    value: substitute_type_inner(&field.value, substitutions, active, bound),
                    optional: field.optional,
                })
                .collect(),
            spread: record.spread.as_ref().map(|spread| match spread {
                typed_ir::RecordSpread::Head(ty) => typed_ir::RecordSpread::Head(Box::new(
                    substitute_type_inner(ty, substitutions, active, bound),
                )),
                typed_ir::RecordSpread::Tail(ty) => typed_ir::RecordSpread::Tail(Box::new(
                    substitute_type_inner(ty, substitutions, active, bound),
                )),
            }),
        }),
        typed_ir::Type::Variant(variant) => typed_ir::Type::Variant(typed_ir::VariantType {
            cases: variant
                .cases
                .iter()
                .map(|case| typed_ir::VariantCase {
                    name: case.name.clone(),
                    payloads: case
                        .payloads
                        .iter()
                        .map(|payload| substitute_type_inner(payload, substitutions, active, bound))
                        .collect(),
                })
                .collect(),
            tail: variant
                .tail
                .as_ref()
                .map(|tail| Box::new(substitute_type_inner(tail, substitutions, active, bound))),
        }),
        typed_ir::Type::Row { items, tail } => typed_ir::Type::Row {
            items: items
                .iter()
                .map(|item| substitute_type_inner(item, substitutions, active, bound))
                .collect(),
            tail: Box::new(substitute_type_inner(tail, substitutions, active, bound)),
        },
        typed_ir::Type::Union(items) => typed_ir::Type::Union(
            items
                .iter()
                .map(|item| substitute_type_inner(item, substitutions, active, bound))
                .collect(),
        ),
        typed_ir::Type::Inter(items) => typed_ir::Type::Inter(
            items
                .iter()
                .map(|item| substitute_type_inner(item, substitutions, active, bound))
                .collect(),
        ),
        typed_ir::Type::Recursive { var, body } => {
            let (var, body) = if substitution_values_contain_free_var(substitutions, var) {
                let fresh = fresh_recursive_binder_var(var, body, substitutions, active, bound);
                (fresh.clone(), rename_bound_type_var(body, var, &fresh))
            } else {
                (var.clone(), body.as_ref().clone())
            };
            let mut scoped_bound = bound.clone();
            scoped_bound.insert(var.clone());
            typed_ir::Type::Recursive {
                var,
                body: Box::new(substitute_type_inner(
                    &body,
                    substitutions,
                    active,
                    &scoped_bound,
                )),
            }
        }
    }
}

fn substitution_values_contain_free_var(
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    var: &typed_ir::TypeVar,
) -> bool {
    substitutions
        .values()
        .any(|ty| type_contains_free_var(ty, var))
}

fn type_contains_free_var(ty: &typed_ir::Type, var: &typed_ir::TypeVar) -> bool {
    let mut vars = BTreeSet::new();
    collect_type_vars(ty, &mut vars);
    vars.contains(var)
}

fn fresh_recursive_binder_var(
    var: &typed_ir::TypeVar,
    body: &typed_ir::Type,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    active: &BTreeSet<typed_ir::TypeVar>,
    bound: &BTreeSet<typed_ir::TypeVar>,
) -> typed_ir::TypeVar {
    let mut used = BTreeSet::new();
    collect_all_type_vars(body, &mut used);
    used.extend(substitutions.keys().cloned());
    for ty in substitutions.values() {
        collect_all_type_vars(ty, &mut used);
    }
    used.extend(active.iter().cloned());
    used.extend(bound.iter().cloned());

    let mut index = 0;
    loop {
        let candidate = typed_ir::TypeVar(format!("{}#subst{index}", var.0));
        if !used.contains(&candidate) {
            return candidate;
        }
        index += 1;
    }
}

fn collect_all_type_vars(ty: &typed_ir::Type, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    match ty {
        typed_ir::Type::Unknown | typed_ir::Type::Never | typed_ir::Type::Any => {}
        typed_ir::Type::Var(var) => {
            vars.insert(var.clone());
        }
        typed_ir::Type::Named { args, .. } => {
            for arg in args {
                collect_all_type_arg_vars(arg, vars);
            }
        }
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            collect_all_type_vars(param, vars);
            collect_all_type_vars(param_effect, vars);
            collect_all_type_vars(ret_effect, vars);
            collect_all_type_vars(ret, vars);
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => {
            for item in items {
                collect_all_type_vars(item, vars);
            }
        }
        typed_ir::Type::Record(record) => {
            for field in &record.fields {
                collect_all_type_vars(&field.value, vars);
            }
            if let Some(spread) = &record.spread {
                match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        collect_all_type_vars(ty, vars);
                    }
                }
            }
        }
        typed_ir::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_all_type_vars(payload, vars);
                }
            }
            if let Some(tail) = variant.tail.as_deref() {
                collect_all_type_vars(tail, vars);
            }
        }
        typed_ir::Type::Row { items, tail } => {
            for item in items {
                collect_all_type_vars(item, vars);
            }
            collect_all_type_vars(tail, vars);
        }
        typed_ir::Type::Recursive { var, body } => {
            vars.insert(var.clone());
            collect_all_type_vars(body, vars);
        }
    }
}

fn collect_all_type_arg_vars(arg: &typed_ir::TypeArg, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    match arg {
        typed_ir::TypeArg::Type(ty) => collect_all_type_vars(ty, vars),
        typed_ir::TypeArg::Bounds(bounds) => {
            if let Some(lower) = bounds.lower.as_deref() {
                collect_all_type_vars(lower, vars);
            }
            if let Some(upper) = bounds.upper.as_deref() {
                collect_all_type_vars(upper, vars);
            }
        }
    }
}

fn rename_bound_type_var(
    ty: &typed_ir::Type,
    from: &typed_ir::TypeVar,
    to: &typed_ir::TypeVar,
) -> typed_ir::Type {
    match ty {
        typed_ir::Type::Unknown => typed_ir::Type::Unknown,
        typed_ir::Type::Never => typed_ir::Type::Never,
        typed_ir::Type::Any => typed_ir::Type::Any,
        typed_ir::Type::Var(var) if var == from => typed_ir::Type::Var(to.clone()),
        typed_ir::Type::Var(var) => typed_ir::Type::Var(var.clone()),
        typed_ir::Type::Named { path, args } => typed_ir::Type::Named {
            path: path.clone(),
            args: args
                .iter()
                .map(|arg| rename_bound_type_arg_var(arg, from, to))
                .collect(),
        },
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => typed_ir::Type::Fun {
            param: Box::new(rename_bound_type_var(param, from, to)),
            param_effect: Box::new(rename_bound_type_var(param_effect, from, to)),
            ret_effect: Box::new(rename_bound_type_var(ret_effect, from, to)),
            ret: Box::new(rename_bound_type_var(ret, from, to)),
        },
        typed_ir::Type::Tuple(items) => typed_ir::Type::Tuple(
            items
                .iter()
                .map(|item| rename_bound_type_var(item, from, to))
                .collect(),
        ),
        typed_ir::Type::Record(record) => typed_ir::Type::Record(typed_ir::RecordType {
            fields: record
                .fields
                .iter()
                .map(|field| typed_ir::RecordField {
                    name: field.name.clone(),
                    value: rename_bound_type_var(&field.value, from, to),
                    optional: field.optional,
                })
                .collect(),
            spread: record.spread.as_ref().map(|spread| match spread {
                typed_ir::RecordSpread::Head(ty) => {
                    typed_ir::RecordSpread::Head(Box::new(rename_bound_type_var(ty, from, to)))
                }
                typed_ir::RecordSpread::Tail(ty) => {
                    typed_ir::RecordSpread::Tail(Box::new(rename_bound_type_var(ty, from, to)))
                }
            }),
        }),
        typed_ir::Type::Variant(variant) => typed_ir::Type::Variant(typed_ir::VariantType {
            cases: variant
                .cases
                .iter()
                .map(|case| typed_ir::VariantCase {
                    name: case.name.clone(),
                    payloads: case
                        .payloads
                        .iter()
                        .map(|payload| rename_bound_type_var(payload, from, to))
                        .collect(),
                })
                .collect(),
            tail: variant
                .tail
                .as_ref()
                .map(|tail| Box::new(rename_bound_type_var(tail, from, to))),
        }),
        typed_ir::Type::Row { items, tail } => typed_ir::Type::Row {
            items: items
                .iter()
                .map(|item| rename_bound_type_var(item, from, to))
                .collect(),
            tail: Box::new(rename_bound_type_var(tail, from, to)),
        },
        typed_ir::Type::Union(items) => typed_ir::Type::Union(
            items
                .iter()
                .map(|item| rename_bound_type_var(item, from, to))
                .collect(),
        ),
        typed_ir::Type::Inter(items) => typed_ir::Type::Inter(
            items
                .iter()
                .map(|item| rename_bound_type_var(item, from, to))
                .collect(),
        ),
        typed_ir::Type::Recursive { var, body } if var == from => typed_ir::Type::Recursive {
            var: var.clone(),
            body: body.clone(),
        },
        typed_ir::Type::Recursive { var, body } => typed_ir::Type::Recursive {
            var: var.clone(),
            body: Box::new(rename_bound_type_var(body, from, to)),
        },
    }
}

fn rename_bound_type_arg_var(
    arg: &typed_ir::TypeArg,
    from: &typed_ir::TypeVar,
    to: &typed_ir::TypeVar,
) -> typed_ir::TypeArg {
    match arg {
        typed_ir::TypeArg::Type(ty) => typed_ir::TypeArg::Type(rename_bound_type_var(ty, from, to)),
        typed_ir::TypeArg::Bounds(bounds) => typed_ir::TypeArg::Bounds(typed_ir::TypeBounds {
            lower: bounds
                .lower
                .as_ref()
                .map(|ty| Box::new(rename_bound_type_var(ty, from, to))),
            upper: bounds
                .upper
                .as_ref()
                .map(|ty| Box::new(rename_bound_type_var(ty, from, to))),
        }),
    }
}

pub(crate) fn substitute_hir_type(
    ty: &RuntimeType,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
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
    scheme: typed_ir::Scheme,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> typed_ir::Scheme {
    typed_ir::Scheme {
        requirements: scheme
            .requirements
            .into_iter()
            .map(|requirement| substitute_role_requirement(requirement, substitutions))
            .collect(),
        body: substitute_type(&scheme.body, substitutions),
    }
}

pub(crate) fn substitute_role_requirement(
    requirement: typed_ir::RoleRequirement,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> typed_ir::RoleRequirement {
    typed_ir::RoleRequirement {
        role: requirement.role,
        args: requirement
            .args
            .into_iter()
            .map(|arg| match arg {
                typed_ir::RoleRequirementArg::Input(bounds) => {
                    typed_ir::RoleRequirementArg::Input(substitute_bounds(bounds, substitutions))
                }
                typed_ir::RoleRequirementArg::Associated { name, bounds } => {
                    typed_ir::RoleRequirementArg::Associated {
                        name,
                        bounds: substitute_bounds(bounds, substitutions),
                    }
                }
            })
            .collect(),
    }
}

pub(crate) fn substitute_apply_evidence(
    evidence: typed_ir::ApplyEvidence,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> typed_ir::ApplyEvidence {
    let mut evidence_vars = BTreeSet::new();
    if let Some(principal) = &evidence.principal_callee {
        collect_type_vars(principal, &mut evidence_vars);
    }
    let mut evidence_substitutions = substitutions
        .iter()
        .filter_map(|(var, ty)| {
            evidence_vars
                .contains(var)
                .then(|| typed_ir::TypeSubstitution {
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
        evidence_substitutions.push(typed_ir::TypeSubstitution {
            var: substitution.var,
            ty: substitute_type(&substitution.ty, substitutions),
        });
    }
    let substitution_candidates = evidence
        .substitution_candidates
        .into_iter()
        .map(|candidate| typed_ir::PrincipalSubstitutionCandidate {
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

    typed_ir::ApplyEvidence {
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
    plan: typed_ir::PrincipalElaborationPlan,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    substitution_candidates: &[typed_ir::PrincipalSubstitutionCandidate],
) -> typed_ir::PrincipalElaborationPlan {
    let plan = substitute_principal_elaboration_plan_slots(plan, substitutions);
    normalize_principal_elaboration_plan(plan, substitution_candidates)
}

fn substitute_principal_elaboration_plan_slots(
    plan: typed_ir::PrincipalElaborationPlan,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> typed_ir::PrincipalElaborationPlan {
    let mut plan_vars = BTreeSet::new();
    collect_type_vars(&plan.principal_callee, &mut plan_vars);
    let mut plan_substitutions = substitutions
        .iter()
        .filter_map(|(var, ty)| {
            plan_vars.contains(var).then(|| typed_ir::TypeSubstitution {
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
        plan_substitutions.push(typed_ir::TypeSubstitution {
            var: substitution.var,
            ty: substitute_type(&substitution.ty, substitutions),
        });
    }

    typed_ir::PrincipalElaborationPlan {
        target: plan.target,
        principal_callee: substitute_type(&plan.principal_callee, substitutions),
        substitutions: plan_substitutions,
        args: plan
            .args
            .into_iter()
            .map(|arg| typed_ir::PrincipalElaborationArg {
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
        result: typed_ir::PrincipalElaborationResult {
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
            .map(|adapter| typed_ir::PrincipalAdapterHole {
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
    plan: typed_ir::PrincipalElaborationPlan,
    substitution_candidates: &[typed_ir::PrincipalSubstitutionCandidate],
) -> typed_ir::PrincipalElaborationPlan {
    normalize_principal_elaboration_plan_with_requirements(plan, substitution_candidates, &[])
}

pub(crate) fn normalize_principal_elaboration_plan_with_requirements(
    plan: typed_ir::PrincipalElaborationPlan,
    substitution_candidates: &[typed_ir::PrincipalSubstitutionCandidate],
    requirements: &[typed_ir::RoleRequirement],
) -> typed_ir::PrincipalElaborationPlan {
    normalize_principal_elaboration_plan_with_role_impls(
        plan,
        substitution_candidates,
        requirements,
        &[],
    )
}

pub(crate) fn normalize_principal_elaboration_plan_with_role_impls(
    plan: typed_ir::PrincipalElaborationPlan,
    substitution_candidates: &[typed_ir::PrincipalSubstitutionCandidate],
    requirements: &[typed_ir::RoleRequirement],
    role_impls: &[typed_ir::RoleImplGraphNode],
) -> typed_ir::PrincipalElaborationPlan {
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
        if projected_unit_substitution_is_only_open_default(substitution, substitution_candidates) {
            continue;
        }
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
    project_principal_substitutions_until_stable(
        &mut substitutions,
        &mut conflicts,
        |substitutions, conflicts| {
            project_substitutions_from_candidates(
                substitution_candidates,
                &required_vars,
                substitutions,
                conflicts,
            );
            project_substitutions_from_role_requirements(
                requirements,
                role_impls,
                &required_vars,
                substitutions,
                conflicts,
            );
        },
    );

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
    if let Some(typed_ir::Type::Var(var)) =
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

fn project_principal_substitutions_until_stable<F>(
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
    mut project: F,
) where
    F: FnMut(&mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>, &mut BTreeSet<typed_ir::TypeVar>),
{
    loop {
        let before_substitutions = substitutions.clone();
        let before_conflicts = conflicts.clone();
        project(substitutions, conflicts);
        if before_substitutions == *substitutions && before_conflicts == *conflicts {
            break;
        }
    }
}

fn projected_unit_substitution_is_only_open_default(
    substitution: &typed_ir::TypeSubstitution,
    substitution_candidates: &[typed_ir::PrincipalSubstitutionCandidate],
) -> bool {
    if !matches!(substitution.ty, typed_ir::Type::Tuple(ref items) if items.is_empty()) {
        return false;
    }
    let mut has_candidate = false;
    for candidate in substitution_candidates
        .iter()
        .filter(|candidate| candidate.var == substitution.var)
    {
        has_candidate = true;
        if !principal_substitution_type_is_open_default(&candidate.ty) {
            return false;
        }
    }
    has_candidate
}

fn principal_plan_result_self_closed_type(
    result: &typed_ir::PrincipalElaborationResult,
    var: &typed_ir::TypeVar,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> Option<typed_ir::Type> {
    result
        .contextual
        .as_ref()
        .and_then(|bounds| principal_plan_bounds_self_closed_type(bounds, var, substitutions))
        .or_else(|| principal_plan_bounds_self_closed_type(&result.intrinsic, var, substitutions))
}

fn principal_plan_bounds_self_closed_type(
    bounds: &typed_ir::TypeBounds,
    var: &typed_ir::TypeVar,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> Option<typed_ir::Type> {
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
    mut plan: typed_ir::PrincipalElaborationPlan,
    substitutions: BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: BTreeSet<typed_ir::TypeVar>,
    substitution_candidates: &[typed_ir::PrincipalSubstitutionCandidate],
) -> typed_ir::PrincipalElaborationPlan {
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
        incomplete_reasons.push(typed_ir::PrincipalElaborationIncompleteReason::MissingTarget);
    }
    for var in &required_vars {
        if conflicts.contains(var) {
            incomplete_reasons.push(
                typed_ir::PrincipalElaborationIncompleteReason::ConflictingSubstitution(
                    var.clone(),
                ),
            );
        } else if !substitutions.contains_key(var) {
            let has_open_candidate = substitution_candidates
                .iter()
                .any(|candidate| candidate.var == *var)
                || plan.incomplete_reasons.iter().any(|reason| {
                    matches!(
                        reason,
                        typed_ir::PrincipalElaborationIncompleteReason::OpenCandidate(candidate_var)
                            if candidate_var == var
                    )
                });
            if has_open_candidate {
                incomplete_reasons.push(
                    typed_ir::PrincipalElaborationIncompleteReason::OpenCandidate(var.clone()),
                );
            } else {
                incomplete_reasons.push(
                    typed_ir::PrincipalElaborationIncompleteReason::MissingSubstitution(
                        var.clone(),
                    ),
                );
            }
        }
    }
    for arg in &plan.args {
        if principal_plan_arg_type(arg).is_none() {
            incomplete_reasons.push(typed_ir::PrincipalElaborationIncompleteReason::OpenArgType(
                arg.index,
            ));
        }
    }
    if principal_plan_result_type(&plan.result).is_none() {
        incomplete_reasons.push(typed_ir::PrincipalElaborationIncompleteReason::OpenResultType);
    }
    incomplete_reasons.extend(
        plan.incomplete_reasons
            .iter()
            .filter_map(|reason| match reason {
                typed_ir::PrincipalElaborationIncompleteReason::MissingAdapterHole(kind) => {
                    Some(typed_ir::PrincipalElaborationIncompleteReason::MissingAdapterHole(*kind))
                }
                typed_ir::PrincipalElaborationIncompleteReason::HandlerBoundaryWithoutPlan => {
                    Some(typed_ir::PrincipalElaborationIncompleteReason::HandlerBoundaryWithoutPlan)
                }
                _ => None,
            }),
    );

    plan.substitutions = substitutions
        .into_iter()
        .filter_map(|(var, ty)| {
            (!conflicts.contains(&var)).then_some(typed_ir::TypeSubstitution { var, ty })
        })
        .collect();
    plan.complete = incomplete_reasons.is_empty();
    plan.incomplete_reasons = incomplete_reasons;
    plan
}

fn principal_elaboration_required_vars(
    plan: &typed_ir::PrincipalElaborationPlan,
) -> BTreeSet<typed_ir::TypeVar> {
    let mut vars = BTreeSet::new();
    collect_type_vars(&plan.principal_callee, &mut vars);
    vars
}

fn principal_elaboration_never_usable_vars(
    plan: &typed_ir::PrincipalElaborationPlan,
) -> BTreeSet<typed_ir::TypeVar> {
    let mut usage = BTreeMap::<typed_ir::TypeVar, PrincipalVarUsage>::new();
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
    ty: &typed_ir::Type,
    effect_slot: bool,
    usage: &mut BTreeMap<typed_ir::TypeVar, PrincipalVarUsage>,
) {
    match ty {
        typed_ir::Type::Var(var) => {
            let usage = usage.entry(var.clone()).or_default();
            if effect_slot {
                usage.mark_effect();
            } else {
                usage.mark_value();
            }
        }
        typed_ir::Type::Named { args, .. } => {
            for arg in args {
                collect_principal_type_arg_usage(arg, usage);
            }
        }
        typed_ir::Type::Fun {
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
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => {
            for item in items {
                collect_principal_var_usage(item, effect_slot, usage);
            }
        }
        typed_ir::Type::Record(record) => {
            for field in &record.fields {
                collect_principal_var_usage(&field.value, false, usage);
            }
            if let Some(spread) = &record.spread {
                match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        collect_principal_var_usage(ty, false, usage);
                    }
                }
            }
        }
        typed_ir::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_principal_var_usage(payload, false, usage);
                }
            }
            if let Some(tail) = &variant.tail {
                collect_principal_var_usage(tail, false, usage);
            }
        }
        typed_ir::Type::Row { items, tail } => {
            for item in items {
                match item {
                    typed_ir::Type::Var(var) => {
                        usage.entry(var.clone()).or_default().mark_effect();
                    }
                    typed_ir::Type::Named { args, .. } => {
                        for arg in args {
                            collect_principal_type_arg_usage(arg, usage);
                        }
                    }
                    other => collect_principal_var_usage(other, true, usage),
                }
            }
            collect_principal_var_usage(tail, true, usage);
        }
        typed_ir::Type::Recursive { var, body } => {
            collect_principal_var_usage(body, effect_slot, usage);
            usage.remove(var);
        }
        typed_ir::Type::Unknown | typed_ir::Type::Never | typed_ir::Type::Any => {}
    }
}

fn collect_principal_type_arg_usage(
    arg: &typed_ir::TypeArg,
    usage: &mut BTreeMap<typed_ir::TypeVar, PrincipalVarUsage>,
) {
    match arg {
        typed_ir::TypeArg::Type(ty) => collect_principal_type_arg_type_usage(ty, usage),
        typed_ir::TypeArg::Bounds(bounds) => {
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
    ty: &typed_ir::Type,
    usage: &mut BTreeMap<typed_ir::TypeVar, PrincipalVarUsage>,
) {
    match ty {
        typed_ir::Type::Var(var) => {
            usage.entry(var.clone()).or_default().mark_type_arg();
        }
        typed_ir::Type::Named { args, .. } => {
            for arg in args {
                collect_principal_type_arg_usage(arg, usage);
            }
        }
        typed_ir::Type::Fun {
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
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => {
            for item in items {
                collect_principal_type_arg_type_usage(item, usage);
            }
        }
        typed_ir::Type::Record(record) => {
            for field in &record.fields {
                collect_principal_var_usage(&field.value, false, usage);
            }
            if let Some(spread) = &record.spread {
                match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        collect_principal_var_usage(ty, false, usage);
                    }
                }
            }
        }
        typed_ir::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_principal_var_usage(payload, false, usage);
                }
            }
            if let Some(tail) = &variant.tail {
                collect_principal_var_usage(tail, false, usage);
            }
        }
        typed_ir::Type::Row { items, tail } => {
            for item in items {
                collect_principal_var_usage(item, true, usage);
            }
            collect_principal_var_usage(tail, true, usage);
        }
        typed_ir::Type::Recursive { var, body } => {
            collect_principal_type_arg_type_usage(body, usage);
            usage.remove(var);
        }
        typed_ir::Type::Unknown | typed_ir::Type::Never | typed_ir::Type::Any => {}
    }
}

fn principal_fun_param_at(ty: &typed_ir::Type, index: usize) -> Option<&typed_ir::Type> {
    let mut current = ty;
    for _ in 0..index {
        current = match current {
            typed_ir::Type::Fun { ret, .. } => ret,
            typed_ir::Type::Recursive { body, .. } => body,
            _ => return None,
        };
    }
    match current {
        typed_ir::Type::Fun { param, .. } => Some(param),
        typed_ir::Type::Recursive { body, .. } => principal_fun_param_at(body, 0),
        _ => None,
    }
}

fn principal_fun_result_after_args(
    ty: &typed_ir::Type,
    arg_count: usize,
) -> Option<&typed_ir::Type> {
    let mut current = ty;
    for _ in 0..arg_count {
        current = match current {
            typed_ir::Type::Fun { ret, .. } => ret,
            typed_ir::Type::Recursive { body, .. } => body,
            _ => return None,
        };
    }
    Some(current)
}

fn principal_plan_arg_type(arg: &typed_ir::PrincipalElaborationArg) -> Option<typed_ir::Type> {
    arg.expected_runtime
        .clone()
        .or_else(|| principal_plan_bounds_slot_type(arg.contextual.as_ref(), false))
        .or_else(|| principal_plan_bounds_slot_type(Some(&arg.intrinsic), false))
}

fn principal_plan_result_type(
    result: &typed_ir::PrincipalElaborationResult,
) -> Option<typed_ir::Type> {
    result
        .expected_runtime
        .clone()
        .or_else(|| principal_plan_bounds_slot_type(result.contextual.as_ref(), true))
        .or_else(|| principal_plan_bounds_slot_type(Some(&result.intrinsic), true))
}

fn principal_plan_bounds_slot_type(
    bounds: Option<&typed_ir::TypeBounds>,
    allow_never: bool,
) -> Option<typed_ir::Type> {
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

fn principal_plan_slot_type_usable(ty: &typed_ir::Type, allow_never: bool) -> bool {
    !core_type_is_inference_var(ty)
        && (allow_never || !core_type_is_never(ty))
        && !type_has_vars(ty)
}

fn insert_exact_projected_substitution(
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
    var: typed_ir::TypeVar,
    ty: typed_ir::Type,
) {
    if core_type_contains_top(&ty) {
        return;
    }
    if let Some(existing) = substitutions.get(&var) {
        if core_type_is_never(existing) && !core_type_is_never(&ty) {
            substitutions.insert(var, ty);
        } else if core_type_is_never(&ty) {
            // `Never` is the empty effect when it appears in effect positions.
            // Keep a more informative closed effect if one has already been
            // projected. Value positions do not insert `Never` here.
        } else if core_type_is_top(existing) && !core_type_is_top(&ty) {
            substitutions.insert(var, ty);
        } else if core_type_is_top(&ty) {
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
    existing: &typed_ir::Type,
    incoming: &typed_ir::Type,
) -> Option<typed_ir::Type> {
    if existing == incoming {
        return Some(existing.clone());
    }
    if core_type_is_unknown(existing) || core_type_is_top(existing) {
        return Some(incoming.clone());
    }
    if core_type_is_unknown(incoming) || core_type_is_top(incoming) {
        return Some(existing.clone());
    }
    match (existing, incoming) {
        (
            typed_ir::Type::Named {
                path: existing_path,
                args: existing_args,
            },
            typed_ir::Type::Named {
                path: incoming_path,
                args: incoming_args,
            },
        ) if existing_path == incoming_path && existing_args.len() == incoming_args.len() => {
            let args = existing_args
                .iter()
                .zip(incoming_args)
                .map(|(existing, incoming)| merge_projected_type_arg_precision(existing, incoming))
                .collect::<Option<Vec<_>>>()?;
            Some(typed_ir::Type::Named {
                path: existing_path.clone(),
                args,
            })
        }
        (existing, typed_ir::Type::Union(incoming_items))
            if incoming_items
                .iter()
                .any(|item| merge_projected_type_precision(existing, item).is_some()) =>
        {
            Some(existing.clone())
        }
        (typed_ir::Type::Union(existing_items), incoming)
            if existing_items
                .iter()
                .any(|item| merge_projected_type_precision(item, incoming).is_some()) =>
        {
            Some(incoming.clone())
        }
        (existing, typed_ir::Type::Inter(incoming_items))
            if incoming_items
                .iter()
                .any(|item| merge_projected_type_precision(existing, item).is_some()) =>
        {
            Some(existing.clone())
        }
        (typed_ir::Type::Inter(existing_items), incoming)
            if existing_items
                .iter()
                .any(|item| merge_projected_type_precision(item, incoming).is_some()) =>
        {
            Some(incoming.clone())
        }
        (typed_ir::Type::Tuple(existing_items), typed_ir::Type::Tuple(incoming_items))
            if existing_items.len() == incoming_items.len() =>
        {
            let items = existing_items
                .iter()
                .zip(incoming_items)
                .map(|(existing, incoming)| merge_projected_type_precision(existing, incoming))
                .collect::<Option<Vec<_>>>()?;
            Some(typed_ir::Type::Tuple(items))
        }
        (
            typed_ir::Type::Fun {
                param: existing_param,
                param_effect: existing_param_effect,
                ret_effect: existing_ret_effect,
                ret: existing_ret,
            },
            typed_ir::Type::Fun {
                param: incoming_param,
                param_effect: incoming_param_effect,
                ret_effect: incoming_ret_effect,
                ret: incoming_ret,
            },
        ) => Some(typed_ir::Type::Fun {
            param: Box::new(merge_projected_type_precision(
                existing_param,
                incoming_param,
            )?),
            param_effect: Box::new(merge_projected_effect_precision(
                existing_param_effect,
                incoming_param_effect,
            )?),
            ret_effect: Box::new(merge_projected_effect_precision(
                existing_ret_effect,
                incoming_ret_effect,
            )?),
            ret: Box::new(merge_projected_type_precision(existing_ret, incoming_ret)?),
        }),
        _ => None,
    }
}

fn merge_projected_effect_precision(
    existing: &typed_ir::Type,
    incoming: &typed_ir::Type,
) -> Option<typed_ir::Type> {
    match (existing, incoming) {
        (existing, incoming) if core_type_is_never(existing) => Some(incoming.clone()),
        (existing, incoming) if core_type_is_never(incoming) => Some(existing.clone()),
        _ => merge_projected_effect_rows(existing, incoming)
            .or_else(|| merge_projected_type_precision(existing, incoming)),
    }
}

fn merge_projected_type_arg_precision(
    existing: &typed_ir::TypeArg,
    incoming: &typed_ir::TypeArg,
) -> Option<typed_ir::TypeArg> {
    match (existing, incoming) {
        (typed_ir::TypeArg::Type(existing), typed_ir::TypeArg::Type(incoming)) => Some(
            typed_ir::TypeArg::Type(merge_projected_type_precision(existing, incoming)?),
        ),
        (typed_ir::TypeArg::Bounds(existing), typed_ir::TypeArg::Bounds(incoming)) => Some(
            typed_ir::TypeArg::Bounds(merge_projected_bounds_precision(existing, incoming)?),
        ),
        (typed_ir::TypeArg::Bounds(existing), typed_ir::TypeArg::Type(incoming))
        | (typed_ir::TypeArg::Type(incoming), typed_ir::TypeArg::Bounds(existing)) => {
            let existing = principal_plan_bounds_single_closed_type(existing, false)?;
            Some(typed_ir::TypeArg::Type(merge_projected_type_precision(
                &existing, incoming,
            )?))
        }
    }
}

fn merge_projected_bounds_precision(
    existing: &typed_ir::TypeBounds,
    incoming: &typed_ir::TypeBounds,
) -> Option<typed_ir::TypeBounds> {
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
    Some(typed_ir::TypeBounds { lower, upper })
}

fn normalize_projected_substitution_type(
    ty: &typed_ir::Type,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> typed_ir::Type {
    normalize_projected_runtime_shape(collapse_repeated_top_choice_type(substitute_type(
        ty,
        substitutions,
    )))
}

fn normalize_projected_runtime_shape(ty: typed_ir::Type) -> typed_ir::Type {
    match ty {
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => typed_ir::Type::Fun {
            param: Box::new(normalize_projected_runtime_shape(*param)),
            param_effect: Box::new(normalize_projected_effect_shape(*param_effect)),
            ret_effect: Box::new(normalize_projected_effect_shape(*ret_effect)),
            ret: Box::new(normalize_projected_runtime_shape(*ret)),
        },
        typed_ir::Type::Named { path, args } => typed_ir::Type::Named {
            path,
            args: args
                .into_iter()
                .map(normalize_projected_runtime_shape_arg)
                .collect(),
        },
        typed_ir::Type::Tuple(items) => typed_ir::Type::Tuple(
            items
                .into_iter()
                .map(normalize_projected_runtime_shape)
                .collect(),
        ),
        typed_ir::Type::Record(record) => typed_ir::Type::Record(typed_ir::RecordType {
            fields: record
                .fields
                .into_iter()
                .map(|field| typed_ir::RecordField {
                    name: field.name,
                    value: normalize_projected_runtime_shape(field.value),
                    optional: field.optional,
                })
                .collect(),
            spread: record.spread.map(|spread| match spread {
                typed_ir::RecordSpread::Head(ty) => {
                    typed_ir::RecordSpread::Head(Box::new(normalize_projected_runtime_shape(*ty)))
                }
                typed_ir::RecordSpread::Tail(ty) => {
                    typed_ir::RecordSpread::Tail(Box::new(normalize_projected_runtime_shape(*ty)))
                }
            }),
        }),
        typed_ir::Type::Variant(variant) => typed_ir::Type::Variant(typed_ir::VariantType {
            cases: variant
                .cases
                .into_iter()
                .map(|case| typed_ir::VariantCase {
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
        typed_ir::Type::Union(items) => typed_ir::Type::Union(
            items
                .into_iter()
                .map(normalize_projected_runtime_shape)
                .collect(),
        ),
        typed_ir::Type::Inter(items) => typed_ir::Type::Inter(
            items
                .into_iter()
                .map(normalize_projected_runtime_shape)
                .collect(),
        ),
        typed_ir::Type::Row { items, tail } => normalize_projected_effect_row_shape(items, *tail),
        typed_ir::Type::Recursive { var, body } => typed_ir::Type::Recursive {
            var,
            body: Box::new(normalize_projected_runtime_shape(*body)),
        },
        other => other,
    }
}

fn normalize_projected_effect_shape(ty: typed_ir::Type) -> typed_ir::Type {
    match ty {
        typed_ir::Type::Unknown => typed_ir::Type::Never,
        typed_ir::Type::Row { items, tail } => normalize_projected_effect_row_shape(items, *tail),
        typed_ir::Type::Named { path, args } => normalize_projected_effect_atom_shape(path, args),
        typed_ir::Type::Never | typed_ir::Type::Any | typed_ir::Type::Var(_) => ty,
        _ => typed_ir::Type::Never,
    }
}

fn normalize_projected_effect_row_shape(
    items: Vec<typed_ir::Type>,
    tail: typed_ir::Type,
) -> typed_ir::Type {
    let tail = match normalize_projected_effect_shape(tail) {
        typed_ir::Type::Row {
            items: nested_items,
            tail: nested_tail,
        } if nested_items.is_empty() => *nested_tail,
        typed_ir::Type::Row { items, tail } => typed_ir::Type::Row { items, tail },
        tail @ (typed_ir::Type::Never
        | typed_ir::Type::Any
        | typed_ir::Type::Unknown
        | typed_ir::Type::Var(_)) => tail,
        _ => typed_ir::Type::Never,
    };
    typed_ir::Type::Row {
        items: items
            .into_iter()
            .map(normalize_projected_effect_shape)
            .filter(|item| !effect_is_empty(item))
            .collect(),
        tail: Box::new(tail),
    }
}

fn normalize_projected_effect_atom_shape(
    path: typed_ir::Path,
    args: Vec<typed_ir::TypeArg>,
) -> typed_ir::Type {
    typed_ir::Type::Named {
        args: if is_synthetic_var_effect_path(&path) {
            Vec::new()
        } else {
            args.into_iter()
                .map(normalize_projected_runtime_shape_arg)
                .collect()
        },
        path,
    }
}

fn normalize_projected_runtime_shape_arg(arg: typed_ir::TypeArg) -> typed_ir::TypeArg {
    match arg {
        typed_ir::TypeArg::Type(ty) => {
            typed_ir::TypeArg::Type(normalize_projected_runtime_shape(ty))
        }
        typed_ir::TypeArg::Bounds(bounds) => typed_ir::TypeArg::Bounds(typed_ir::TypeBounds {
            lower: bounds
                .lower
                .map(|ty| Box::new(normalize_projected_runtime_shape(*ty))),
            upper: bounds
                .upper
                .map(|ty| Box::new(normalize_projected_runtime_shape(*ty))),
        }),
    }
}

fn collapse_repeated_top_choice_type(ty: typed_ir::Type) -> typed_ir::Type {
    match ty {
        typed_ir::Type::Union(items) => {
            collapse_repeated_top_choice_items(items, typed_ir::Type::Union)
        }
        typed_ir::Type::Inter(items) => {
            collapse_repeated_top_choice_items(items, typed_ir::Type::Inter)
        }
        other => other,
    }
}

fn collapse_repeated_top_choice_items(
    items: Vec<typed_ir::Type>,
    rebuild: impl FnOnce(Vec<typed_ir::Type>) -> typed_ir::Type,
) -> typed_ir::Type {
    let mut unique = Vec::<typed_ir::Type>::new();
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
    left: &typed_ir::Type,
    right: &typed_ir::Type,
) -> Option<typed_ir::Type> {
    if !matches!(left, typed_ir::Type::Row { .. }) && !matches!(right, typed_ir::Type::Row { .. }) {
        return None;
    }
    let (mut items, left_tail) = projected_effect_row_parts(left.clone());
    let (right_items, right_tail) = projected_effect_row_parts(right.clone());
    for item in right_items {
        if !core_type_is_never(&item) && !items.iter().any(|existing| existing == &item) {
            items.push(item);
        }
    }
    let tail = if core_type_is_never(&left_tail) || left_tail == right_tail {
        right_tail
    } else if core_type_is_never(&right_tail) {
        left_tail
    } else {
        typed_ir::Type::Union(vec![left_tail, right_tail])
    };
    if items.is_empty() {
        return Some(tail);
    }
    Some(typed_ir::Type::Row {
        items,
        tail: Box::new(tail),
    })
}

fn projected_effect_row_parts(effect: typed_ir::Type) -> (Vec<typed_ir::Type>, typed_ir::Type) {
    match normalize_projected_effect_shape(effect) {
        typed_ir::Type::Never => (Vec::new(), typed_ir::Type::Never),
        typed_ir::Type::Row { items, tail } => (items, *tail),
        other => (vec![other], typed_ir::Type::Never),
    }
}

fn project_substitutions_from_candidates(
    candidates: &[typed_ir::PrincipalSubstitutionCandidate],
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
) {
    let mut by_var = BTreeMap::<
        typed_ir::TypeVar,
        Vec<(typed_ir::PrincipalCandidateRelation, typed_ir::Type)>,
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
        if let Some(existing) = substitutions.get(&var) {
            if candidates
                .iter()
                .any(|(relation, ty)| !substitution_satisfies_candidate(existing, *relation, ty))
            {
                conflicts.insert(var);
            }
            continue;
        }
        if conflicts.contains(&var) {
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
                    matches!(relation, typed_ir::PrincipalCandidateRelation::Exact)
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
                    matches!(relation, typed_ir::PrincipalCandidateRelation::Lower)
                })
                .map(|(_, ty)| ty),
        );
        let upper = unique_candidate_type(
            candidates
                .iter()
                .filter(|(relation, _)| {
                    matches!(relation, typed_ir::PrincipalCandidateRelation::Upper)
                })
                .map(|(_, ty)| ty),
        );
        if let Some(lower) = effect_residual_candidate_from_upper_bounds(&lower, &candidates) {
            insert_exact_projected_substitution(substitutions, conflicts, var, lower);
            continue;
        }
        if let (CandidateTypeChoice::One(lower), CandidateTypeChoice::One(upper)) = (lower, upper)
            && lower == upper
        {
            insert_exact_projected_substitution(substitutions, conflicts, var, lower);
        }
    }
}

fn effect_residual_candidate_from_upper_bounds(
    lower: &CandidateTypeChoice,
    candidates: &[(typed_ir::PrincipalCandidateRelation, typed_ir::Type)],
) -> Option<typed_ir::Type> {
    let CandidateTypeChoice::One(lower) = lower else {
        return None;
    };
    let lower_atoms = effect_candidate_atoms(lower)?;
    if lower_atoms.is_empty() {
        return None;
    }
    if !lower_atoms.iter().any(is_synthetic_var_effect_atom) {
        return None;
    }

    let mut saw_concrete_upper = false;
    for (relation, upper) in candidates {
        if !matches!(relation, typed_ir::PrincipalCandidateRelation::Upper) {
            continue;
        }
        if core_type_is_unknown(upper) || core_type_is_top(upper) {
            continue;
        }
        saw_concrete_upper = true;
        let upper_atoms = effect_candidate_atoms(upper)?;
        if !lower_atoms
            .iter()
            .all(|atom| upper_atoms.iter().any(|upper_atom| upper_atom == atom))
        {
            return None;
        }
    }

    saw_concrete_upper.then(|| lower.clone())
}

fn is_synthetic_var_effect_atom(ty: &typed_ir::Type) -> bool {
    matches!(ty, typed_ir::Type::Named { path, .. } if is_synthetic_var_effect_path(path))
}

fn effect_candidate_atoms(ty: &typed_ir::Type) -> Option<Vec<typed_ir::Type>> {
    let mut atoms = Vec::new();
    collect_effect_candidate_atoms(ty, &mut atoms).then_some(atoms)
}

fn collect_effect_candidate_atoms(ty: &typed_ir::Type, out: &mut Vec<typed_ir::Type>) -> bool {
    match ty {
        typed_ir::Type::Named { path, args } => {
            let atom = normalize_projected_effect_atom_shape(path.clone(), args.clone());
            if !principal_plan_substitution_type_usable(&atom, false) {
                return false;
            }
            if !out.iter().any(|existing| existing == &atom) {
                out.push(atom);
            }
            true
        }
        typed_ir::Type::Row { items, tail } => {
            items
                .iter()
                .all(|item| collect_effect_candidate_atoms(item, out))
                && collect_effect_candidate_atoms(tail, out)
        }
        typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => items
            .iter()
            .all(|item| collect_effect_candidate_atoms(item, out)),
        typed_ir::Type::Never | typed_ir::Type::Unknown => true,
        _ => false,
    }
}

fn substitution_satisfies_candidate(
    substitution: &typed_ir::Type,
    relation: typed_ir::PrincipalCandidateRelation,
    candidate: &typed_ir::Type,
) -> bool {
    match relation {
        typed_ir::PrincipalCandidateRelation::Exact => {
            type_compatible(substitution, candidate) && type_compatible(candidate, substitution)
        }
        typed_ir::PrincipalCandidateRelation::Lower => type_compatible(substitution, candidate),
        typed_ir::PrincipalCandidateRelation::Upper => type_compatible(candidate, substitution),
    }
}

fn unique_owned_candidate_type(
    candidates: impl Iterator<Item = typed_ir::Type>,
) -> CandidateTypeChoice {
    let mut choice: Option<typed_ir::Type> = None;
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
    var: &typed_ir::TypeVar,
    ty: &typed_ir::Type,
) -> Option<typed_ir::Type> {
    let items = match ty {
        typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => items,
        _ => return None,
    };
    let mut closed = None::<typed_ir::Type>;
    for item in items {
        if matches!(item, typed_ir::Type::Var(item_var) if item_var == var) {
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
    requirements: &[typed_ir::RoleRequirement],
    role_impls: &[typed_ir::RoleImplGraphNode],
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
) {
    project_principal_substitutions_until_stable(
        substitutions,
        conflicts,
        |substitutions, conflicts| {
            for requirement in requirements {
                let inputs = requirement
                    .args
                    .iter()
                    .filter_map(|arg| match arg {
                        typed_ir::RoleRequirementArg::Input(bounds) => {
                            let bounds = substitute_bounds(bounds.clone(), substitutions);
                            principal_plan_bounds_slot_type(Some(&bounds), false)
                        }
                        typed_ir::RoleRequirementArg::Associated { .. } => None,
                    })
                    .collect::<Vec<_>>();
                if inputs.is_empty() {
                    continue;
                }
                for associated in requirement.args.iter().filter_map(requirement_associated) {
                    if let Some(resolved) = resolve_associated_requirement_from_impls(
                        requirement,
                        associated.0,
                        &inputs,
                        role_impls,
                    ) {
                        project_associated_substitution(
                            associated,
                            &resolved,
                            params,
                            substitutions,
                            conflicts,
                        );
                    }
                }
            }
        },
    );
}

fn project_associated_substitution(
    associated: (&typed_ir::Name, &typed_ir::TypeBounds),
    item: &typed_ir::Type,
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
) {
    let (_, bounds) = associated;
    if !principal_plan_substitution_type_usable(item, false) {
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

fn resolve_associated_requirement_from_impls(
    requirement: &typed_ir::RoleRequirement,
    name: &typed_ir::Name,
    inputs: &[typed_ir::Type],
    role_impls: &[typed_ir::RoleImplGraphNode],
) -> Option<typed_ir::Type> {
    let mut resolved = None;
    for role_impl in role_impls.iter().filter(|role_impl| {
        role_impl.role == requirement.role && role_impl.inputs.len() == inputs.len()
    }) {
        let Some(associated) = role_impl
            .associated_types
            .iter()
            .find(|associated| associated.name == *name)
        else {
            continue;
        };
        let Some(candidate) =
            project_role_impl_associated_type(&role_impl.inputs, inputs, &associated.value)
        else {
            continue;
        };
        match &resolved {
            Some(existing) if existing != &candidate => return None,
            Some(_) => {}
            None => resolved = Some(candidate),
        }
    }
    resolved
}

fn project_role_impl_associated_type(
    impl_inputs: &[typed_ir::TypeBounds],
    actual_inputs: &[typed_ir::Type],
    associated: &typed_ir::TypeBounds,
) -> Option<typed_ir::Type> {
    let mut impl_vars = BTreeSet::new();
    let templates = impl_inputs
        .iter()
        .map(|bounds| {
            let template = principal_plan_bounds_slot_type(Some(bounds), false)?;
            collect_type_vars(&template, &mut impl_vars);
            Some(template)
        })
        .collect::<Option<Vec<_>>>()?;
    collect_type_bounds_vars(associated, &mut impl_vars);
    let mut substitutions = BTreeMap::new();
    let mut conflicts = BTreeSet::new();
    for (template, actual) in templates.iter().zip(actual_inputs) {
        project_closed_substitutions_from_type(
            template,
            actual,
            &impl_vars,
            &mut substitutions,
            &mut conflicts,
            false,
            32,
        );
    }
    if !conflicts.is_empty() {
        return None;
    }
    principal_plan_bounds_slot_type(
        Some(&substitute_bounds(associated.clone(), &substitutions)),
        false,
    )
}

fn collect_type_bounds_vars(bounds: &typed_ir::TypeBounds, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    if let Some(lower) = bounds.lower.as_deref() {
        collect_type_vars(lower, vars);
    }
    if let Some(upper) = bounds.upper.as_deref() {
        collect_type_vars(upper, vars);
    }
}

fn requirement_associated(
    arg: &typed_ir::RoleRequirementArg,
) -> Option<(&typed_ir::Name, &typed_ir::TypeBounds)> {
    match arg {
        typed_ir::RoleRequirementArg::Associated { name, bounds } => Some((name, bounds)),
        typed_ir::RoleRequirementArg::Input(_) => None,
    }
}

enum CandidateTypeChoice {
    None,
    One(typed_ir::Type),
    Conflict,
}

fn unique_candidate_type<'a>(
    candidates: impl Iterator<Item = &'a typed_ir::Type>,
) -> CandidateTypeChoice {
    let mut choice: Option<typed_ir::Type> = None;
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
    template: &typed_ir::Type,
    actual: &typed_ir::Type,
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
    allow_never: bool,
    depth: usize,
) {
    if depth == 0 {
        debug_assert!(false, "type substitution inference depth exhausted");
        return;
    }
    match (template, actual) {
        (typed_ir::Type::Var(var), actual) if params.contains(var) => {
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
            typed_ir::Type::Named { path, args },
            typed_ir::Type::Named {
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
            typed_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            },
            typed_ir::Type::Fun {
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
        (typed_ir::Type::Tuple(items), typed_ir::Type::Tuple(actual_items))
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
        (typed_ir::Type::Record(record), typed_ir::Type::Record(actual_record)) => {
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
        (typed_ir::Type::Variant(variant), typed_ir::Type::Variant(actual_variant)) => {
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
        (typed_ir::Type::Union(items) | typed_ir::Type::Inter(items), actual)
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
            typed_ir::Type::Row { items, tail },
            typed_ir::Type::Row {
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
        (typed_ir::Type::Row { items, tail }, actual) if allow_never => {
            project_closed_effect_row_substitutions(
                items,
                tail,
                std::slice::from_ref(actual),
                &typed_ir::Type::Never,
                params,
                substitutions,
                conflicts,
                depth - 1,
            );
        }
        (typed_ir::Type::Recursive { body, .. }, actual) => {
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
        (template, typed_ir::Type::Recursive { body, .. }) => {
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
    template: &typed_ir::Type,
    actual: &typed_ir::Type,
    allow_never: bool,
) -> bool {
    match (template, actual) {
        (template, _) if principal_substitution_type_is_open_default(template) => false,
        (_, actual) if core_type_is_unknown(actual) || core_type_is_top(actual) => false,
        (_, actual) if core_type_is_never(actual) => allow_never && core_type_is_never(template),
        (template, _) if core_type_is_never(template) => false,
        (
            typed_ir::Type::Named { path, args },
            typed_ir::Type::Named {
                path: actual_path,
                args: actual_args,
            },
        ) => path == actual_path && args.len() == actual_args.len(),
        (typed_ir::Type::Fun { .. }, typed_ir::Type::Fun { .. }) => true,
        (typed_ir::Type::Tuple(items), typed_ir::Type::Tuple(actual_items)) => {
            items.len() == actual_items.len()
        }
        (typed_ir::Type::Record(_), typed_ir::Type::Record(_)) => true,
        (typed_ir::Type::Variant(_), typed_ir::Type::Variant(_)) => true,
        (typed_ir::Type::Row { .. }, typed_ir::Type::Row { .. }) => true,
        (typed_ir::Type::Row { .. }, _) => allow_never,
        (typed_ir::Type::Recursive { body, .. }, actual) => {
            projection_choice_item_matches_actual(body, actual, allow_never)
        }
        (template, typed_ir::Type::Recursive { body, .. }) => {
            projection_choice_item_matches_actual(template, body, allow_never)
        }
        (template, actual) => template == actual,
    }
}

pub(crate) fn project_closed_substitutions_from_type_bounds(
    template: &typed_ir::Type,
    actual: &typed_ir::TypeBounds,
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
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
    template_items: &[typed_ir::Type],
    template_tail: &typed_ir::Type,
    actual_items: &[typed_ir::Type],
    actual_tail: &typed_ir::Type,
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
    depth: usize,
) {
    if depth == 0 {
        return;
    }
    let mut matched_actual = vec![false; actual_items.len()];
    let mut row_vars = Vec::new();

    for template in template_items {
        match template {
            typed_ir::Type::Var(var) if params.contains(var) => row_vars.push(var.clone()),
            _ => {
                for (index, actual) in actual_items.iter().enumerate() {
                    if matched_actual[index] || !same_effect_item(template, actual) {
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
    let residual = normalize_projected_effect_shape(effect_row_from_items_and_tail(
        residual_items,
        actual_tail.clone(),
    ));

    if let [var] = row_vars.as_slice() {
        if principal_plan_substitution_type_usable(&residual, true) {
            insert_exact_projected_substitution(
                substitutions,
                conflicts,
                var.clone(),
                residual.clone(),
            );
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
    template: &typed_ir::TypeArg,
    actual: &typed_ir::TypeArg,
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
    _allow_never: bool,
    depth: usize,
) {
    match (template, actual) {
        (typed_ir::TypeArg::Type(template), typed_ir::TypeArg::Type(actual)) => {
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
        (typed_ir::TypeArg::Type(template), typed_ir::TypeArg::Bounds(actual)) => {
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
        (typed_ir::TypeArg::Bounds(template), typed_ir::TypeArg::Type(actual)) => {
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
        (typed_ir::TypeArg::Bounds(template), typed_ir::TypeArg::Bounds(actual)) => {
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
    template: &typed_ir::TypeBounds,
    actual: &typed_ir::Type,
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
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
    template: &typed_ir::Type,
    actual: &typed_ir::Type,
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
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
        (BoundChoicePolarity::Lower, typed_ir::Type::Union(items)) => {
            for item in items {
                if let typed_ir::Type::Var(var) = item
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
        (BoundChoicePolarity::Lower, typed_ir::Type::Inter(items))
        | (BoundChoicePolarity::Upper, typed_ir::Type::Union(items))
        | (BoundChoicePolarity::Upper, typed_ir::Type::Inter(items)) => {
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
        (_, typed_ir::Type::Recursive { body, .. }) => {
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
    bounds: &typed_ir::TypeBounds,
    allow_never: bool,
) -> Option<typed_ir::Type> {
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

fn normalize_projected_closed_choice_type(ty: typed_ir::Type) -> typed_ir::Type {
    collapse_repeated_top_choice_type(collapse_single_bound_type_args(
        normalize_projected_runtime_shape(ty),
    ))
}

fn collapse_single_bound_type_args(ty: typed_ir::Type) -> typed_ir::Type {
    match ty {
        typed_ir::Type::Named { path, args } => typed_ir::Type::Named {
            path,
            args: args
                .into_iter()
                .map(collapse_single_bound_type_arg)
                .collect(),
        },
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => typed_ir::Type::Fun {
            param: Box::new(collapse_single_bound_type_args(*param)),
            param_effect: Box::new(collapse_single_bound_type_args(*param_effect)),
            ret_effect: Box::new(collapse_single_bound_type_args(*ret_effect)),
            ret: Box::new(collapse_single_bound_type_args(*ret)),
        },
        typed_ir::Type::Tuple(items) => typed_ir::Type::Tuple(
            items
                .into_iter()
                .map(collapse_single_bound_type_args)
                .collect(),
        ),
        typed_ir::Type::Record(record) => typed_ir::Type::Record(typed_ir::RecordType {
            fields: record
                .fields
                .into_iter()
                .map(|field| typed_ir::RecordField {
                    name: field.name,
                    value: collapse_single_bound_type_args(field.value),
                    optional: field.optional,
                })
                .collect(),
            spread: record.spread.map(|spread| match spread {
                typed_ir::RecordSpread::Head(ty) => {
                    typed_ir::RecordSpread::Head(Box::new(collapse_single_bound_type_args(*ty)))
                }
                typed_ir::RecordSpread::Tail(ty) => {
                    typed_ir::RecordSpread::Tail(Box::new(collapse_single_bound_type_args(*ty)))
                }
            }),
        }),
        typed_ir::Type::Variant(variant) => typed_ir::Type::Variant(typed_ir::VariantType {
            cases: variant
                .cases
                .into_iter()
                .map(|case| typed_ir::VariantCase {
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
        typed_ir::Type::Union(items) => typed_ir::Type::Union(
            items
                .into_iter()
                .map(collapse_single_bound_type_args)
                .collect(),
        ),
        typed_ir::Type::Inter(items) => typed_ir::Type::Inter(
            items
                .into_iter()
                .map(collapse_single_bound_type_args)
                .collect(),
        ),
        typed_ir::Type::Row { items, tail } => typed_ir::Type::Row {
            items: items
                .into_iter()
                .map(collapse_single_bound_type_args)
                .collect(),
            tail: Box::new(collapse_single_bound_type_args(*tail)),
        },
        typed_ir::Type::Recursive { var, body } => typed_ir::Type::Recursive {
            var,
            body: Box::new(collapse_single_bound_type_args(*body)),
        },
        other => other,
    }
}

fn collapse_single_bound_type_arg(arg: typed_ir::TypeArg) -> typed_ir::TypeArg {
    match arg {
        typed_ir::TypeArg::Type(ty) => typed_ir::TypeArg::Type(collapse_single_bound_type_args(ty)),
        typed_ir::TypeArg::Bounds(bounds) => {
            let bounds = typed_ir::TypeBounds {
                lower: bounds
                    .lower
                    .map(|ty| Box::new(collapse_single_bound_type_args(*ty))),
                upper: bounds
                    .upper
                    .map(|ty| Box::new(collapse_single_bound_type_args(*ty))),
            };
            principal_plan_bounds_single_closed_type(&bounds, false)
                .map(typed_ir::TypeArg::Type)
                .unwrap_or(typed_ir::TypeArg::Bounds(bounds))
        }
    }
}

fn principal_plan_substitution_type_usable(ty: &typed_ir::Type, allow_never: bool) -> bool {
    if principal_plan_function_slot_usable(ty, allow_never) {
        return true;
    }
    !principal_substitution_type_is_open_default(ty)
        && (allow_never || !core_type_is_never(ty))
        && !type_has_vars(ty)
        && !core_type_contains_top(ty)
        && (allow_never || !core_type_contains_unknown(ty))
}

fn principal_substitution_type_is_open_default(ty: &typed_ir::Type) -> bool {
    core_type_is_unknown(ty) || core_type_is_top(ty) || core_type_is_inference_var(ty)
}

fn principal_plan_function_slot_usable(ty: &typed_ir::Type, allow_never: bool) -> bool {
    let mut current = ty;
    let mut has_function_spine = false;
    while let typed_ir::Type::Fun {
        param,
        param_effect,
        ret_effect,
        ret,
    } = current
    {
        has_function_spine = true;
        if type_has_vars(param)
            || type_has_vars(param_effect)
            || type_has_vars(ret_effect)
            || core_type_contains_top(param)
            || core_type_contains_top(param_effect)
            || core_type_contains_top(ret_effect)
        {
            return false;
        }
        current = ret;
    }
    has_function_spine
        && !type_has_vars(current)
        && !core_type_contains_top(current)
        && (allow_never || !core_type_is_never(current))
}

pub(crate) fn substitute_join_evidence(
    evidence: JoinEvidence,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> JoinEvidence {
    JoinEvidence {
        result: substitute_type(&evidence.result, substitutions),
    }
}

pub(crate) fn substitute_bounds(
    bounds: typed_ir::TypeBounds,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> typed_ir::TypeBounds {
    typed_ir::TypeBounds {
        lower: bounds
            .lower
            .map(|lower| Box::new(substitute_type(&lower, substitutions))),
        upper: bounds
            .upper
            .map(|upper| Box::new(substitute_type(&upper, substitutions))),
    }
}

pub(super) fn infer_type_substitutions_inner(
    template: &typed_ir::Type,
    actual: &typed_ir::Type,
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    depth: usize,
    options: TypeSubstitutionInferOptions,
) {
    if depth == 0 {
        return;
    }
    match (template, actual) {
        (typed_ir::Type::Var(var), actual) if params.contains(var) => {
            insert_substitution(
                substitutions,
                var.clone(),
                actual.clone(),
                options.prefer_non_never,
            );
        }
        (
            typed_ir::Type::Named { path, args },
            typed_ir::Type::Named {
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
                    options,
                );
            }
        }
        (
            typed_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            },
            typed_ir::Type::Fun {
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
                options,
            );
            if options.include_function_effects {
                infer_type_substitutions_inner(
                    param_effect,
                    actual_param_effect,
                    params,
                    substitutions,
                    depth - 1,
                    options,
                );
                infer_type_substitutions_inner(
                    ret_effect,
                    actual_ret_effect,
                    params,
                    substitutions,
                    depth - 1,
                    options,
                );
            }
            infer_type_substitutions_inner(
                ret,
                actual_ret,
                params,
                substitutions,
                depth - 1,
                options,
            );
        }
        (typed_ir::Type::Tuple(items), typed_ir::Type::Tuple(actual_items))
            if items.len() == actual_items.len() =>
        {
            for (item, actual_item) in items.iter().zip(actual_items) {
                infer_type_substitutions_inner(
                    item,
                    actual_item,
                    params,
                    substitutions,
                    depth - 1,
                    options,
                );
            }
        }
        (typed_ir::Type::Union(items) | typed_ir::Type::Inter(items), actual) => {
            for item in items {
                if !inference_choice_item_matches_actual(item, actual) {
                    continue;
                }
                infer_type_substitutions_inner(
                    item,
                    actual,
                    params,
                    substitutions,
                    depth - 1,
                    options,
                );
            }
        }
        (typed_ir::Type::Record(record), typed_ir::Type::Record(actual_record)) => {
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
                        options,
                    );
                }
            }
        }
        (
            typed_ir::Type::Row { items, tail },
            typed_ir::Type::Row {
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
                options,
            );
        }
        (typed_ir::Type::Row { items, tail }, actual) => {
            infer_effect_row_substitutions(
                items,
                tail,
                std::slice::from_ref(actual),
                &typed_ir::Type::Never,
                params,
                substitutions,
                depth - 1,
                options,
            );
        }
        (typed_ir::Type::Variant(variant), typed_ir::Type::Variant(actual_variant)) => {
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
                            options,
                        );
                    }
                }
            }
        }
        (typed_ir::Type::Recursive { body, .. }, actual) => {
            infer_type_substitutions_inner(body, actual, params, substitutions, depth - 1, options);
        }
        (template, typed_ir::Type::Recursive { body, .. }) => {
            infer_type_substitutions_inner(
                template,
                body,
                params,
                substitutions,
                depth - 1,
                options,
            );
        }
        _ => {}
    }
}

fn inference_choice_item_matches_actual(
    template: &typed_ir::Type,
    actual: &typed_ir::Type,
) -> bool {
    match (template, actual) {
        (template, _) if principal_substitution_type_is_open_default(template) => false,
        (_, actual) if core_type_is_unknown(actual) || core_type_is_top(actual) => false,
        (_, actual) if core_type_is_never(actual) => false,
        (template, _) if core_type_is_never(template) => false,
        (
            typed_ir::Type::Named { path, args },
            typed_ir::Type::Named {
                path: actual_path,
                args: actual_args,
            },
        ) => path == actual_path && args.len() == actual_args.len(),
        (typed_ir::Type::Fun { .. }, typed_ir::Type::Fun { .. }) => true,
        (typed_ir::Type::Tuple(items), typed_ir::Type::Tuple(actual_items)) => {
            items.len() == actual_items.len()
        }
        (typed_ir::Type::Record(_), typed_ir::Type::Record(_)) => true,
        (typed_ir::Type::Variant(_), typed_ir::Type::Variant(_)) => true,
        (typed_ir::Type::Row { .. }, typed_ir::Type::Row { .. }) => true,
        (typed_ir::Type::Recursive { body, .. }, actual) => {
            inference_choice_item_matches_actual(body, actual)
        }
        (template, typed_ir::Type::Recursive { body, .. }) => {
            inference_choice_item_matches_actual(template, body)
        }
        (template, actual) => template == actual,
    }
}

pub(super) fn infer_effect_row_substitutions(
    template_items: &[typed_ir::Type],
    template_tail: &typed_ir::Type,
    actual_items: &[typed_ir::Type],
    actual_tail: &typed_ir::Type,
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    depth: usize,
    options: TypeSubstitutionInferOptions,
) {
    let mut matched_actual = vec![false; actual_items.len()];
    let mut row_vars = Vec::new();

    for template in template_items {
        match template {
            typed_ir::Type::Var(var) if params.contains(var) => {
                row_vars.push(var.clone());
            }
            _ => {
                for (index, actual) in actual_items.iter().enumerate() {
                    if matched_actual[index] || !same_effect_item(template, actual) {
                        continue;
                    }
                    infer_type_substitutions_inner(
                        template,
                        actual,
                        params,
                        substitutions,
                        depth,
                        options,
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

    if let [var] = row_vars.as_slice() {
        if !(options.skip_empty_effect_residual && effect_is_empty(&residual)) {
            insert_substitution(
                substitutions,
                var.clone(),
                residual.clone(),
                options.prefer_non_never,
            );
        }
    }
    if options.skip_empty_effect_residual && effect_is_empty(&residual) {
        return;
    }
    infer_type_substitutions_inner(
        template_tail,
        &residual,
        params,
        substitutions,
        depth,
        options,
    );
}

pub(crate) fn same_effect_head(left: &typed_ir::Type, right: &typed_ir::Type) -> bool {
    match (left, right) {
        (
            typed_ir::Type::Named { path, .. },
            typed_ir::Type::Named {
                path: actual_path, ..
            },
        ) => effect_paths_match(path, actual_path),
        _ => false,
    }
}

fn same_effect_item(left: &typed_ir::Type, right: &typed_ir::Type) -> bool {
    match (left, right) {
        (
            typed_ir::Type::Named { path, args },
            typed_ir::Type::Named {
                path: actual_path,
                args: actual_args,
            },
        ) => {
            effect_paths_match(path, actual_path)
                && args.len() == actual_args.len()
                && args.iter().zip(actual_args).all(|(left, right)| {
                    type_arg_compatible(left, right, 128) && type_arg_compatible(right, left, 128)
                })
        }
        _ => false,
    }
}

pub(super) fn effect_row_from_items_and_tail(
    items: Vec<typed_ir::Type>,
    tail: typed_ir::Type,
) -> typed_ir::Type {
    if items.is_empty() {
        return tail;
    }
    if effect_is_empty(&tail) && items.len() == 1 {
        return items.into_iter().next().unwrap();
    }
    typed_ir::Type::Row {
        items,
        tail: Box::new(tail),
    }
}

pub(super) fn infer_type_arg_substitutions(
    template: &typed_ir::TypeArg,
    actual: &typed_ir::TypeArg,
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    depth: usize,
    options: TypeSubstitutionInferOptions,
) {
    match (template, actual) {
        (typed_ir::TypeArg::Type(template), typed_ir::TypeArg::Type(actual)) => {
            infer_type_substitutions_inner(template, actual, params, substitutions, depth, options);
        }
        (typed_ir::TypeArg::Type(template), typed_ir::TypeArg::Bounds(actual)) => {
            if let Some(actual) = tir_evidence_bound(actual) {
                infer_type_substitutions_inner(
                    template,
                    &actual,
                    params,
                    substitutions,
                    depth,
                    options,
                );
            }
        }
        (typed_ir::TypeArg::Bounds(template), typed_ir::TypeArg::Type(actual)) => {
            if let Some(template) = tir_evidence_bound(template) {
                infer_type_substitutions_inner(
                    &template,
                    actual,
                    params,
                    substitutions,
                    depth,
                    options,
                );
            }
        }
        (typed_ir::TypeArg::Bounds(template), typed_ir::TypeArg::Bounds(actual)) => {
            if let (Some(template), Some(actual)) =
                (tir_evidence_bound(template), tir_evidence_bound(actual))
            {
                infer_type_substitutions_inner(
                    &template,
                    &actual,
                    params,
                    substitutions,
                    depth,
                    options,
                );
            }
        }
    }
}

pub(super) fn insert_substitution(
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    var: typed_ir::TypeVar,
    ty: typed_ir::Type,
    prefer_non_never: bool,
) {
    if core_type_is_unknown(&ty) || core_type_is_top(&ty) {
        return;
    }
    if matches!(&ty, typed_ir::Type::Var(actual) if actual == &var) || type_contains_var(&ty, &var)
    {
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

pub(super) fn type_has_vars(ty: &typed_ir::Type) -> bool {
    let mut vars = BTreeSet::new();
    collect_type_vars(ty, &mut vars);
    !vars.is_empty()
}

pub(super) fn type_contains_var(ty: &typed_ir::Type, var: &typed_ir::TypeVar) -> bool {
    let mut vars = BTreeSet::new();
    collect_type_vars(ty, &mut vars);
    vars.contains(var)
}

pub(super) fn tir_evidence_bound(bounds: &typed_ir::TypeBounds) -> Option<typed_ir::Type> {
    choose_bounds_type(bounds, BoundsChoice::TirEvidence)
}

fn substitute_type_arg(
    arg: &typed_ir::TypeArg,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    active: &mut BTreeSet<typed_ir::TypeVar>,
    bound: &BTreeSet<typed_ir::TypeVar>,
) -> typed_ir::TypeArg {
    match arg {
        typed_ir::TypeArg::Type(ty) => {
            typed_ir::TypeArg::Type(substitute_type_inner(ty, substitutions, active, bound))
        }
        typed_ir::TypeArg::Bounds(bounds) => typed_ir::TypeArg::Bounds(typed_ir::TypeBounds {
            lower: bounds
                .lower
                .as_ref()
                .map(|ty| Box::new(substitute_type_inner(ty, substitutions, active, bound))),
            upper: bounds
                .upper
                .as_ref()
                .map(|ty| Box::new(substitute_type_inner(ty, substitutions, active, bound))),
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn substitute_type_follows_transitive_aliases() {
        let a = tv("a");
        let b = tv("b");
        let mut substitutions = BTreeMap::new();
        substitutions.insert(a, typed_ir::Type::Var(b.clone()));
        substitutions.insert(b, named("int"));

        assert_eq!(
            substitute_type(&typed_ir::Type::Var(tv("a")), &substitutions),
            named("int")
        );
    }

    #[test]
    fn substitute_type_stops_at_alias_cycles() {
        let a = tv("a");
        let b = tv("b");
        let mut substitutions = BTreeMap::new();
        substitutions.insert(a, typed_ir::Type::Var(b.clone()));
        substitutions.insert(b, typed_ir::Type::Var(tv("a")));

        assert_eq!(
            substitute_type(&typed_ir::Type::Var(tv("a")), &substitutions),
            typed_ir::Type::Var(tv("a"))
        );
    }

    #[test]
    fn substitute_type_does_not_replace_recursive_binder() {
        let a = tv("a");
        let mut substitutions = BTreeMap::new();
        substitutions.insert(a.clone(), named("int"));
        let ty = typed_ir::Type::Recursive {
            var: a.clone(),
            body: Box::new(typed_ir::Type::Var(a.clone())),
        };

        assert_eq!(
            substitute_type(&ty, &substitutions),
            typed_ir::Type::Recursive {
                var: a.clone(),
                body: Box::new(typed_ir::Type::Var(a)),
            }
        );
    }

    #[test]
    fn substitute_type_renames_recursive_binder_to_avoid_capture() {
        let a = tv("a");
        let x = tv("x");
        let mut substitutions = BTreeMap::new();
        substitutions.insert(a.clone(), typed_ir::Type::Var(x.clone()));
        let ty = typed_ir::Type::Recursive {
            var: x.clone(),
            body: Box::new(typed_ir::Type::Var(a)),
        };

        let substituted = substitute_type(&ty, &substitutions);

        let typed_ir::Type::Recursive { var, body } = substituted else {
            panic!("expected recursive type");
        };
        assert_ne!(var, x);
        assert_eq!(*body, typed_ir::Type::Var(x));
    }

    #[test]
    fn plan_normalization_closes_child_var_after_parent_substitution() {
        let a = tv("a");
        let t = tv("t");
        let mut substitutions = BTreeMap::new();
        substitutions.insert(t.clone(), named("int"));

        let plan = list_plan_for_arg(list_of(typed_ir::Type::Var(t)));
        let normalized = substitute_principal_elaboration_plan(plan, &substitutions, &[]);

        assert!(normalized.complete, "{:?}", normalized.incomplete_reasons);
        assert_eq!(
            normalized.substitutions,
            vec![typed_ir::TypeSubstitution {
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
        plan.substitutions = vec![typed_ir::TypeSubstitution {
            var: t.clone(),
            ty: named("int"),
        }];
        let candidates = vec![typed_ir::PrincipalSubstitutionCandidate {
            var: a.clone(),
            relation: typed_ir::PrincipalCandidateRelation::Exact,
            ty: typed_ir::Type::Var(t),
            source_edge: None,
            path: vec![typed_ir::PrincipalSlotPathSegment::Result],
        }];

        let normalized = normalize_principal_elaboration_plan(plan, &candidates);

        assert!(normalized.complete, "{:?}", normalized.incomplete_reasons);
        assert_eq!(
            normalized.substitutions,
            vec![
                typed_ir::TypeSubstitution {
                    var: a,
                    ty: named("int"),
                },
                typed_ir::TypeSubstitution {
                    var: tv("t"),
                    ty: named("int"),
                },
            ]
        );
    }

    #[test]
    fn plan_normalization_rejects_substitution_that_violates_candidate_bounds() {
        let item = tv("item");
        let mut plan = typed_ir::PrincipalElaborationPlan {
            target: Some(typed_ir::Path::from_name(typed_ir::Name(
                "for_in".to_string(),
            ))),
            principal_callee: typed_ir::Type::Fun {
                param: Box::new(typed_ir::Type::Var(item.clone())),
                param_effect: Box::new(typed_ir::Type::Never),
                ret_effect: Box::new(typed_ir::Type::Never),
                ret: Box::new(named("unit")),
            },
            substitutions: vec![typed_ir::TypeSubstitution {
                var: item.clone(),
                ty: named("unit"),
            }],
            args: vec![typed_ir::PrincipalElaborationArg {
                index: 0,
                intrinsic: typed_ir::TypeBounds::exact(named("int")),
                contextual: None,
                expected_runtime: None,
                source_edge: Some(1),
            }],
            result: typed_ir::PrincipalElaborationResult {
                intrinsic: typed_ir::TypeBounds::exact(named("unit")),
                contextual: None,
                expected_runtime: None,
            },
            adapters: Vec::new(),
            complete: false,
            incomplete_reasons: Vec::new(),
        };
        plan.incomplete_reasons =
            vec![typed_ir::PrincipalElaborationIncompleteReason::MissingSubstitution(item.clone())];
        let candidates = vec![typed_ir::PrincipalSubstitutionCandidate {
            var: item.clone(),
            relation: typed_ir::PrincipalCandidateRelation::Lower,
            ty: named("int"),
            source_edge: Some(1),
            path: vec![typed_ir::PrincipalSlotPathSegment::Arg],
        }];

        let normalized = normalize_principal_elaboration_plan(plan, &candidates);

        assert!(!normalized.complete);
        assert!(normalized.incomplete_reasons.contains(
            &typed_ir::PrincipalElaborationIncompleteReason::ConflictingSubstitution(item)
        ));
        assert!(normalized.substitutions.is_empty());
    }

    #[test]
    fn plan_normalization_leaves_open_child_var_missing() {
        let plan = list_plan_for_arg(list_of(typed_ir::Type::Var(tv("t"))));
        let normalized = substitute_principal_elaboration_plan(plan, &BTreeMap::new(), &[]);

        assert!(!normalized.complete);
        assert!(normalized.incomplete_reasons.contains(
            &typed_ir::PrincipalElaborationIncompleteReason::MissingSubstitution(tv("a"))
        ));
    }

    #[test]
    fn plan_normalization_does_not_solve_union_actuals() {
        let plan = list_plan_for_arg(list_of(typed_ir::Type::Union(vec![
            typed_ir::Type::Var(tv("t")),
            named("int"),
        ])));
        let normalized = substitute_principal_elaboration_plan(plan, &BTreeMap::new(), &[]);

        assert!(!normalized.complete);
        assert!(normalized.incomplete_reasons.contains(
            &typed_ir::PrincipalElaborationIncompleteReason::MissingSubstitution(tv("a"))
        ));
    }

    #[test]
    fn plan_normalization_closes_child_var_from_single_closed_type_arg_bound() {
        let plan = list_plan_for_arg(typed_ir::Type::Named {
            path: typed_ir::Path::from_name(typed_ir::Name("list".to_string())),
            args: vec![typed_ir::TypeArg::Bounds(typed_ir::TypeBounds::upper(
                named("int"),
            ))],
        });
        let normalized = substitute_principal_elaboration_plan(plan, &BTreeMap::new(), &[]);

        assert!(normalized.complete, "{:?}", normalized.incomplete_reasons);
        assert_eq!(
            normalized.substitutions,
            vec![typed_ir::TypeSubstitution {
                var: tv("a"),
                ty: named("int"),
            }]
        );
    }

    #[test]
    fn plan_normalization_closes_child_var_from_repeated_choice_bound_args() {
        let list_int = list_of(named("int"));
        let list_bounded_int = typed_ir::Type::Named {
            path: typed_ir::Path::from_name(typed_ir::Name("list".to_string())),
            args: vec![typed_ir::TypeArg::Bounds(typed_ir::TypeBounds {
                lower: Some(Box::new(typed_ir::Type::Union(vec![
                    named("int"),
                    named("int"),
                ]))),
                upper: Some(Box::new(named("int"))),
            })],
        };
        let plan = list_plan_for_arg(typed_ir::Type::Union(vec![
            list_int.clone(),
            list_bounded_int,
            list_int,
        ]));
        let normalized = substitute_principal_elaboration_plan(plan, &BTreeMap::new(), &[]);

        assert!(normalized.complete, "{:?}", normalized.incomplete_reasons);
        assert_eq!(
            normalized.substitutions,
            vec![typed_ir::TypeSubstitution {
                var: tv("a"),
                ty: named("int"),
            }]
        );
    }

    #[test]
    fn plan_normalization_does_not_infer_fold_item_from_list_shape_without_impl_graph() {
        let mut plan = typed_ir::PrincipalElaborationPlan {
            target: Some(typed_ir::Path::from_name(typed_ir::Name("all".to_string()))),
            principal_callee: typed_ir::Type::Fun {
                param: Box::new(typed_ir::Type::Var(tv("container"))),
                param_effect: Box::new(typed_ir::Type::Never),
                ret_effect: Box::new(typed_ir::Type::Never),
                ret: Box::new(typed_ir::Type::Var(tv("item"))),
            },
            substitutions: vec![typed_ir::TypeSubstitution {
                var: tv("container"),
                ty: list_of(named("int")),
            }],
            args: vec![typed_ir::PrincipalElaborationArg {
                index: 0,
                intrinsic: typed_ir::TypeBounds::exact(list_of(named("int"))),
                contextual: None,
                expected_runtime: None,
                source_edge: None,
            }],
            result: typed_ir::PrincipalElaborationResult {
                intrinsic: typed_ir::TypeBounds::default(),
                contextual: None,
                expected_runtime: None,
            },
            adapters: Vec::new(),
            complete: false,
            incomplete_reasons: Vec::new(),
        };
        plan.result.contextual = Some(typed_ir::TypeBounds::exact(typed_ir::Type::Var(tv("item"))));

        let normalized = normalize_principal_elaboration_plan_with_requirements(
            plan,
            &[],
            &[typed_ir::RoleRequirement {
                role: typed_ir::Path::from_name(typed_ir::Name("Fold".to_string())),
                args: vec![
                    typed_ir::RoleRequirementArg::Input(typed_ir::TypeBounds::exact(
                        typed_ir::Type::Var(tv("container")),
                    )),
                    typed_ir::RoleRequirementArg::Associated {
                        name: typed_ir::Name("item".to_string()),
                        bounds: typed_ir::TypeBounds::exact(typed_ir::Type::Var(tv("item"))),
                    },
                ],
            }],
        );

        assert!(!normalized.complete);
        assert!(normalized.incomplete_reasons.contains(
            &typed_ir::PrincipalElaborationIncompleteReason::MissingSubstitution(tv("item"))
        ));
    }

    #[test]
    fn plan_normalization_projects_associated_role_requirement_from_impl_graph() {
        let mut plan = typed_ir::PrincipalElaborationPlan {
            target: Some(typed_ir::Path::from_name(typed_ir::Name("get".to_string()))),
            principal_callee: typed_ir::Type::Fun {
                param: Box::new(typed_ir::Type::Var(tv("container"))),
                param_effect: Box::new(typed_ir::Type::Never),
                ret_effect: Box::new(typed_ir::Type::Never),
                ret: Box::new(typed_ir::Type::Var(tv("item"))),
            },
            substitutions: vec![typed_ir::TypeSubstitution {
                var: tv("container"),
                ty: named("bag"),
            }],
            args: vec![typed_ir::PrincipalElaborationArg {
                index: 0,
                intrinsic: typed_ir::TypeBounds::exact(named("bag")),
                contextual: None,
                expected_runtime: None,
                source_edge: None,
            }],
            result: typed_ir::PrincipalElaborationResult {
                intrinsic: typed_ir::TypeBounds::default(),
                contextual: None,
                expected_runtime: None,
            },
            adapters: Vec::new(),
            complete: false,
            incomplete_reasons: Vec::new(),
        };
        plan.result.contextual = Some(typed_ir::TypeBounds::exact(typed_ir::Type::Var(tv("item"))));

        let role_impls = vec![typed_ir::RoleImplGraphNode {
            role: typed_ir::Path::from_name(typed_ir::Name("Readable".to_string())),
            inputs: vec![typed_ir::TypeBounds::exact(named("bag"))],
            associated_types: vec![typed_ir::RecordField {
                name: typed_ir::Name("item".to_string()),
                value: typed_ir::TypeBounds::exact(named("int")),
                optional: false,
            }],
            members: Vec::new(),
        }];
        let normalized = normalize_principal_elaboration_plan_with_role_impls(
            plan,
            &[],
            &[typed_ir::RoleRequirement {
                role: typed_ir::Path::from_name(typed_ir::Name("Readable".to_string())),
                args: vec![
                    typed_ir::RoleRequirementArg::Input(typed_ir::TypeBounds::exact(
                        typed_ir::Type::Var(tv("container")),
                    )),
                    typed_ir::RoleRequirementArg::Associated {
                        name: typed_ir::Name("item".to_string()),
                        bounds: typed_ir::TypeBounds::exact(typed_ir::Type::Var(tv("item"))),
                    },
                ],
            }],
            &role_impls,
        );

        assert!(normalized.complete, "{:?}", normalized.incomplete_reasons);
        assert!(
            normalized
                .substitutions
                .contains(&typed_ir::TypeSubstitution {
                    var: tv("item"),
                    ty: named("int"),
                })
        );
    }

    #[test]
    fn role_requirement_projection_closes_deep_associated_chain() {
        let chain_len = 6;
        let vars = (0..=chain_len)
            .map(|index| tv(&format!("v{index}")))
            .collect::<Vec<_>>();
        let mut requirements = Vec::new();
        let mut role_impls = Vec::new();
        for index in (0..chain_len).rev() {
            let role = typed_ir::Path::from_name(typed_ir::Name(format!("Role{index}")));
            let next = typed_ir::Name("next".to_string());
            requirements.push(typed_ir::RoleRequirement {
                role: role.clone(),
                args: vec![
                    typed_ir::RoleRequirementArg::Input(typed_ir::TypeBounds::exact(
                        typed_ir::Type::Var(vars[index].clone()),
                    )),
                    typed_ir::RoleRequirementArg::Associated {
                        name: next.clone(),
                        bounds: typed_ir::TypeBounds::exact(typed_ir::Type::Var(
                            vars[index + 1].clone(),
                        )),
                    },
                ],
            });
            role_impls.push(typed_ir::RoleImplGraphNode {
                role,
                inputs: vec![typed_ir::TypeBounds::exact(named(&format!("t{index}")))],
                associated_types: vec![typed_ir::RecordField {
                    name: next,
                    value: typed_ir::TypeBounds::exact(named(&format!("t{}", index + 1))),
                    optional: false,
                }],
                members: Vec::new(),
            });
        }
        let params = vars.iter().cloned().collect::<BTreeSet<_>>();
        let mut substitutions = BTreeMap::from([(vars[0].clone(), named("t0"))]);
        let mut conflicts = BTreeSet::new();

        project_substitutions_from_role_requirements(
            &requirements,
            &role_impls,
            &params,
            &mut substitutions,
            &mut conflicts,
        );

        assert!(conflicts.is_empty(), "{conflicts:?}");
        assert_eq!(substitutions.get(&vars[chain_len]), Some(&named("t6")));
    }

    #[test]
    fn plan_normalization_does_not_project_conflicting_type_arg_bounds() {
        let plan = list_plan_for_arg(typed_ir::Type::Named {
            path: typed_ir::Path::from_name(typed_ir::Name("list".to_string())),
            args: vec![typed_ir::TypeArg::Bounds(typed_ir::TypeBounds {
                lower: Some(Box::new(named("int"))),
                upper: Some(Box::new(named("bool"))),
            })],
        });
        let normalized = substitute_principal_elaboration_plan(plan, &BTreeMap::new(), &[]);

        assert!(!normalized.complete);
        assert!(normalized.incomplete_reasons.contains(
            &typed_ir::PrincipalElaborationIncompleteReason::MissingSubstitution(tv("a"))
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
            typed_ir::PrincipalElaborationIncompleteReason::MissingAdapterHole(
                typed_ir::PrincipalAdapterKind::ValueToThunk,
            ),
        ];
        let normalized = substitute_principal_elaboration_plan(plan, &BTreeMap::new(), &[]);

        assert!(!normalized.complete);
        assert!(normalized.adapters.is_empty());
        assert!(normalized.incomplete_reasons.contains(
            &typed_ir::PrincipalElaborationIncompleteReason::MissingAdapterHole(
                typed_ir::PrincipalAdapterKind::ValueToThunk,
            )
        ));
    }

    #[test]
    fn closed_projection_matches_effect_row_residuals_without_graph_solving() {
        let item = tv("item");
        let residual = tv("residual");
        let template = typed_ir::Type::Row {
            items: vec![named_with_args(
                "sub",
                vec![typed_ir::TypeArg::Type(typed_ir::Type::Var(item.clone()))],
            )],
            tail: Box::new(typed_ir::Type::Var(residual.clone())),
        };
        let actual = typed_ir::Type::Row {
            items: vec![
                named_with_args("sub", vec![typed_ir::TypeArg::Type(named("int"))]),
                named("junction"),
            ],
            tail: Box::new(typed_ir::Type::Never),
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
    fn closed_projection_does_not_split_residual_across_multiple_row_vars() {
        let left = tv("left");
        let right = tv("right");
        let template = typed_ir::Type::Row {
            items: vec![
                typed_ir::Type::Var(left.clone()),
                typed_ir::Type::Var(right.clone()),
            ],
            tail: Box::new(typed_ir::Type::Never),
        };
        let actual = typed_ir::Type::Row {
            items: vec![named("io"), named("state")],
            tail: Box::new(typed_ir::Type::Never),
        };
        let params = BTreeSet::from([left.clone(), right.clone()]);
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
        assert!(!substitutions.contains_key(&left));
        assert!(!substitutions.contains_key(&right));
    }

    #[test]
    fn inference_does_not_split_residual_across_multiple_row_vars() {
        let left = tv("left");
        let right = tv("right");
        let template = typed_ir::Type::Row {
            items: vec![
                typed_ir::Type::Var(left.clone()),
                typed_ir::Type::Var(right.clone()),
            ],
            tail: Box::new(typed_ir::Type::Never),
        };
        let actual = typed_ir::Type::Row {
            items: vec![named("io"), named("state")],
            tail: Box::new(typed_ir::Type::Never),
        };
        let params = BTreeSet::from([left.clone(), right.clone()]);
        let mut substitutions = BTreeMap::new();

        infer_type_substitutions(&template, &actual, &params, &mut substitutions);

        assert!(!substitutions.contains_key(&left));
        assert!(!substitutions.contains_key(&right));
    }

    #[test]
    fn inference_does_not_solve_bare_var_choice_branch() {
        let item = tv("item");
        let template = typed_ir::Type::Union(vec![typed_ir::Type::Var(item.clone()), named("int")]);
        let params = BTreeSet::from([item.clone()]);
        let mut substitutions = BTreeMap::new();

        infer_type_substitutions(&template, &named("bool"), &params, &mut substitutions);

        assert!(!substitutions.contains_key(&item));
    }

    #[test]
    fn inference_solves_matching_structured_choice_branch() {
        let item = tv("item");
        let template = typed_ir::Type::Union(vec![
            list_of(typed_ir::Type::Var(item.clone())),
            named("int"),
        ]);
        let params = BTreeSet::from([item.clone()]);
        let mut substitutions = BTreeMap::new();

        infer_type_substitutions(
            &template,
            &list_of(named("bool")),
            &params,
            &mut substitutions,
        );

        assert_eq!(substitutions.get(&item), Some(&named("bool")));
    }

    #[test]
    fn closed_projection_treats_child_effect_as_matching_parent_row_item() {
        let residual = tv("residual");
        let template = typed_ir::Type::Row {
            items: vec![path_type(["#loop_label"])],
            tail: Box::new(typed_ir::Type::Var(residual.clone())),
        };
        let actual = typed_ir::Type::Row {
            items: vec![path_type(["#loop_label", "last"]), named("state")],
            tail: Box::new(typed_ir::Type::Never),
        };
        let params = BTreeSet::from([residual.clone()]);
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
        assert_eq!(substitutions.get(&residual), Some(&named("state")));
    }

    #[test]
    fn closed_projection_keeps_effect_with_incompatible_payload_in_residual() {
        let residual = tv("residual");
        let template = typed_ir::Type::Row {
            items: vec![named_with_args(
                "sub",
                vec![typed_ir::TypeArg::Type(named("int"))],
            )],
            tail: Box::new(typed_ir::Type::Var(residual.clone())),
        };
        let actual_effect = named_with_args("sub", vec![typed_ir::TypeArg::Type(named("bool"))]);
        let actual = typed_ir::Type::Row {
            items: vec![actual_effect.clone()],
            tail: Box::new(typed_ir::Type::Never),
        };
        let params = BTreeSet::from([residual.clone()]);
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
        assert_eq!(substitutions.get(&residual), Some(&actual_effect));
    }

    #[test]
    fn inference_keeps_effect_with_incompatible_payload_in_residual() {
        let residual = tv("residual");
        let template = typed_ir::Type::Row {
            items: vec![named_with_args(
                "sub",
                vec![typed_ir::TypeArg::Type(named("int"))],
            )],
            tail: Box::new(typed_ir::Type::Var(residual.clone())),
        };
        let actual_effect = named_with_args("sub", vec![typed_ir::TypeArg::Type(named("bool"))]);
        let actual = typed_ir::Type::Row {
            items: vec![actual_effect.clone()],
            tail: Box::new(typed_ir::Type::Never),
        };
        let params = BTreeSet::from([residual.clone()]);
        let mut substitutions = BTreeMap::new();

        infer_type_substitutions(&template, &actual, &params, &mut substitutions);

        assert_eq!(substitutions.get(&residual), Some(&actual_effect));
    }

    #[test]
    fn closed_projection_does_not_solve_principal_var_union_from_closed_actual() {
        let left = tv("left");
        let right = tv("right");
        let template = typed_ir::Type::Union(vec![
            typed_ir::Type::Var(left.clone()),
            typed_ir::Type::Var(right.clone()),
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

    fn list_plan_for_arg(arg_ty: typed_ir::Type) -> typed_ir::PrincipalElaborationPlan {
        typed_ir::PrincipalElaborationPlan {
            target: Some(typed_ir::Path::from_name(typed_ir::Name(
                "view_raw".to_string(),
            ))),
            principal_callee: typed_ir::Type::Fun {
                param: Box::new(list_of(typed_ir::Type::Var(tv("a")))),
                param_effect: Box::new(typed_ir::Type::Never),
                ret_effect: Box::new(typed_ir::Type::Never),
                ret: Box::new(named("unit")),
            },
            substitutions: Vec::new(),
            args: vec![typed_ir::PrincipalElaborationArg {
                index: 0,
                intrinsic: typed_ir::TypeBounds::exact(arg_ty),
                contextual: None,
                expected_runtime: None,
                source_edge: None,
            }],
            result: typed_ir::PrincipalElaborationResult {
                intrinsic: typed_ir::TypeBounds::exact(named("unit")),
                contextual: None,
                expected_runtime: None,
            },
            adapters: Vec::new(),
            complete: false,
            incomplete_reasons: vec![
                typed_ir::PrincipalElaborationIncompleteReason::MissingSubstitution(tv("a")),
            ],
        }
    }

    fn list_of(item: typed_ir::Type) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: typed_ir::Path::from_name(typed_ir::Name("list".to_string())),
            args: vec![typed_ir::TypeArg::Type(item)],
        }
    }

    fn named(name: &str) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: typed_ir::Path::from_name(typed_ir::Name(name.to_string())),
            args: Vec::new(),
        }
    }

    fn named_with_args(name: &str, args: Vec<typed_ir::TypeArg>) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: typed_ir::Path::from_name(typed_ir::Name(name.to_string())),
            args,
        }
    }

    fn path_type<const N: usize>(segments: [&str; N]) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: typed_ir::Path::new(
                segments
                    .into_iter()
                    .map(|segment| typed_ir::Name(segment.to_string()))
                    .collect(),
            ),
            args: Vec::new(),
        }
    }

    fn tv(name: &str) -> typed_ir::TypeVar {
        typed_ir::TypeVar(name.to_string())
    }
}
