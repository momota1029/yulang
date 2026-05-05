use crate::ir::Module;

use std::collections::{BTreeMap, HashMap};
use std::sync::OnceLock;

use super::*;
use super::{
    SubstitutionSpecializeProfile, principal_unify_module, principal_unify_module_profiled,
};
use crate::types::{
    core_type_contains_unknown, normalize_principal_elaboration_plan_with_requirements,
    runtime_core_type,
};

pub(super) fn principal_elaborate_module(module: Module) -> Module {
    // The main path should execute exported principal elaboration evidence,
    // not infer substitutions from runtime IR shapes.
    principal_unify_module(module)
}

pub(super) fn principal_elaborate_module_profiled(
    module: Module,
) -> (Module, SubstitutionSpecializeProfile) {
    // The main path should execute exported principal elaboration evidence,
    // not infer substitutions from runtime IR shapes.
    principal_unify_module_profiled(module)
}

pub(super) fn principal_elaborate_strict_failure(module: &Module) -> Option<String> {
    let reachable = root_reachable_binding_paths(module);
    let generic_bindings = module
        .bindings
        .iter()
        .filter(|binding| reachable.contains(&binding.name))
        .filter(|binding| !principal_binding_substitution_vars(binding).is_empty())
        .map(|binding| (binding.name.clone(), binding))
        .collect::<HashMap<_, _>>();
    if generic_bindings.is_empty() {
        return None;
    }

    let mut failures = HashMap::<core_ir::Path, PrincipalElaborationStrictTarget>::new();
    for expr in &module.root_exprs {
        collect_principal_elaboration_failures(expr, None, &generic_bindings, &mut failures);
    }
    for binding in module
        .bindings
        .iter()
        .filter(|binding| reachable.contains(&binding.name))
    {
        collect_principal_elaboration_failures(
            &binding.body,
            None,
            &generic_bindings,
            &mut failures,
        );
    }

    if failures.is_empty() {
        None
    } else {
        Some(format_principal_elaboration_strict_failure(failures))
    }
}

fn collect_principal_elaboration_failures(
    expr: &Expr,
    result_contextual: Option<&core_ir::TypeBounds>,
    generic_bindings: &HashMap<core_ir::Path, &Binding>,
    failures: &mut HashMap<core_ir::Path, PrincipalElaborationStrictTarget>,
) {
    if let Some(spine) = principal_apply_spine(expr)
        && let Some(binding) = generic_bindings.get(spine.target)
    {
        let plan = principal_elaboration_plan_for_expr(expr, binding, result_contextual);
        if handler_binding_info(binding).is_none()
            && !plan
                .as_ref()
                .is_some_and(|plan| plan.complete || handler_boundary_plan_is_strict_complete(plan))
        {
            let target = failures.entry(spine.target.clone()).or_default();
            target.count += 1;
            if handler_binding_info(binding).is_some() {
                target.bump(format!(
                    "{:?}",
                    core_ir::PrincipalElaborationIncompleteReason::HandlerBoundaryWithoutPlan
                ));
            } else if let Some(plan) = plan {
                for reason in &plan.incomplete_reasons {
                    target.bump(format!("{reason:?}"));
                }
            } else {
                target.bump("MissingPrincipalElaborationPlan".to_string());
            }
        }
        for (arg, evidence) in spine
            .args
            .into_iter()
            .zip(spine.evidences_by_arg.into_iter())
        {
            let arg_context = evidence.and_then(|evidence| evidence.expected_arg.as_ref());
            collect_principal_elaboration_failures(arg, arg_context, generic_bindings, failures);
        }
        return;
    }

    match &expr.kind {
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            ..
        } => {
            let callee_context = evidence
                .as_ref()
                .and_then(|evidence| evidence.expected_callee.as_ref());
            let arg_context = evidence
                .as_ref()
                .and_then(|evidence| evidence.expected_arg.as_ref());
            collect_principal_elaboration_failures(
                callee,
                callee_context,
                generic_bindings,
                failures,
            );
            collect_principal_elaboration_failures(arg, arg_context, generic_bindings, failures);
        }
        ExprKind::Lambda { body, .. }
        | ExprKind::BindHere { expr: body }
        | ExprKind::Thunk { expr: body, .. }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::AddId { thunk: body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. } => {
            collect_principal_elaboration_failures(body, None, generic_bindings, failures);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_principal_elaboration_failures(cond, None, generic_bindings, failures);
            collect_principal_elaboration_failures(then_branch, None, generic_bindings, failures);
            collect_principal_elaboration_failures(else_branch, None, generic_bindings, failures);
        }
        ExprKind::Tuple(items) => {
            for item in items {
                collect_principal_elaboration_failures(item, None, generic_bindings, failures);
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                collect_principal_elaboration_failures(
                    &field.value,
                    None,
                    generic_bindings,
                    failures,
                );
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                        collect_principal_elaboration_failures(
                            expr,
                            None,
                            generic_bindings,
                            failures,
                        );
                    }
                }
            }
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                collect_principal_elaboration_failures(value, None, generic_bindings, failures);
            }
        }
        ExprKind::Select { base, .. } => {
            collect_principal_elaboration_failures(base, None, generic_bindings, failures);
        }
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            collect_principal_elaboration_failures(scrutinee, None, generic_bindings, failures);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_principal_elaboration_failures(guard, None, generic_bindings, failures);
                }
                collect_principal_elaboration_failures(&arm.body, None, generic_bindings, failures);
            }
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                collect_principal_elaboration_failures_in_stmt(stmt, generic_bindings, failures);
            }
            if let Some(tail) = tail {
                collect_principal_elaboration_failures(
                    tail,
                    result_contextual,
                    generic_bindings,
                    failures,
                );
            }
        }
        ExprKind::Handle { body, arms, .. } => {
            collect_principal_elaboration_failures(body, None, generic_bindings, failures);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_principal_elaboration_failures(guard, None, generic_bindings, failures);
                }
                collect_principal_elaboration_failures(&arm.body, None, generic_bindings, failures);
            }
        }
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
}

fn handler_boundary_plan_is_strict_complete(plan: &core_ir::PrincipalElaborationPlan) -> bool {
    !plan.incomplete_reasons.is_empty()
        && plan.incomplete_reasons.iter().all(|reason| {
            matches!(
                reason,
                core_ir::PrincipalElaborationIncompleteReason::HandlerBoundaryWithoutPlan
            )
        })
}

fn collect_principal_elaboration_failures_in_stmt(
    stmt: &Stmt,
    generic_bindings: &HashMap<core_ir::Path, &Binding>,
    failures: &mut HashMap<core_ir::Path, PrincipalElaborationStrictTarget>,
) {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) | Stmt::Module { body: value, .. } => {
            collect_principal_elaboration_failures(value, None, generic_bindings, failures);
        }
    }
}

fn format_principal_elaboration_strict_failure(
    failures: HashMap<core_ir::Path, PrincipalElaborationStrictTarget>,
) -> String {
    let mut lines = Vec::new();
    let mut failures = failures.into_iter().collect::<Vec<_>>();
    failures.sort_by(|(left, _), (right, _)| canonical_path(left).cmp(&canonical_path(right)));
    for (target, failure) in failures.into_iter().take(16) {
        let reasons = failure
            .reasons
            .into_iter()
            .map(|(reason, count)| format!("{reason}={count}"))
            .collect::<Vec<_>>()
            .join(", ");
        lines.push(format!(
            "{}: incomplete_calls={}, reasons=[{}]",
            canonical_path(&target),
            failure.count,
            reasons
        ));
    }
    format!(
        "principal elaboration strict mode found incomplete reachable plans:\n{}",
        lines.join("\n")
    )
}

#[derive(Default)]
struct PrincipalElaborationStrictTarget {
    count: usize,
    reasons: BTreeMap<String, usize>,
}

impl PrincipalElaborationStrictTarget {
    fn bump(&mut self, reason: String) {
        *self.reasons.entry(reason).or_default() += 1;
    }
}

struct PrincipalApplySpine<'a> {
    target: &'a core_ir::Path,
    args: Vec<&'a Expr>,
    evidences_by_arg: Vec<Option<&'a core_ir::ApplyEvidence>>,
}

fn principal_apply_spine(expr: &Expr) -> Option<PrincipalApplySpine<'_>> {
    let mut current = expr;
    let mut args = Vec::new();
    let mut evidences_by_arg = Vec::new();
    while let ExprKind::Apply {
        callee,
        arg,
        evidence,
        ..
    } = &current.kind
    {
        args.push(arg.as_ref());
        evidences_by_arg.push(evidence.as_ref());
        current = callee;
        while let ExprKind::BindHere { expr } = &current.kind {
            current = expr;
        }
    }
    let ExprKind::Var(target) = &current.kind else {
        return None;
    };
    args.reverse();
    evidences_by_arg.reverse();
    Some(PrincipalApplySpine {
        target,
        args,
        evidences_by_arg,
    })
}

pub(super) fn principal_elaboration_plan_for_expr(
    expr: &Expr,
    binding: &Binding,
    result_contextual: Option<&core_ir::TypeBounds>,
) -> Option<core_ir::PrincipalElaborationPlan> {
    let spine = principal_apply_spine(expr)?;
    if spine.target != &binding.name {
        return None;
    }
    if let Some(plan) =
        complete_principal_elaboration_plan_from_spine(&spine, binding, result_contextual)
            .filter(|plan| plan.complete)
    {
        return Some(plan);
    }
    if let Some(plan) = spine.evidences_by_arg.iter().find_map(|evidence| {
        let evidence = evidence.as_ref().copied()?;
        let plan = evidence.principal_elaboration.as_ref()?;
        (plan.complete
            && plan
                .target
                .as_ref()
                .is_none_or(|plan_target| plan_target == &binding.name))
        .then_some(plan.clone())
    }) {
        return Some(plan);
    }
    complete_principal_elaboration_plan_from_spine(&spine, binding, result_contextual).or_else(
        || {
            spine.evidences_by_arg.iter().find_map(|evidence| {
                let evidence = evidence.as_ref().copied()?;
                let plan = evidence.principal_elaboration.as_ref()?;
                (plan
                    .target
                    .as_ref()
                    .is_none_or(|plan_target| plan_target == &binding.name))
                .then_some(plan.clone())
            })
        },
    )
}

fn complete_principal_elaboration_plan_from_spine(
    spine: &PrincipalApplySpine<'_>,
    binding: &Binding,
    result_contextual: Option<&core_ir::TypeBounds>,
) -> Option<core_ir::PrincipalElaborationPlan> {
    let (params, ret) = core_fun_spine(&binding.scheme.body, spine.args.len())?;
    let mut substitutions = Vec::new();
    let mut candidates = Vec::new();
    let mut args = Vec::new();
    for (index, (arg, evidence)) in spine.args.iter().zip(&spine.evidences_by_arg).enumerate() {
        let runtime_arg = principal_plan_runtime_arg_bounds(arg);
        let Some(evidence) = evidence else {
            args.push(core_ir::PrincipalElaborationArg {
                index,
                intrinsic: runtime_arg.unwrap_or_default(),
                contextual: None,
                expected_runtime: None,
                source_edge: None,
            });
            continue;
        };
        substitutions.extend(evidence.substitutions.clone());
        candidates.extend(evidence.substitution_candidates.clone());
        args.push(core_ir::PrincipalElaborationArg {
            index,
            intrinsic: principal_plan_best_arg_bounds(&evidence.arg, runtime_arg),
            contextual: params
                .get(index)
                .cloned()
                .map(core_ir::TypeBounds::exact)
                .or_else(|| evidence.expected_arg.clone()),
            expected_runtime: None,
            source_edge: evidence.arg_source_edge,
        });
    }
    let result = spine
        .evidences_by_arg
        .last()
        .and_then(|evidence| evidence.map(|evidence| evidence.result.clone()))
        .unwrap_or_default();
    let plan = core_ir::PrincipalElaborationPlan {
        target: Some(binding.name.clone()),
        principal_callee: binding.scheme.body.clone(),
        substitutions,
        args,
        result: core_ir::PrincipalElaborationResult {
            intrinsic: result,
            contextual: result_contextual
                .cloned()
                .or_else(|| Some(core_ir::TypeBounds::exact(ret))),
            expected_runtime: None,
        },
        adapters: Vec::new(),
        complete: false,
        incomplete_reasons: Vec::new(),
    };
    let plan = normalize_principal_elaboration_plan_with_requirements(
        plan,
        &candidates,
        &binding.scheme.requirements,
    );
    debug_principal_elaboration_plan_from_spine(spine.target, &plan, &candidates);
    Some(plan)
}

fn principal_plan_best_arg_bounds(
    evidence: &core_ir::TypeBounds,
    runtime: Option<core_ir::TypeBounds>,
) -> core_ir::TypeBounds {
    match (
        principal_plan_bounds_are_precise(evidence),
        runtime
            .as_ref()
            .is_some_and(principal_plan_bounds_are_precise),
    ) {
        (true, _) => evidence.clone(),
        (false, true) => runtime.expect("checked precise runtime arg bounds"),
        (false, false) => evidence.clone(),
    }
}

fn principal_plan_runtime_arg_bounds(arg: &Expr) -> Option<core_ir::TypeBounds> {
    let ty = runtime_core_type(&arg.ty);
    principal_plan_type_is_precise(&ty).then(|| core_ir::TypeBounds::exact(ty))
}

fn principal_plan_bounds_are_precise(bounds: &core_ir::TypeBounds) -> bool {
    exact_type_from_bounds(bounds).is_some_and(principal_plan_type_is_precise)
}

fn principal_plan_type_is_precise(ty: &core_ir::Type) -> bool {
    !matches!(ty, core_ir::Type::Unknown | core_ir::Type::Any)
        && !core_type_has_vars(ty)
        && !core_type_contains_unknown(ty)
}

fn debug_principal_elaboration_plan_from_spine(
    target: &core_ir::Path,
    plan: &core_ir::PrincipalElaborationPlan,
    candidates: &[core_ir::PrincipalSubstitutionCandidate],
) {
    if !debug_principal_elaborate_enabled() {
        return;
    }
    if plan.complete {
        eprintln!(
            "principal elaborate spine-plan complete {} substitutions={:?}",
            canonical_path(target),
            plan.substitutions
        );
    } else {
        eprintln!(
            "principal elaborate spine-plan incomplete {} reasons={:?} substitutions={:?} candidates={}",
            canonical_path(target),
            plan.incomplete_reasons,
            plan.substitutions,
            candidates.len()
        );
        for arg in &plan.args {
            eprintln!(
                "  arg{} intrinsic={:?} contextual={:?}",
                arg.index, arg.intrinsic, arg.contextual
            );
        }
        eprintln!(
            "  result intrinsic={:?} contextual={:?}",
            plan.result.intrinsic, plan.result.contextual
        );
        for candidate in candidates.iter().take(12) {
            eprintln!(
                "  candidate {:?} {:?} {:?} source={:?} path={:?}",
                candidate.var,
                candidate.relation,
                candidate.ty,
                candidate.source_edge,
                candidate.path
            );
        }
    }
}

fn debug_principal_elaborate_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("YULANG_DEBUG_PRINCIPAL_ELABORATE").is_some())
}

fn exact_type_from_bounds(bounds: &core_ir::TypeBounds) -> Option<&core_ir::Type> {
    match (bounds.lower.as_deref(), bounds.upper.as_deref()) {
        (Some(lower), None) => Some(lower),
        (Some(lower), Some(upper)) if type_matches_exact_bounds(lower, upper) => Some(lower),
        _ => None,
    }
}

fn type_matches_exact_bounds(actual: &core_ir::Type, expected: &core_ir::Type) -> bool {
    if actual == expected || matches!(actual, core_ir::Type::Any) {
        return true;
    }
    match (actual, expected) {
        (
            core_ir::Type::Named {
                path: actual_path,
                args: actual_args,
            },
            core_ir::Type::Named {
                path: expected_path,
                args: expected_args,
            },
        ) => {
            actual_path == expected_path
                && actual_args.len() == expected_args.len()
                && actual_args
                    .iter()
                    .zip(expected_args)
                    .all(|(actual, expected)| type_arg_matches_exact_bounds(actual, expected))
        }
        (
            core_ir::Type::Fun {
                param: actual_param,
                param_effect: actual_param_effect,
                ret_effect: actual_ret_effect,
                ret: actual_ret,
            },
            core_ir::Type::Fun {
                param: expected_param,
                param_effect: expected_param_effect,
                ret_effect: expected_ret_effect,
                ret: expected_ret,
            },
        ) => {
            type_matches_exact_bounds(actual_param, expected_param)
                && type_matches_exact_bounds(actual_param_effect, expected_param_effect)
                && type_matches_exact_bounds(actual_ret_effect, expected_ret_effect)
                && type_matches_exact_bounds(actual_ret, expected_ret)
        }
        (core_ir::Type::Tuple(actual), core_ir::Type::Tuple(expected))
        | (core_ir::Type::Union(actual), core_ir::Type::Union(expected))
        | (core_ir::Type::Inter(actual), core_ir::Type::Inter(expected)) => {
            type_list_matches_exact_bounds(actual, expected)
        }
        (
            core_ir::Type::Row { items, tail },
            core_ir::Type::Row {
                items: expected_items,
                tail: expected_tail,
            },
        ) => {
            type_list_matches_exact_bounds(items, expected_items)
                && type_matches_exact_bounds(tail, expected_tail)
        }
        _ => false,
    }
}

fn type_list_matches_exact_bounds(actual: &[core_ir::Type], expected: &[core_ir::Type]) -> bool {
    actual.len() == expected.len()
        && actual
            .iter()
            .zip(expected)
            .all(|(actual, expected)| type_matches_exact_bounds(actual, expected))
}

fn type_arg_matches_exact_bounds(actual: &core_ir::TypeArg, expected: &core_ir::TypeArg) -> bool {
    if actual == expected {
        return true;
    }
    match (actual, expected) {
        (core_ir::TypeArg::Type(actual), core_ir::TypeArg::Bounds(expected)) => {
            bounds_are_exact_type(expected, actual)
        }
        (core_ir::TypeArg::Bounds(actual), core_ir::TypeArg::Type(expected)) => {
            bounds_are_exact_type(actual, expected)
        }
        (core_ir::TypeArg::Bounds(actual), core_ir::TypeArg::Bounds(expected)) => {
            match (
                exact_type_from_bounds(actual),
                exact_type_from_bounds(expected),
            ) {
                (Some(actual), Some(expected)) => type_matches_exact_bounds(actual, expected),
                _ => false,
            }
        }
        _ => false,
    }
}

fn bounds_are_exact_type(bounds: &core_ir::TypeBounds, ty: &core_ir::Type) -> bool {
    exact_type_from_bounds(bounds).is_some_and(|exact| type_matches_exact_bounds(exact, ty))
}

fn core_fun_parts(ty: &core_ir::Type) -> Option<(core_ir::Type, core_ir::Type)> {
    let core_ir::Type::Fun { param, ret, .. } = ty else {
        return None;
    };
    Some((param.as_ref().clone(), ret.as_ref().clone()))
}

fn core_fun_spine(ty: &core_ir::Type, arity: usize) -> Option<(Vec<core_ir::Type>, core_ir::Type)> {
    let mut params = Vec::with_capacity(arity);
    let mut current = ty.clone();
    for _ in 0..arity {
        let (param, ret) = core_fun_parts(&current)?;
        params.push(param);
        current = ret;
    }
    Some((params, current))
}

fn principal_binding_substitution_vars(binding: &Binding) -> BTreeSet<core_ir::TypeVar> {
    let mut vars = BTreeSet::new();
    collect_binding_type_params(binding, &mut vars);
    vars
}
