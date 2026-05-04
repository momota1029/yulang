use crate::ir::Module;

use std::collections::{BTreeMap, HashMap};

use super::*;
use super::{
    SubstitutionSpecializeProfile, principal_elaboration_plan_for_expr,
    substitute_specialize_module_profiled,
};

pub(super) fn principal_elaborate_module_profiled(
    module: Module,
) -> (Module, SubstitutionSpecializeProfile) {
    // This pass is being migrated from substitution-specialize to
    // principal-elaborate. The main path should execute exported principal
    // elaboration evidence, not infer substitutions from runtime IR shapes.
    substitute_specialize_module_profiled(module)
}

pub(super) fn principal_elaborate_strict_failure(module: &Module) -> Option<String> {
    let generic_bindings = module
        .bindings
        .iter()
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
    for binding in &module.bindings {
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
        if !plan.as_ref().is_some_and(|plan| plan.complete) {
            let target = failures.entry(spine.target.clone()).or_default();
            target.count += 1;
            if let Some(plan) = plan {
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

fn principal_binding_substitution_vars(binding: &Binding) -> BTreeSet<core_ir::TypeVar> {
    let mut vars = BTreeSet::new();
    collect_binding_type_params(binding, &mut vars);
    vars
}
