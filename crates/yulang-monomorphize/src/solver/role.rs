//! Role / trait method resolution for the finalize stage.
//!
//! Two responsibilities:
//!
//! 1. **Associated-type closure** during graph solving — when a binding's
//!    scheme says `requirements: Role<Input> => Associated`, the solver may
//!    leave an associated-type slot underdetermined. `close_role_associated_types`
//!    walks `role_impls` to project the impl's associated type back into the
//!    graph and re-solve.
//!
//! 2. **Role method dispatch rewriting** — once mono bindings are emitted,
//!    `rewrite_role_method_calls` traverses every expression and replaces
//!    abstract role-method `Apply` spines with the concrete impl member,
//!    using a scored candidate match (`role_method_candidate_score`,
//!    `core_subtype_match_score`, `type_bounds_match_score`).
//!
//! A small custom unifier (`infer_type_substitutions_inner`) lives here too —
//! it turns the bounds attached to role-method instances into substitutions
//! for type variables in the candidate's signature.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use yulang_runtime_ir::{
    FinalizedBinding as Binding, FinalizedExpr as Expr, FinalizedExprKind as ExprKind,
    FinalizedModule as Module, RuntimeType as RuntimeType,
};
use yulang_typed_ir as typed_ir;

use crate::{
    MonomorphizeResult, TypeGraph, graph::runtime_type_from_core_value, materialize_core_type,
};

use super::{
    apply_spine::{ApplySpine, ApplyStep},
    materialize, rewrite,
};

pub(crate) fn role_required_apply_waiting_for_arguments(
    binding: &Binding,
    spine: &ApplySpine<'_>,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
) -> bool {
    !binding.scheme.requirements.is_empty()
        && spine
            .steps
            .iter()
            .any(|step| !super::core_type_is_closed(&step.arg_type(local_types)))
}

pub(crate) fn close_role_associated_types(
    graph: &mut TypeGraph,
    binding: &Binding,
    principal: &crate::PrincipalInstance,
    solution: &crate::GraphSolution,
    role_impls: &[typed_ir::RoleImplGraphNode],
) -> MonomorphizeResult<bool> {
    let mut changed = false;
    let principal_renames = principal_rename_substitutions(principal);
    let solution_substitutions = solution.substitutions();
    for requirement in &binding.scheme.requirements {
        // Role method defaults expose associated slots through the requirement,
        // not through the apply spine. Close those slots from the selected impl
        // before deciding that a graph is genuinely incomplete.
        let Some(inputs) = solved_role_requirement_inputs(
            requirement,
            &principal_renames,
            &solution_substitutions,
        ) else {
            continue;
        };
        for arg in &requirement.args {
            let typed_ir::RoleRequirementArg::Associated { name, bounds } = arg else {
                continue;
            };
            let Some(projected) =
                resolve_associated_requirement_from_impls(requirement, name, &inputs, role_impls)
            else {
                continue;
            };
            let target = materialize::materialize_type_bounds(bounds.clone(), &principal_renames);
            let Some(target) = super::apply_spine::type_from_bounds(&target) else {
                continue;
            };
            graph.constrain_subtype(projected.clone(), target.clone())?;
            graph.constrain_subtype(target, projected)?;
            changed = true;
        }
    }
    Ok(changed)
}

/// True if any var's solution contains Unknown — i.e. the solver gave us a
/// shape (e.g. `Tuple([Unknown, Unknown])`) but didn't fill the components.
/// Such "shape-only" solutions need the associated-type closure to refine.
pub(crate) fn solution_has_unknown_components(solution: &crate::GraphSolution) -> bool {
    solution
        .type_vars
        .iter()
        .filter_map(|var| var.solution.as_ref())
        .any(super::core_type_has_unknown)
}

fn principal_rename_substitutions(
    principal: &crate::PrincipalInstance,
) -> Vec<typed_ir::TypeSubstitution> {
    principal
        .type_params
        .iter()
        .map(|param| typed_ir::TypeSubstitution {
            var: param.original.clone(),
            ty: typed_ir::Type::Var(param.fresh.clone()),
        })
        .collect()
}

fn solved_role_requirement_inputs(
    requirement: &typed_ir::RoleRequirement,
    principal_renames: &[typed_ir::TypeSubstitution],
    solution_substitutions: &[typed_ir::TypeSubstitution],
) -> Option<Vec<typed_ir::Type>> {
    let mut inputs = Vec::new();
    for arg in &requirement.args {
        let typed_ir::RoleRequirementArg::Input(bounds) = arg else {
            continue;
        };
        let bounds = materialize::materialize_type_bounds(bounds.clone(), principal_renames);
        let bounds = materialize::materialize_type_bounds(bounds, solution_substitutions);
        let ty = super::apply_spine::type_from_bounds(&bounds)?;
        if !super::core_type_is_closed(&ty) {
            return None;
        }
        inputs.push(ty);
    }
    Some(inputs)
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
            let template = super::apply_spine::type_from_bounds(bounds)?;
            collect_type_vars(&template, &mut impl_vars);
            Some(template)
        })
        .collect::<Option<Vec<_>>>()?;
    collect_type_bounds_vars(associated, &mut impl_vars);
    let mut substitutions = BTreeMap::new();
    for (template, actual) in templates.iter().zip(actual_inputs) {
        infer_type_substitutions(template, actual, &impl_vars, &mut substitutions);
    }
    let substitution_list = substitution_map_to_list(&substitutions);
    if templates
        .iter()
        .zip(actual_inputs)
        .any(|(template, actual)| {
            materialize_core_type(template.clone(), &substitution_list) != *actual
        })
    {
        return None;
    }
    super::apply_spine::type_from_bounds(&materialize::materialize_type_bounds(
        associated.clone(),
        &substitution_list,
    ))
}

fn collect_type_bounds_vars(bounds: &typed_ir::TypeBounds, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    if let Some(lower) = bounds.lower.as_deref() {
        collect_type_vars(lower, vars);
    }
    if let Some(upper) = bounds.upper.as_deref() {
        collect_type_vars(upper, vars);
    }
}

fn collect_type_vars(ty: &typed_ir::Type, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    match ty {
        typed_ir::Type::Unknown | typed_ir::Type::Never | typed_ir::Type::Any => {}
        typed_ir::Type::Var(var) => {
            vars.insert(var.clone());
        }
        typed_ir::Type::Named { args, .. } => {
            for arg in args {
                collect_type_arg_vars(arg, vars);
            }
        }
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            collect_type_vars(param, vars);
            collect_type_vars(param_effect, vars);
            collect_type_vars(ret_effect, vars);
            collect_type_vars(ret, vars);
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => {
            for item in items {
                collect_type_vars(item, vars);
            }
        }
        typed_ir::Type::Record(record) => {
            for field in &record.fields {
                collect_type_vars(&field.value, vars);
            }
        }
        typed_ir::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_type_vars(payload, vars);
                }
            }
            if let Some(tail) = &variant.tail {
                collect_type_vars(tail, vars);
            }
        }
        typed_ir::Type::Row { items, tail } => {
            for item in items {
                collect_type_vars(item, vars);
            }
            collect_type_vars(tail, vars);
        }
        typed_ir::Type::Recursive { var, body } => {
            let inserted = vars.insert(var.clone());
            collect_type_vars(body, vars);
            if inserted {
                vars.remove(var);
            }
        }
    }
}

fn collect_type_arg_vars(arg: &typed_ir::TypeArg, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    match arg {
        typed_ir::TypeArg::Type(ty) => collect_type_vars(ty, vars),
        typed_ir::TypeArg::Bounds(bounds) => collect_type_bounds_vars(bounds, vars),
    }
}

fn infer_type_substitutions(
    template: &typed_ir::Type,
    actual: &typed_ir::Type,
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) {
    infer_type_substitutions_inner(template, actual, params, substitutions, 64);
}

fn infer_type_substitutions_inner(
    template: &typed_ir::Type,
    actual: &typed_ir::Type,
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    depth: usize,
) {
    if depth == 0 {
        return;
    }
    match (template, actual) {
        (typed_ir::Type::Var(var), actual) if params.contains(var) => {
            substitutions
                .entry(var.clone())
                .or_insert_with(|| actual.clone());
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
            infer_type_substitutions_inner(param, actual_param, params, substitutions, depth - 1);
            infer_type_substitutions_inner(
                param_effect,
                actual_param_effect,
                params,
                substitutions,
                depth - 1,
            );
            infer_type_substitutions_inner(
                ret_effect,
                actual_ret_effect,
                params,
                substitutions,
                depth - 1,
            );
            infer_type_substitutions_inner(ret, actual_ret, params, substitutions, depth - 1);
        }
        (typed_ir::Type::Tuple(items), typed_ir::Type::Tuple(actual_items))
            if items.len() == actual_items.len() =>
        {
            for (item, actual_item) in items.iter().zip(actual_items) {
                infer_type_substitutions_inner(item, actual_item, params, substitutions, depth - 1);
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
                    );
                }
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
                    infer_type_substitutions_inner(
                        payload,
                        actual_payload,
                        params,
                        substitutions,
                        depth - 1,
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
        ) if items.len() == actual_items.len() => {
            for (item, actual_item) in items.iter().zip(actual_items) {
                infer_type_substitutions_inner(item, actual_item, params, substitutions, depth - 1);
            }
            infer_type_substitutions_inner(tail, actual_tail, params, substitutions, depth - 1);
        }
        (typed_ir::Type::Union(items) | typed_ir::Type::Inter(items), actual) => {
            for item in items {
                infer_type_substitutions_inner(item, actual, params, substitutions, depth - 1);
            }
        }
        (typed_ir::Type::Recursive { body, .. }, actual) => {
            infer_type_substitutions_inner(body, actual, params, substitutions, depth - 1);
        }
        (template, typed_ir::Type::Recursive { body, .. }) => {
            infer_type_substitutions_inner(template, body, params, substitutions, depth - 1);
        }
        _ => {}
    }
}

fn infer_type_arg_substitutions(
    template: &typed_ir::TypeArg,
    actual: &typed_ir::TypeArg,
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    depth: usize,
) {
    match (template, actual) {
        (typed_ir::TypeArg::Type(template), typed_ir::TypeArg::Type(actual)) => {
            infer_type_substitutions_inner(template, actual, params, substitutions, depth);
        }
        (typed_ir::TypeArg::Bounds(template), typed_ir::TypeArg::Bounds(actual)) => {
            infer_type_bounds_substitutions(template, actual, params, substitutions, depth);
        }
        _ => {}
    }
}

fn infer_type_bounds_substitutions(
    template: &typed_ir::TypeBounds,
    actual: &typed_ir::TypeBounds,
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    depth: usize,
) {
    if let (Some(template), Some(actual)) = (template.lower.as_deref(), actual.lower.as_deref()) {
        infer_type_substitutions_inner(template, actual, params, substitutions, depth);
    }
    if let (Some(template), Some(actual)) = (template.upper.as_deref(), actual.upper.as_deref()) {
        infer_type_substitutions_inner(template, actual, params, substitutions, depth);
    }
}

fn substitution_map_to_list(
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> Vec<typed_ir::TypeSubstitution> {
    substitutions
        .iter()
        .map(|(var, ty)| typed_ir::TypeSubstitution {
            var: var.clone(),
            ty: ty.clone(),
        })
        .collect()
}

pub(crate) fn rewrite_role_method_calls(module: &mut Module) -> bool {
    let candidates = role_method_candidates(module);
    if candidates.is_empty() {
        return false;
    }
    let reachable = super::reachable_paths(module);
    let mut changed = false;
    for binding in &mut module.bindings {
        if !reachable.contains(&binding.name) {
            continue;
        }
        let mut local_types = super::apply_spine::binding_local_types(binding);
        changed |= rewrite_role_method_expr(&mut binding.body, &mut local_types, &candidates);
    }
    for expr in &mut module.root_exprs {
        changed |= rewrite_role_method_expr(expr, &mut HashMap::new(), &candidates);
    }
    changed
}

pub(crate) fn rewrite_root_role_method_calls(module: &mut Module) -> bool {
    let candidates = role_method_candidates(module);
    if candidates.is_empty() {
        return false;
    }
    let mut changed = false;
    for expr in &mut module.root_exprs {
        changed |= rewrite_role_method_expr(expr, &mut HashMap::new(), &candidates);
    }
    changed
}

#[derive(Clone)]
struct RoleMethodCandidate {
    role: typed_ir::Path,
    member: typed_ir::Name,
    value: typed_ir::Path,
    inputs: Vec<typed_ir::TypeBounds>,
    callee_type: RuntimeType,
}

fn role_method_candidates(module: &Module) -> Vec<RoleMethodCandidate> {
    let bindings = module
        .bindings
        .iter()
        .map(|binding| (binding.name.clone(), binding))
        .collect::<HashMap<_, _>>();
    let mut seen = HashSet::new();
    let mut candidates = Vec::new();
    for role_impl in &module.role_impls {
        for member in &role_impl.members {
            let key = (
                role_impl.role.clone(),
                member.name.clone(),
                member.value.clone(),
            );
            if !seen.insert(key) {
                continue;
            }
            let Some(binding) = bindings.get(&member.value) else {
                continue;
            };
            candidates.push(RoleMethodCandidate {
                role: role_impl.role.clone(),
                member: member.name.clone(),
                value: member.value.clone(),
                inputs: role_impl.inputs.clone(),
                callee_type: runtime_type_from_core_value(binding.scheme.body.clone()),
            });
        }
    }
    candidates
}

fn rewrite_role_method_expr(
    expr: &mut Expr,
    local_types: &mut HashMap<typed_ir::Path, RuntimeType>,
    candidates: &[RoleMethodCandidate],
) -> bool {
    let mut changed = false;
    match &mut expr.kind {
        ExprKind::Apply { callee, arg, .. } => {
            changed |= rewrite_role_method_expr(callee, local_types, candidates);
            changed |= rewrite_role_method_expr(arg, local_types, candidates);
        }
        ExprKind::Lambda { param, body, .. } => {
            let previous = super::runtime_function_param(&expr.ty)
                .map(|param_ty| local_types.insert(super::path_from_name(param), param_ty));
            changed |= rewrite_role_method_expr(body, local_types, candidates);
            restore_local_type(local_types, super::path_from_name(param), previous);
        }
        ExprKind::BindHere { expr: body }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::AddId { thunk: body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. }
        | ExprKind::Select { base: body, .. }
        | ExprKind::Thunk { expr: body, .. } => {
            changed |= rewrite_role_method_expr(body, local_types, candidates);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            changed |= rewrite_role_method_expr(cond, local_types, candidates);
            changed |= rewrite_role_method_expr(then_branch, local_types, candidates);
            changed |= rewrite_role_method_expr(else_branch, local_types, candidates);
        }
        ExprKind::Tuple(items) => {
            for item in items {
                changed |= rewrite_role_method_expr(item, local_types, candidates);
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                changed |= rewrite_role_method_expr(&mut field.value, local_types, candidates);
            }
            if let Some(spread) = spread {
                changed |= rewrite_role_method_record_spread(spread, local_types, candidates);
            }
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                changed |= rewrite_role_method_expr(value, local_types, candidates);
            }
        }
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            let scrutinee_ty = super::apply_spine::expr_lower_type(scrutinee, local_types);
            changed |= rewrite_role_method_expr(scrutinee, local_types, candidates);
            for arm in arms {
                let mut arm_locals = local_types.clone();
                super::apply_spine::collect_pattern_local_types(
                    &arm.pattern,
                    Some(&scrutinee_ty),
                    &mut arm_locals,
                );
                if let Some(guard) = &mut arm.guard {
                    changed |= rewrite_role_method_expr(guard, &mut arm_locals, candidates);
                }
                changed |= rewrite_role_method_expr(&mut arm.body, &mut arm_locals, candidates);
            }
        }
        ExprKind::Block { stmts, tail } => {
            let mut scoped_locals = local_types.clone();
            for stmt in stmts {
                changed |= rewrite_role_method_stmt(stmt, &mut scoped_locals, candidates);
                super::apply_spine::collect_stmt_local_types(stmt, &mut scoped_locals);
            }
            if let Some(tail) = tail {
                changed |= rewrite_role_method_expr(tail, &mut scoped_locals, candidates);
            }
        }
        ExprKind::Handle { body, arms, .. } => {
            changed |= rewrite_role_method_expr(body, local_types, candidates);
            for arm in arms {
                let mut arm_locals = local_types.clone();
                super::apply_spine::collect_pattern_local_types(
                    &arm.payload,
                    None,
                    &mut arm_locals,
                );
                if let Some(resume) = &arm.resume {
                    arm_locals.insert(super::path_from_name(&resume.name), resume.ty.clone());
                }
                if let Some(guard) = &mut arm.guard {
                    changed |= rewrite_role_method_expr(guard, &mut arm_locals, candidates);
                }
                changed |= rewrite_role_method_expr(&mut arm.body, &mut arm_locals, candidates);
            }
        }
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
    if let Some((path, callee_type)) = resolve_role_method_apply(expr, local_types, candidates) {
        rewrite::replace_apply_spine_binding(expr, &path, &callee_type);
        changed = true;
    }
    changed
}

fn restore_local_type(
    local_types: &mut HashMap<typed_ir::Path, RuntimeType>,
    path: typed_ir::Path,
    previous: Option<Option<RuntimeType>>,
) {
    match previous {
        Some(Some(ty)) => {
            local_types.insert(path, ty);
        }
        Some(None) => {
            local_types.remove(&path);
        }
        None => {}
    }
}

fn rewrite_role_method_record_spread(
    spread: &mut yulang_runtime_ir::FinalizedRecordSpreadExpr,
    local_types: &mut HashMap<typed_ir::Path, RuntimeType>,
    candidates: &[RoleMethodCandidate],
) -> bool {
    match spread {
        yulang_runtime_ir::FinalizedRecordSpreadExpr::Head(expr)
        | yulang_runtime_ir::FinalizedRecordSpreadExpr::Tail(expr) => {
            rewrite_role_method_expr(expr, local_types, candidates)
        }
    }
}

fn rewrite_role_method_stmt(
    stmt: &mut yulang_runtime_ir::FinalizedStmt,
    local_types: &mut HashMap<typed_ir::Path, RuntimeType>,
    candidates: &[RoleMethodCandidate],
) -> bool {
    match stmt {
        yulang_runtime_ir::FinalizedStmt::Let { pattern: _, value } => {
            rewrite_role_method_expr(value, local_types, candidates)
        }
        yulang_runtime_ir::FinalizedStmt::Expr(expr)
        | yulang_runtime_ir::FinalizedStmt::Module { body: expr, .. } => {
            rewrite_role_method_expr(expr, local_types, candidates)
        }
    }
}

fn resolve_role_method_apply(
    expr: &Expr,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    candidates: &[RoleMethodCandidate],
) -> Option<(typed_ir::Path, RuntimeType)> {
    let spine = ApplySpine::new(expr)?;
    if let Some(resolution) = resolve_role_method_spine(&spine, local_types, candidates) {
        return Some(resolution);
    }
    resolve_impl_method_spine(&spine, local_types, candidates)
}

fn resolve_role_method_spine(
    spine: &ApplySpine<'_>,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    candidates: &[RoleMethodCandidate],
) -> Option<(typed_ir::Path, RuntimeType)> {
    let (role, member) = role_method_parts(spine.binding)?;
    let receiver = spine.steps.first()?;
    let receiver_types = role_receiver_types(receiver, local_types);
    let mut best = None;
    let mut ambiguous = false;
    for candidate in candidates
        .iter()
        .filter(|candidate| candidate.role == role && candidate.member == member)
    {
        let Some(score) =
            role_method_candidate_score(candidate, &receiver_types, spine, local_types)
        else {
            continue;
        };
        match best {
            None => {
                best = Some((score, candidate));
                ambiguous = false;
            }
            Some((best_score, _)) if score > best_score => {
                best = Some((score, candidate));
                ambiguous = false;
            }
            Some((best_score, _)) if score == best_score => {
                ambiguous = true;
            }
            Some(_) => {}
        }
    }
    if ambiguous {
        return None;
    }
    best.map(|(_, candidate)| (candidate.value.clone(), candidate.callee_type.clone()))
}

fn resolve_impl_method_spine(
    spine: &ApplySpine<'_>,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    candidates: &[RoleMethodCandidate],
) -> Option<(typed_ir::Path, RuntimeType)> {
    let member = impl_method_member(spine.binding)?;
    let receiver = spine.steps.first()?;
    let receiver_types = role_receiver_types(receiver, local_types);
    let mut best = None;
    let mut ambiguous = false;
    for candidate in candidates
        .iter()
        .filter(|candidate| candidate.member == *member)
    {
        let Some(score) =
            role_method_candidate_score(candidate, &receiver_types, spine, local_types)
        else {
            continue;
        };
        match best {
            None => {
                best = Some((score, candidate));
                ambiguous = false;
            }
            Some((best_score, _)) if score > best_score => {
                best = Some((score, candidate));
                ambiguous = false;
            }
            Some((best_score, _)) if score == best_score => {
                ambiguous = true;
            }
            Some(_) => {}
        }
    }
    if ambiguous {
        return None;
    }
    let (_, candidate) = best?;
    if candidate.value == *spine.binding {
        return None;
    }
    Some((candidate.value.clone(), candidate.callee_type.clone()))
}

fn role_method_parts(path: &typed_ir::Path) -> Option<(typed_ir::Path, typed_ir::Name)> {
    let (member, role) = path.segments.split_last()?;
    if role.is_empty() {
        return None;
    }
    Some((typed_ir::Path::new(role.to_vec()), member.clone()))
}

fn impl_method_member(path: &typed_ir::Path) -> Option<&typed_ir::Name> {
    if !path
        .segments
        .iter()
        .any(|segment| segment.0.starts_with("&impl#"))
    {
        return None;
    }
    path.segments.last()
}

fn role_receiver_types(
    receiver: &ApplyStep<'_>,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
) -> Vec<typed_ir::Type> {
    let mut out = Vec::new();
    if let Some(ty) = receiver
        .evidence
        .and_then(super::apply_spine::apply_observed_arg_type)
    {
        push_unique_type(&mut out, ty);
    }
    push_unique_type(&mut out, receiver.arg_type(local_types));
    push_role_receiver_expr_types(&mut out, receiver.arg, local_types);
    out
}

fn push_role_receiver_expr_types(
    out: &mut Vec<typed_ir::Type>,
    expr: &Expr,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
) {
    push_unique_type(
        out,
        super::runtime_type_to_core(super::apply_spine::expr_lower_type(expr, local_types)),
    );
    match &expr.kind {
        ExprKind::BindHere { expr } => {
            if let RuntimeType::Thunk { value, .. } = &expr.ty {
                push_unique_type(out, super::runtime_type_to_core((**value).clone()));
            }
            push_role_receiver_expr_types(out, expr, local_types);
        }
        ExprKind::Coerce { expr, to, .. } => {
            push_unique_type(out, to.clone());
            push_role_receiver_expr_types(out, expr, local_types);
        }
        _ => {}
    }
}

fn push_unique_type(out: &mut Vec<typed_ir::Type>, ty: typed_ir::Type) {
    if !out.iter().any(|existing| existing == &ty) {
        out.push(ty);
    }
}

fn role_method_candidate_score(
    candidate: &RoleMethodCandidate,
    receiver_types: &[typed_ir::Type],
    spine: &ApplySpine<'_>,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
) -> Option<usize> {
    let receiver_bounds = candidate.inputs.first()?;
    let receiver_score = receiver_types
        .iter()
        .filter_map(|receiver_ty| type_bounds_match_score(receiver_bounds, receiver_ty))
        .max()?;
    let spine_score = role_method_spine_score(&candidate.callee_type, spine, local_types);
    Some(receiver_score + spine_score)
}

fn role_method_spine_score(
    callee_type: &RuntimeType,
    spine: &ApplySpine<'_>,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
) -> usize {
    let mut current = super::runtime_type_to_core(callee_type.clone());
    let mut score = 0;
    for step in &spine.steps {
        let typed_ir::Type::Fun { param, ret, .. } = current else {
            break;
        };
        let arg_type = step.arg_type(local_types);
        score += soft_core_match_score(&param, &arg_type);
        if let Some(evidence) = step.evidence {
            score += soft_type_bounds_match_score(&evidence.arg, &param);
            if let Some(expected) = &evidence.expected_arg {
                score += soft_type_bounds_match_score(expected, &param);
            }
            score += soft_type_bounds_match_score(&evidence.result, &ret);
        }
        current = *ret;
    }
    score
}

fn soft_type_bounds_match_score(bounds: &typed_ir::TypeBounds, actual: &typed_ir::Type) -> usize {
    let mut score = 0;
    if let Some(lower) = bounds.lower.as_deref() {
        score += soft_core_match_score(lower, actual);
    }
    if let Some(upper) = bounds.upper.as_deref() {
        score += soft_core_match_score(actual, upper);
    }
    score
}

fn soft_core_match_score(left: &typed_ir::Type, right: &typed_ir::Type) -> usize {
    core_subtype_match_score(left, right).unwrap_or(0)
}

fn type_bounds_match_score(
    bounds: &typed_ir::TypeBounds,
    actual: &typed_ir::Type,
) -> Option<usize> {
    let mut score = 0;
    if let Some(lower) = bounds.lower.as_deref() {
        let lower_score = core_subtype_match_score(lower, actual)?;
        score += lower_score;
    }
    if let Some(upper) = bounds.upper.as_deref() {
        let upper_score = core_subtype_match_score(actual, upper)?;
        score += upper_score;
    }
    Some(score)
}

pub(crate) fn core_subtype_match_score(
    sub: &typed_ir::Type,
    sup: &typed_ir::Type,
) -> Option<usize> {
    if sub == sup {
        return Some(8);
    }
    match (sub, sup) {
        (typed_ir::Type::Never, _) | (_, typed_ir::Type::Any) => Some(1),
        (typed_ir::Type::Var(_), _) | (_, typed_ir::Type::Var(_)) => Some(2),
        (typed_ir::Type::Union(items), sup) => items
            .iter()
            .map(|item| core_subtype_match_score(item, sup))
            .try_fold(1, |acc, score| score.map(|score| acc + score)),
        (sub, typed_ir::Type::Union(items)) => items
            .iter()
            .filter_map(|item| core_subtype_match_score(sub, item))
            .max()
            .map(|score| score + 1),
        (
            typed_ir::Type::Named { path, args },
            typed_ir::Type::Named {
                path: actual_path,
                args: actual_args,
            },
        ) if path == actual_path && args.len() == actual_args.len() => args
            .iter()
            .zip(actual_args)
            .map(|(left, right)| type_arg_match_score(left, right))
            .try_fold(4, |acc, score| score.map(|score| acc + score)),
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
        ) => Some(
            core_subtype_match_score(actual_param, param)?
                + core_subtype_match_score(param_effect, actual_param_effect)?
                + core_subtype_match_score(ret_effect, actual_ret_effect)?
                + core_subtype_match_score(ret, actual_ret)?,
        ),
        (typed_ir::Type::Tuple(items), typed_ir::Type::Tuple(actual_items))
            if items.len() == actual_items.len() =>
        {
            items
                .iter()
                .zip(actual_items)
                .map(|(left, right)| core_subtype_match_score(left, right))
                .try_fold(4, |acc, score| score.map(|score| acc + score))
        }
        _ => None,
    }
}

fn type_arg_match_score(left: &typed_ir::TypeArg, right: &typed_ir::TypeArg) -> Option<usize> {
    match (left, right) {
        (typed_ir::TypeArg::Type(left), typed_ir::TypeArg::Type(right)) => {
            core_subtype_match_score(left, right)
        }
        (typed_ir::TypeArg::Bounds(left), typed_ir::TypeArg::Bounds(right)) => {
            let lower = match (left.lower.as_deref(), right.lower.as_deref()) {
                (Some(left), Some(right)) => core_subtype_match_score(left, right)?,
                (None, None) => 1,
                _ => return None,
            };
            let upper = match (left.upper.as_deref(), right.upper.as_deref()) {
                (Some(left), Some(right)) => core_subtype_match_score(left, right)?,
                (None, None) => 1,
                _ => return None,
            };
            Some(lower + upper)
        }
        _ => None,
    }
}
