use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum TypeSurfaceSite {
    BindingScheme,
    BindingRequirement,
    ExprTy,
    PatternTy,
    ApplyEvidence,
    JoinEvidence,
    TypeInstantiation,
    HandleEffect,
    ResumeBinding,
    ThunkEffect,
    ThunkValue,
    AddIdAllowed,
    CoerceFrom,
    CoerceTo,
}

pub(super) enum TypeSurfaceMut<'a> {
    Core(&'a mut typed_ir::Type),
    Runtime(&'a mut RuntimeType),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct TypeSurfaceResidual {
    pub site: TypeSurfaceSite,
    pub vars: Vec<typed_ir::TypeVar>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct BindingTypeSurfaceResidual {
    pub binding: typed_ir::Path,
    pub residual: TypeSurfaceResidual,
}

pub(super) fn collect_module_binding_runtime_type_residuals(
    module: &Module,
) -> Vec<BindingTypeSurfaceResidual> {
    let mut out = Vec::new();
    for binding in &module.bindings {
        out.extend(
            collect_binding_runtime_type_residuals(binding)
                .into_iter()
                .map(|residual| BindingTypeSurfaceResidual {
                    binding: binding.name.clone(),
                    residual,
                }),
        );
    }
    out
}

pub(super) fn collect_binding_runtime_type_residuals(
    binding: &Binding,
) -> Vec<TypeSurfaceResidual> {
    let mut residuals = Vec::new();
    let mut binding = binding.clone();
    visit_binding_type_surfaces_mut(&mut binding, &mut |site, surface| match surface {
        TypeSurfaceMut::Core(ty) => collect_core_type_surface_residuals(ty, site, &mut residuals),
        TypeSurfaceMut::Runtime(ty) => {
            collect_runtime_type_surface_residuals(ty, site, &mut residuals);
        }
    });
    residuals
}

pub(super) fn visit_binding_type_surfaces_mut<F>(binding: &mut Binding, visit: &mut F)
where
    F: FnMut(TypeSurfaceSite, TypeSurfaceMut<'_>),
{
    visit(
        TypeSurfaceSite::BindingScheme,
        TypeSurfaceMut::Core(&mut binding.scheme.body),
    );
    for requirement in &mut binding.scheme.requirements {
        visit_role_requirement_type_surfaces_mut(requirement, visit);
    }
    visit_expr_type_surfaces_mut(&mut binding.body, visit);
}

pub(super) fn visit_expr_type_surfaces_mut<F>(expr: &mut Expr, visit: &mut F)
where
    F: FnMut(TypeSurfaceSite, TypeSurfaceMut<'_>),
{
    visit(
        TypeSurfaceSite::ExprTy,
        TypeSurfaceMut::Runtime(&mut expr.ty),
    );
    match &mut expr.kind {
        ExprKind::Lambda { body, .. } => visit_expr_type_surfaces_mut(body, visit),
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        } => {
            visit_expr_type_surfaces_mut(callee, visit);
            visit_expr_type_surfaces_mut(arg, visit);
            if let Some(evidence) = evidence {
                visit_apply_evidence_type_surfaces_mut(evidence, visit);
            }
            if let Some(instantiation) = instantiation {
                visit_type_instantiation_surfaces_mut(instantiation, visit);
            }
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            evidence,
        } => {
            visit_expr_type_surfaces_mut(cond, visit);
            visit_expr_type_surfaces_mut(then_branch, visit);
            visit_expr_type_surfaces_mut(else_branch, visit);
            if let Some(evidence) = evidence {
                visit_join_evidence_type_surfaces_mut(evidence, visit);
            }
        }
        ExprKind::Tuple(items) => {
            for item in items {
                visit_expr_type_surfaces_mut(item, visit);
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                visit_expr_type_surfaces_mut(&mut field.value, visit);
            }
            visit_record_spread_expr_surfaces_mut(spread, visit);
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                visit_expr_type_surfaces_mut(value, visit);
            }
        }
        ExprKind::Select { base, .. } => visit_expr_type_surfaces_mut(base, visit),
        ExprKind::Match {
            scrutinee,
            arms,
            evidence,
        } => {
            visit_expr_type_surfaces_mut(scrutinee, visit);
            for arm in arms {
                visit_match_arm_type_surfaces_mut(arm, visit);
            }
            visit_join_evidence_type_surfaces_mut(evidence, visit);
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                visit_stmt_type_surfaces_mut(stmt, visit);
            }
            if let Some(tail) = tail {
                visit_expr_type_surfaces_mut(tail, visit);
            }
        }
        ExprKind::Handle {
            body,
            arms,
            evidence,
            handler,
        } => {
            visit_expr_type_surfaces_mut(body, visit);
            for arm in arms {
                visit_handle_arm_type_surfaces_mut(arm, visit);
            }
            visit_join_evidence_type_surfaces_mut(evidence, visit);
            visit_handle_effect_type_surfaces_mut(handler, visit);
        }
        ExprKind::BindHere { expr } | ExprKind::Pack { expr, .. } => {
            visit_expr_type_surfaces_mut(expr, visit);
        }
        ExprKind::Thunk {
            effect,
            value,
            expr,
        } => {
            visit(TypeSurfaceSite::ThunkEffect, TypeSurfaceMut::Core(effect));
            visit(TypeSurfaceSite::ThunkValue, TypeSurfaceMut::Runtime(value));
            visit_expr_type_surfaces_mut(expr, visit);
        }
        ExprKind::Coerce { from, to, expr } => {
            visit(TypeSurfaceSite::CoerceFrom, TypeSurfaceMut::Core(from));
            visit(TypeSurfaceSite::CoerceTo, TypeSurfaceMut::Core(to));
            visit_expr_type_surfaces_mut(expr, visit);
        }
        ExprKind::LocalPushId { body, .. } => {
            visit_expr_type_surfaces_mut(body, visit);
        }
        ExprKind::AddId { allowed, thunk, .. } => {
            visit(TypeSurfaceSite::AddIdAllowed, TypeSurfaceMut::Core(allowed));
            visit_expr_type_surfaces_mut(thunk, visit);
        }
        ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::Var(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
}

pub(super) fn visit_stmt_type_surfaces_mut<F>(stmt: &mut Stmt, visit: &mut F)
where
    F: FnMut(TypeSurfaceSite, TypeSurfaceMut<'_>),
{
    match stmt {
        Stmt::Let { pattern, value } => {
            visit_pattern_type_surfaces_mut(pattern, visit);
            visit_expr_type_surfaces_mut(value, visit);
        }
        Stmt::Expr(expr) | Stmt::Module { body: expr, .. } => {
            visit_expr_type_surfaces_mut(expr, visit);
        }
    }
}

pub(super) fn visit_pattern_type_surfaces_mut<F>(pattern: &mut Pattern, visit: &mut F)
where
    F: FnMut(TypeSurfaceSite, TypeSurfaceMut<'_>),
{
    match pattern {
        Pattern::Wildcard { ty }
        | Pattern::Bind { ty, .. }
        | Pattern::Lit { ty, .. }
        | Pattern::Tuple { ty, .. }
        | Pattern::List { ty, .. }
        | Pattern::Record { ty, .. }
        | Pattern::Variant { ty, .. }
        | Pattern::Or { ty, .. }
        | Pattern::As { ty, .. } => {
            visit(TypeSurfaceSite::PatternTy, TypeSurfaceMut::Runtime(ty));
        }
    }
    match pattern {
        Pattern::Tuple { items, .. } => {
            for item in items {
                visit_pattern_type_surfaces_mut(item, visit);
            }
        }
        Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            for item in prefix {
                visit_pattern_type_surfaces_mut(item, visit);
            }
            if let Some(spread) = spread {
                visit_pattern_type_surfaces_mut(spread, visit);
            }
            for item in suffix {
                visit_pattern_type_surfaces_mut(item, visit);
            }
        }
        Pattern::Record { fields, spread, .. } => {
            for field in fields {
                visit_pattern_type_surfaces_mut(&mut field.pattern, visit);
                if let Some(default) = &mut field.default {
                    visit_expr_type_surfaces_mut(default, visit);
                }
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadPattern::Head(pattern) | RecordSpreadPattern::Tail(pattern) => {
                        visit_pattern_type_surfaces_mut(pattern, visit);
                    }
                }
            }
        }
        Pattern::Variant { value, .. } => {
            if let Some(value) = value {
                visit_pattern_type_surfaces_mut(value, visit);
            }
        }
        Pattern::Or { left, right, .. } => {
            visit_pattern_type_surfaces_mut(left, visit);
            visit_pattern_type_surfaces_mut(right, visit);
        }
        Pattern::As { pattern, .. } => visit_pattern_type_surfaces_mut(pattern, visit),
        Pattern::Wildcard { .. } | Pattern::Bind { .. } | Pattern::Lit { .. } => {}
    }
}

fn visit_role_requirement_type_surfaces_mut<F>(
    requirement: &mut typed_ir::RoleRequirement,
    visit: &mut F,
) where
    F: FnMut(TypeSurfaceSite, TypeSurfaceMut<'_>),
{
    for arg in &mut requirement.args {
        match arg {
            typed_ir::RoleRequirementArg::Input(bounds)
            | typed_ir::RoleRequirementArg::Associated { bounds, .. } => {
                visit_type_bounds_surfaces_mut(bounds, TypeSurfaceSite::BindingRequirement, visit);
            }
        }
    }
}

fn visit_record_spread_expr_surfaces_mut<F>(spread: &mut Option<RecordSpreadExpr>, visit: &mut F)
where
    F: FnMut(TypeSurfaceSite, TypeSurfaceMut<'_>),
{
    if let Some(spread) = spread {
        match spread {
            RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                visit_expr_type_surfaces_mut(expr, visit);
            }
        }
    }
}

fn visit_match_arm_type_surfaces_mut<F>(arm: &mut MatchArm, visit: &mut F)
where
    F: FnMut(TypeSurfaceSite, TypeSurfaceMut<'_>),
{
    visit_pattern_type_surfaces_mut(&mut arm.pattern, visit);
    if let Some(guard) = &mut arm.guard {
        visit_expr_type_surfaces_mut(guard, visit);
    }
    visit_expr_type_surfaces_mut(&mut arm.body, visit);
}

fn visit_handle_arm_type_surfaces_mut<F>(arm: &mut HandleArm, visit: &mut F)
where
    F: FnMut(TypeSurfaceSite, TypeSurfaceMut<'_>),
{
    visit_pattern_type_surfaces_mut(&mut arm.payload, visit);
    if let Some(resume) = &mut arm.resume {
        visit(
            TypeSurfaceSite::ResumeBinding,
            TypeSurfaceMut::Runtime(&mut resume.ty),
        );
    }
    if let Some(guard) = &mut arm.guard {
        visit_expr_type_surfaces_mut(guard, visit);
    }
    visit_expr_type_surfaces_mut(&mut arm.body, visit);
}

fn visit_apply_evidence_type_surfaces_mut<F>(evidence: &mut typed_ir::ApplyEvidence, visit: &mut F)
where
    F: FnMut(TypeSurfaceSite, TypeSurfaceMut<'_>),
{
    visit_type_bounds_surfaces_mut(&mut evidence.callee, TypeSurfaceSite::ApplyEvidence, visit);
    if let Some(expected) = &mut evidence.expected_callee {
        visit_type_bounds_surfaces_mut(expected, TypeSurfaceSite::ApplyEvidence, visit);
    }
    visit_type_bounds_surfaces_mut(&mut evidence.arg, TypeSurfaceSite::ApplyEvidence, visit);
    if let Some(expected) = &mut evidence.expected_arg {
        visit_type_bounds_surfaces_mut(expected, TypeSurfaceSite::ApplyEvidence, visit);
    }
    visit_type_bounds_surfaces_mut(&mut evidence.result, TypeSurfaceSite::ApplyEvidence, visit);
    if let Some(principal) = &mut evidence.principal_callee {
        visit(
            TypeSurfaceSite::ApplyEvidence,
            TypeSurfaceMut::Core(principal),
        );
    }
    for substitution in &mut evidence.substitutions {
        visit(
            TypeSurfaceSite::ApplyEvidence,
            TypeSurfaceMut::Core(&mut substitution.ty),
        );
    }
    for candidate in &mut evidence.substitution_candidates {
        visit(
            TypeSurfaceSite::ApplyEvidence,
            TypeSurfaceMut::Core(&mut candidate.ty),
        );
    }
    if let Some(plan) = &mut evidence.principal_elaboration {
        visit_principal_elaboration_plan_surfaces_mut(plan, visit);
    }
}

fn visit_principal_elaboration_plan_surfaces_mut<F>(
    plan: &mut typed_ir::PrincipalElaborationPlan,
    visit: &mut F,
) where
    F: FnMut(TypeSurfaceSite, TypeSurfaceMut<'_>),
{
    visit(
        TypeSurfaceSite::ApplyEvidence,
        TypeSurfaceMut::Core(&mut plan.principal_callee),
    );
    for substitution in &mut plan.substitutions {
        visit(
            TypeSurfaceSite::ApplyEvidence,
            TypeSurfaceMut::Core(&mut substitution.ty),
        );
    }
    for arg in &mut plan.args {
        visit_type_bounds_surfaces_mut(&mut arg.intrinsic, TypeSurfaceSite::ApplyEvidence, visit);
        if let Some(contextual) = &mut arg.contextual {
            visit_type_bounds_surfaces_mut(contextual, TypeSurfaceSite::ApplyEvidence, visit);
        }
        if let Some(expected) = &mut arg.expected_runtime {
            visit(
                TypeSurfaceSite::ApplyEvidence,
                TypeSurfaceMut::Core(expected),
            );
        }
    }
    visit_type_bounds_surfaces_mut(
        &mut plan.result.intrinsic,
        TypeSurfaceSite::ApplyEvidence,
        visit,
    );
    if let Some(contextual) = &mut plan.result.contextual {
        visit_type_bounds_surfaces_mut(contextual, TypeSurfaceSite::ApplyEvidence, visit);
    }
    if let Some(expected) = &mut plan.result.expected_runtime {
        visit(
            TypeSurfaceSite::ApplyEvidence,
            TypeSurfaceMut::Core(expected),
        );
    }
    for adapter in &mut plan.adapters {
        visit(
            TypeSurfaceSite::ApplyEvidence,
            TypeSurfaceMut::Core(&mut adapter.actual),
        );
        visit(
            TypeSurfaceSite::ApplyEvidence,
            TypeSurfaceMut::Core(&mut adapter.expected),
        );
    }
}

fn visit_type_instantiation_surfaces_mut<F>(instantiation: &mut TypeInstantiation, visit: &mut F)
where
    F: FnMut(TypeSurfaceSite, TypeSurfaceMut<'_>),
{
    for substitution in &mut instantiation.args {
        visit(
            TypeSurfaceSite::TypeInstantiation,
            TypeSurfaceMut::Core(&mut substitution.ty),
        );
    }
}

fn visit_join_evidence_type_surfaces_mut<F>(evidence: &mut JoinEvidence, visit: &mut F)
where
    F: FnMut(TypeSurfaceSite, TypeSurfaceMut<'_>),
{
    visit(
        TypeSurfaceSite::JoinEvidence,
        TypeSurfaceMut::Core(&mut evidence.result),
    );
}

fn visit_handle_effect_type_surfaces_mut<F>(handler: &mut HandleEffect, visit: &mut F)
where
    F: FnMut(TypeSurfaceSite, TypeSurfaceMut<'_>),
{
    if let Some(residual) = &mut handler.residual_before {
        visit(
            TypeSurfaceSite::HandleEffect,
            TypeSurfaceMut::Core(residual),
        );
    }
    if let Some(residual) = &mut handler.residual_after {
        visit(
            TypeSurfaceSite::HandleEffect,
            TypeSurfaceMut::Core(residual),
        );
    }
}

fn visit_type_bounds_surfaces_mut<F>(
    bounds: &mut typed_ir::TypeBounds,
    site: TypeSurfaceSite,
    visit: &mut F,
) where
    F: FnMut(TypeSurfaceSite, TypeSurfaceMut<'_>),
{
    if let Some(lower) = bounds.lower.as_deref_mut() {
        visit(site, TypeSurfaceMut::Core(lower));
    }
    if let Some(upper) = bounds.upper.as_deref_mut() {
        visit(site, TypeSurfaceMut::Core(upper));
    }
}

fn collect_runtime_type_surface_residuals(
    ty: &RuntimeType,
    site: TypeSurfaceSite,
    residuals: &mut Vec<TypeSurfaceResidual>,
) {
    let mut vars = BTreeSet::new();
    collect_hir_type_vars(ty, &mut vars);
    push_surface_residual(site, vars, residuals);
}

fn collect_core_type_surface_residuals(
    ty: &typed_ir::Type,
    site: TypeSurfaceSite,
    residuals: &mut Vec<TypeSurfaceResidual>,
) {
    let mut vars = BTreeSet::new();
    collect_core_type_vars(ty, &mut vars);
    push_surface_residual(site, vars, residuals);
}

fn push_surface_residual(
    site: TypeSurfaceSite,
    vars: BTreeSet<typed_ir::TypeVar>,
    residuals: &mut Vec<TypeSurfaceResidual>,
) {
    if vars.is_empty() {
        return;
    }
    residuals.push(TypeSurfaceResidual {
        site,
        vars: vars.into_iter().collect(),
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::EffectIdRef;

    #[test]
    fn residuals_report_add_id_allowed_site() {
        let var = typed_ir::TypeVar("e".to_string());
        let binding = binding_with_body(Expr::typed(
            ExprKind::AddId {
                id: EffectIdRef::Peek,
                allowed: typed_ir::Type::Var(var.clone()),
                active: true,
                thunk: Box::new(unit_thunk()),
            },
            RuntimeType::thunk(typed_ir::Type::Never, RuntimeType::core(unit_type())),
        ));

        let residuals = collect_binding_runtime_type_residuals(&binding);

        assert!(residuals.iter().any(|residual| {
            residual.site == TypeSurfaceSite::AddIdAllowed && residual.vars == vec![var.clone()]
        }));
    }

    #[test]
    fn residuals_report_pattern_site() {
        let var = typed_ir::TypeVar("p".to_string());
        let binding = binding_with_body(Expr::typed(
            ExprKind::Block {
                stmts: vec![Stmt::Let {
                    pattern: Pattern::Bind {
                        name: typed_ir::Name("x".to_string()),
                        ty: RuntimeType::core(typed_ir::Type::Var(var.clone())),
                    },
                    value: unit_expr(),
                }],
                tail: Some(Box::new(unit_expr())),
            },
            RuntimeType::core(unit_type()),
        ));

        let residuals = collect_binding_runtime_type_residuals(&binding);

        assert!(residuals.iter().any(|residual| {
            residual.site == TypeSurfaceSite::PatternTy && residual.vars == vec![var.clone()]
        }));
    }

    #[test]
    fn module_residuals_keep_binding_owner() {
        let var = typed_ir::TypeVar("a".to_string());
        let binding = Binding {
            name: typed_ir::Path::from_name(typed_ir::Name("owner".to_string())),
            type_params: Vec::new(),
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: typed_ir::Type::Var(var.clone()),
            },
            body: unit_expr(),
        };
        let module = Module {
            path: typed_ir::Path::from_name(typed_ir::Name("test".to_string())),
            bindings: vec![binding],
            root_exprs: Vec::new(),
            roots: Vec::new(),
            role_impls: Vec::new(),
        };

        let residuals = collect_module_binding_runtime_type_residuals(&module);

        assert_eq!(residuals.len(), 1);
        assert_eq!(
            residuals[0].binding,
            typed_ir::Path::from_name(typed_ir::Name("owner".to_string()))
        );
        assert_eq!(residuals[0].residual.site, TypeSurfaceSite::BindingScheme);
        assert_eq!(residuals[0].residual.vars, vec![var]);
    }

    #[test]
    fn residuals_report_apply_evidence_candidates_and_plan_slots() {
        let candidate_var = typed_ir::TypeVar("candidate".to_string());
        let plan_var = typed_ir::TypeVar("plan".to_string());
        let runtime_var = typed_ir::TypeVar("runtime".to_string());
        let binding = binding_with_body(Expr::typed(
            ExprKind::Apply {
                callee: Box::new(Expr::typed(
                    ExprKind::Var(typed_ir::Path::from_name(typed_ir::Name("f".to_string()))),
                    RuntimeType::fun(
                        RuntimeType::core(unit_type()),
                        RuntimeType::core(unit_type()),
                    ),
                )),
                arg: Box::new(unit_expr()),
                evidence: Some(typed_ir::ApplyEvidence {
                    callee_source_edge: None,
                    arg_source_edge: None,
                    callee: typed_ir::TypeBounds::exact(unit_type()),
                    expected_callee: None,
                    arg: typed_ir::TypeBounds::exact(unit_type()),
                    expected_arg: None,
                    result: typed_ir::TypeBounds::exact(unit_type()),
                    principal_callee: None,
                    substitutions: Vec::new(),
                    substitution_candidates: vec![typed_ir::PrincipalSubstitutionCandidate {
                        var: candidate_var.clone(),
                        relation: typed_ir::PrincipalCandidateRelation::Exact,
                        ty: typed_ir::Type::Var(candidate_var.clone()),
                        source_edge: None,
                        path: Vec::new(),
                    }],
                    role_method: false,
                    principal_elaboration: Some(typed_ir::PrincipalElaborationPlan {
                        target: None,
                        principal_callee: typed_ir::Type::Var(plan_var.clone()),
                        substitutions: Vec::new(),
                        args: vec![typed_ir::PrincipalElaborationArg {
                            index: 0,
                            intrinsic: typed_ir::TypeBounds::exact(unit_type()),
                            contextual: None,
                            expected_runtime: Some(typed_ir::Type::Var(runtime_var.clone())),
                            source_edge: None,
                        }],
                        result: typed_ir::PrincipalElaborationResult {
                            intrinsic: typed_ir::TypeBounds::exact(unit_type()),
                            contextual: None,
                            expected_runtime: None,
                        },
                        adapters: Vec::new(),
                        complete: true,
                        incomplete_reasons: Vec::new(),
                    }),
                }),
                instantiation: None,
            },
            RuntimeType::core(unit_type()),
        ));

        let residuals = collect_binding_runtime_type_residuals(&binding);
        let vars = residuals
            .iter()
            .filter(|residual| residual.site == TypeSurfaceSite::ApplyEvidence)
            .flat_map(|residual| residual.vars.iter().cloned())
            .collect::<BTreeSet<_>>();

        assert!(vars.contains(&candidate_var));
        assert!(vars.contains(&plan_var));
        assert!(vars.contains(&runtime_var));
    }

    fn binding_with_body(body: Expr) -> Binding {
        Binding {
            name: typed_ir::Path::from_name(typed_ir::Name("main".to_string())),
            type_params: Vec::new(),
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: unit_type(),
            },
            body,
        }
    }

    fn unit_thunk() -> Expr {
        Expr::typed(
            ExprKind::Thunk {
                effect: typed_ir::Type::Never,
                value: RuntimeType::core(unit_type()),
                expr: Box::new(unit_expr()),
            },
            RuntimeType::thunk(typed_ir::Type::Never, RuntimeType::core(unit_type())),
        )
    }

    fn unit_expr() -> Expr {
        Expr::typed(
            ExprKind::Lit(typed_ir::Lit::Unit),
            RuntimeType::core(unit_type()),
        )
    }

    fn unit_type() -> typed_ir::Type {
        typed_ir::Type::Named {
            path: typed_ir::Path::from_name(typed_ir::Name("unit".to_string())),
            args: Vec::new(),
        }
    }
}
