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
    collect_core_type_surface_residuals(
        &binding.scheme.body,
        TypeSurfaceSite::BindingScheme,
        &mut residuals,
    );
    for requirement in &binding.scheme.requirements {
        collect_role_requirement_type_residuals(requirement, &mut residuals);
    }
    collect_expr_type_surface_residuals(&binding.body, &mut residuals);
    residuals
}

fn collect_role_requirement_type_residuals(
    requirement: &typed_ir::RoleRequirement,
    residuals: &mut Vec<TypeSurfaceResidual>,
) {
    for arg in &requirement.args {
        match arg {
            typed_ir::RoleRequirementArg::Input(bounds)
            | typed_ir::RoleRequirementArg::Associated { bounds, .. } => {
                collect_type_bounds_surface_residuals(
                    bounds,
                    TypeSurfaceSite::BindingRequirement,
                    residuals,
                );
            }
        }
    }
}

fn collect_expr_type_surface_residuals(expr: &Expr, residuals: &mut Vec<TypeSurfaceResidual>) {
    collect_runtime_type_surface_residuals(&expr.ty, TypeSurfaceSite::ExprTy, residuals);
    match &expr.kind {
        ExprKind::Lambda { body, .. } => collect_expr_type_surface_residuals(body, residuals),
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        } => {
            collect_expr_type_surface_residuals(callee, residuals);
            collect_expr_type_surface_residuals(arg, residuals);
            if let Some(evidence) = evidence {
                collect_apply_evidence_surface_residuals(evidence, residuals);
            }
            if let Some(instantiation) = instantiation {
                collect_type_instantiation_surface_residuals(instantiation, residuals);
            }
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            evidence,
        } => {
            collect_expr_type_surface_residuals(cond, residuals);
            collect_expr_type_surface_residuals(then_branch, residuals);
            collect_expr_type_surface_residuals(else_branch, residuals);
            if let Some(evidence) = evidence {
                collect_join_evidence_surface_residuals(evidence, residuals);
            }
        }
        ExprKind::Tuple(items) => {
            for item in items {
                collect_expr_type_surface_residuals(item, residuals);
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                collect_expr_type_surface_residuals(&field.value, residuals);
            }
            collect_record_spread_expr_surface_residuals(spread, residuals);
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                collect_expr_type_surface_residuals(value, residuals);
            }
        }
        ExprKind::Select { base, .. } => collect_expr_type_surface_residuals(base, residuals),
        ExprKind::Match {
            scrutinee,
            arms,
            evidence,
        } => {
            collect_expr_type_surface_residuals(scrutinee, residuals);
            for arm in arms {
                collect_match_arm_surface_residuals(arm, residuals);
            }
            collect_join_evidence_surface_residuals(evidence, residuals);
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                collect_stmt_type_surface_residuals(stmt, residuals);
            }
            if let Some(tail) = tail {
                collect_expr_type_surface_residuals(tail, residuals);
            }
        }
        ExprKind::Handle {
            body,
            arms,
            evidence,
            handler,
        } => {
            collect_expr_type_surface_residuals(body, residuals);
            for arm in arms {
                collect_pattern_type_surface_residuals(&arm.payload, residuals);
                if let Some(resume) = &arm.resume {
                    collect_runtime_type_surface_residuals(
                        &resume.ty,
                        TypeSurfaceSite::ResumeBinding,
                        residuals,
                    );
                }
                if let Some(guard) = &arm.guard {
                    collect_expr_type_surface_residuals(guard, residuals);
                }
                collect_expr_type_surface_residuals(&arm.body, residuals);
            }
            collect_join_evidence_surface_residuals(evidence, residuals);
            collect_handle_effect_surface_residuals(handler, residuals);
        }
        ExprKind::BindHere { expr } | ExprKind::Pack { expr, .. } => {
            collect_expr_type_surface_residuals(expr, residuals)
        }
        ExprKind::Thunk {
            effect,
            value,
            expr,
        } => {
            collect_core_type_surface_residuals(effect, TypeSurfaceSite::ThunkEffect, residuals);
            collect_runtime_type_surface_residuals(value, TypeSurfaceSite::ThunkValue, residuals);
            collect_expr_type_surface_residuals(expr, residuals);
        }
        ExprKind::Coerce { from, to, expr } => {
            collect_core_type_surface_residuals(from, TypeSurfaceSite::CoerceFrom, residuals);
            collect_core_type_surface_residuals(to, TypeSurfaceSite::CoerceTo, residuals);
            collect_expr_type_surface_residuals(expr, residuals);
        }
        ExprKind::LocalPushId { body, .. } => {
            collect_expr_type_surface_residuals(body, residuals);
        }
        ExprKind::AddId { allowed, thunk, .. } => {
            collect_core_type_surface_residuals(allowed, TypeSurfaceSite::AddIdAllowed, residuals);
            collect_expr_type_surface_residuals(thunk, residuals);
        }
        ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::Var(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
}

fn collect_stmt_type_surface_residuals(stmt: &Stmt, residuals: &mut Vec<TypeSurfaceResidual>) {
    match stmt {
        Stmt::Let { pattern, value } => {
            collect_pattern_type_surface_residuals(pattern, residuals);
            collect_expr_type_surface_residuals(value, residuals);
        }
        Stmt::Expr(expr) | Stmt::Module { body: expr, .. } => {
            collect_expr_type_surface_residuals(expr, residuals);
        }
    }
}

fn collect_match_arm_surface_residuals(arm: &MatchArm, residuals: &mut Vec<TypeSurfaceResidual>) {
    collect_pattern_type_surface_residuals(&arm.pattern, residuals);
    if let Some(guard) = &arm.guard {
        collect_expr_type_surface_residuals(guard, residuals);
    }
    collect_expr_type_surface_residuals(&arm.body, residuals);
}

fn collect_pattern_type_surface_residuals(
    pattern: &Pattern,
    residuals: &mut Vec<TypeSurfaceResidual>,
) {
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
            collect_runtime_type_surface_residuals(ty, TypeSurfaceSite::PatternTy, residuals);
        }
    }
    match pattern {
        Pattern::Tuple { items, .. } => {
            for item in items {
                collect_pattern_type_surface_residuals(item, residuals);
            }
        }
        Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            for item in prefix {
                collect_pattern_type_surface_residuals(item, residuals);
            }
            if let Some(spread) = spread {
                collect_pattern_type_surface_residuals(spread, residuals);
            }
            for item in suffix {
                collect_pattern_type_surface_residuals(item, residuals);
            }
        }
        Pattern::Record { fields, spread, .. } => {
            for field in fields {
                collect_pattern_type_surface_residuals(&field.pattern, residuals);
                if let Some(default) = &field.default {
                    collect_expr_type_surface_residuals(default, residuals);
                }
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadPattern::Head(pattern) | RecordSpreadPattern::Tail(pattern) => {
                        collect_pattern_type_surface_residuals(pattern, residuals);
                    }
                }
            }
        }
        Pattern::Variant { value, .. } => {
            if let Some(value) = value {
                collect_pattern_type_surface_residuals(value, residuals);
            }
        }
        Pattern::Or { left, right, .. } => {
            collect_pattern_type_surface_residuals(left, residuals);
            collect_pattern_type_surface_residuals(right, residuals);
        }
        Pattern::As { pattern, .. } => collect_pattern_type_surface_residuals(pattern, residuals),
        Pattern::Wildcard { .. } | Pattern::Bind { .. } | Pattern::Lit { .. } => {}
    }
}

fn collect_record_spread_expr_surface_residuals(
    spread: &Option<RecordSpreadExpr>,
    residuals: &mut Vec<TypeSurfaceResidual>,
) {
    if let Some(spread) = spread {
        match spread {
            RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                collect_expr_type_surface_residuals(expr, residuals);
            }
        }
    }
}

fn collect_apply_evidence_surface_residuals(
    evidence: &typed_ir::ApplyEvidence,
    residuals: &mut Vec<TypeSurfaceResidual>,
) {
    collect_type_bounds_surface_residuals(
        &evidence.callee,
        TypeSurfaceSite::ApplyEvidence,
        residuals,
    );
    if let Some(expected) = &evidence.expected_callee {
        collect_type_bounds_surface_residuals(expected, TypeSurfaceSite::ApplyEvidence, residuals);
    }
    collect_type_bounds_surface_residuals(&evidence.arg, TypeSurfaceSite::ApplyEvidence, residuals);
    if let Some(expected) = &evidence.expected_arg {
        collect_type_bounds_surface_residuals(expected, TypeSurfaceSite::ApplyEvidence, residuals);
    }
    collect_type_bounds_surface_residuals(
        &evidence.result,
        TypeSurfaceSite::ApplyEvidence,
        residuals,
    );
    if let Some(principal) = &evidence.principal_callee {
        collect_core_type_surface_residuals(principal, TypeSurfaceSite::ApplyEvidence, residuals);
    }
    for substitution in &evidence.substitutions {
        collect_core_type_surface_residuals(
            &substitution.ty,
            TypeSurfaceSite::ApplyEvidence,
            residuals,
        );
    }
    if let Some(plan) = &evidence.principal_elaboration {
        collect_core_type_surface_residuals(
            &plan.principal_callee,
            TypeSurfaceSite::ApplyEvidence,
            residuals,
        );
        for substitution in &plan.substitutions {
            collect_core_type_surface_residuals(
                &substitution.ty,
                TypeSurfaceSite::ApplyEvidence,
                residuals,
            );
        }
    }
}

fn collect_type_instantiation_surface_residuals(
    instantiation: &TypeInstantiation,
    residuals: &mut Vec<TypeSurfaceResidual>,
) {
    for substitution in &instantiation.args {
        collect_core_type_surface_residuals(
            &substitution.ty,
            TypeSurfaceSite::TypeInstantiation,
            residuals,
        );
    }
}

fn collect_join_evidence_surface_residuals(
    evidence: &JoinEvidence,
    residuals: &mut Vec<TypeSurfaceResidual>,
) {
    collect_core_type_surface_residuals(&evidence.result, TypeSurfaceSite::JoinEvidence, residuals);
}

fn collect_handle_effect_surface_residuals(
    handler: &HandleEffect,
    residuals: &mut Vec<TypeSurfaceResidual>,
) {
    if let Some(residual) = &handler.residual_before {
        collect_core_type_surface_residuals(residual, TypeSurfaceSite::HandleEffect, residuals);
    }
    if let Some(residual) = &handler.residual_after {
        collect_core_type_surface_residuals(residual, TypeSurfaceSite::HandleEffect, residuals);
    }
}

fn collect_type_bounds_surface_residuals(
    bounds: &typed_ir::TypeBounds,
    site: TypeSurfaceSite,
    residuals: &mut Vec<TypeSurfaceResidual>,
) {
    if let Some(lower) = bounds.lower.as_deref() {
        collect_core_type_surface_residuals(lower, site, residuals);
    }
    if let Some(upper) = bounds.upper.as_deref() {
        collect_core_type_surface_residuals(upper, site, residuals);
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
