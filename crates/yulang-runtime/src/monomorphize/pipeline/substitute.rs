use super::*;

pub(super) fn substitute_binding(
    mut binding: Binding,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> Binding {
    visit_binding_type_surfaces_mut(&mut binding, &mut |_, surface| {
        substitute_type_surface(surface, substitutions);
    });
    binding
}

fn substitute_type_surface(
    surface: TypeSurfaceMut<'_>,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) {
    match surface {
        TypeSurfaceMut::Core(ty) => {
            *ty = substitute_type(ty, substitutions);
        }
        TypeSurfaceMut::Runtime(ty) => {
            let source = std::mem::replace(ty, RuntimeType::Unknown);
            *ty = substitute_hir_type(source, substitutions);
        }
    }
}

pub(super) fn substitute_hir_type(
    ty: RuntimeType,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> RuntimeType {
    let allowed_vars = BTreeSet::new();
    let ty = match ty {
        RuntimeType::Unknown => RuntimeType::unknown(),
        RuntimeType::Core(ty) => RuntimeType::core(project_runtime_type_with_vars(
            &substitute_type(&ty, substitutions),
            &allowed_vars,
        )),
        RuntimeType::Fun { param, ret } => RuntimeType::fun(
            substitute_hir_type(*param, substitutions),
            substitute_hir_type(*ret, substitutions),
        ),
        RuntimeType::Thunk { effect, value } => RuntimeType::thunk(
            project_runtime_effect(&substitute_type(&effect, substitutions)),
            substitute_hir_type(*value, substitutions),
        ),
    };
    normalize_hir_function_type(ty)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn substitute_binding_covers_apply_evidence_type_surfaces() {
        let var = typed_ir::TypeVar("a".to_string());
        let unit = unit_type();
        let mut substitutions = BTreeMap::new();
        substitutions.insert(var.clone(), unit.clone());
        let binding = Binding {
            name: path("main"),
            type_params: vec![var.clone()],
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: typed_ir::Type::Var(var.clone()),
            },
            body: Expr::typed(
                ExprKind::Apply {
                    callee: Box::new(Expr::typed(
                        ExprKind::Var(path("f")),
                        RuntimeType::fun(
                            RuntimeType::core(typed_ir::Type::Var(var.clone())),
                            RuntimeType::core(typed_ir::Type::Var(var.clone())),
                        ),
                    )),
                    arg: Box::new(unit_expr()),
                    evidence: Some(apply_evidence_with_var(&var)),
                    instantiation: Some(TypeInstantiation {
                        target: path("f"),
                        args: vec![crate::ir::TypeSubstitution {
                            var: var.clone(),
                            ty: typed_ir::Type::Var(var.clone()),
                        }],
                    }),
                },
                RuntimeType::core(typed_ir::Type::Var(var.clone())),
            ),
        };

        let substituted = substitute_binding(binding, &substitutions);
        let residuals = collect_binding_runtime_type_residuals(&substituted);

        assert!(
            residuals
                .iter()
                .flat_map(|residual| residual.vars.iter())
                .all(|residual| residual != &var),
            "{residuals:?}"
        );
    }

    fn apply_evidence_with_var(var: &typed_ir::TypeVar) -> typed_ir::ApplyEvidence {
        typed_ir::ApplyEvidence {
            callee_source_edge: None,
            arg_source_edge: None,
            callee: typed_ir::TypeBounds::exact(typed_ir::Type::Var(var.clone())),
            expected_callee: Some(typed_ir::TypeBounds::exact(typed_ir::Type::Var(
                var.clone(),
            ))),
            arg: typed_ir::TypeBounds::exact(typed_ir::Type::Var(var.clone())),
            expected_arg: Some(typed_ir::TypeBounds::exact(typed_ir::Type::Var(
                var.clone(),
            ))),
            result: typed_ir::TypeBounds::exact(typed_ir::Type::Var(var.clone())),
            principal_callee: Some(typed_ir::Type::Var(var.clone())),
            substitutions: vec![typed_ir::TypeSubstitution {
                var: var.clone(),
                ty: typed_ir::Type::Var(var.clone()),
            }],
            substitution_candidates: vec![typed_ir::PrincipalSubstitutionCandidate {
                var: var.clone(),
                relation: typed_ir::PrincipalCandidateRelation::Exact,
                ty: typed_ir::Type::Var(var.clone()),
                source_edge: None,
                path: Vec::new(),
            }],
            role_method: false,
            principal_elaboration: Some(typed_ir::PrincipalElaborationPlan {
                target: None,
                principal_callee: typed_ir::Type::Var(var.clone()),
                substitutions: vec![typed_ir::TypeSubstitution {
                    var: var.clone(),
                    ty: typed_ir::Type::Var(var.clone()),
                }],
                args: vec![typed_ir::PrincipalElaborationArg {
                    index: 0,
                    intrinsic: typed_ir::TypeBounds::exact(typed_ir::Type::Var(var.clone())),
                    contextual: Some(typed_ir::TypeBounds::exact(typed_ir::Type::Var(
                        var.clone(),
                    ))),
                    expected_runtime: Some(typed_ir::Type::Var(var.clone())),
                    source_edge: None,
                }],
                result: typed_ir::PrincipalElaborationResult {
                    intrinsic: typed_ir::TypeBounds::exact(typed_ir::Type::Var(var.clone())),
                    contextual: Some(typed_ir::TypeBounds::exact(typed_ir::Type::Var(
                        var.clone(),
                    ))),
                    expected_runtime: Some(typed_ir::Type::Var(var.clone())),
                },
                adapters: vec![typed_ir::PrincipalAdapterHole {
                    kind: typed_ir::PrincipalAdapterKind::Coerce,
                    source_edge: None,
                    actual: typed_ir::Type::Var(var.clone()),
                    expected: typed_ir::Type::Var(var.clone()),
                }],
                complete: true,
                incomplete_reasons: Vec::new(),
            }),
        }
    }

    fn unit_expr() -> Expr {
        Expr::typed(
            ExprKind::Lit(typed_ir::Lit::Unit),
            RuntimeType::core(unit_type()),
        )
    }

    fn unit_type() -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path("unit"),
            args: Vec::new(),
        }
    }

    fn path(name: &str) -> typed_ir::Path {
        typed_ir::Path::from_name(typed_ir::Name(name.to_string()))
    }
}
