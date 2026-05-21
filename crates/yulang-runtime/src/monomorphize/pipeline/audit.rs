use super::*;
use crate::runtime_intrinsic::binding_is_parametric_runtime_intrinsic;

pub(super) fn audit_monomorphized_module(module: &Module) -> RuntimeResult<()> {
    audit_no_residual_type_params(module)?;
    audit_no_residual_runtime_type_vars(module)
}

fn audit_no_residual_type_params(module: &Module) -> RuntimeResult<()> {
    for binding in &module.bindings {
        if binding_is_parametric_runtime_intrinsic(binding) {
            continue;
        }
        if binding.type_params.is_empty() {
            continue;
        }
        if std::env::var_os("YULANG_DEBUG_MONO_PIPELINE").is_some() {
            debug_residual_type_param_referrers(module, binding);
        }
        return Err(RuntimeError::ResidualPolymorphicBinding {
            path: binding.name.clone(),
            vars: binding.type_params.clone(),
            source: crate::diagnostic::ResidualPolymorphicSource::TypeParams,
        });
    }
    Ok(())
}

fn audit_no_residual_runtime_type_vars(module: &Module) -> RuntimeResult<()> {
    for (binding, residuals) in residual_runtime_type_vars_by_binding(module) {
        let vars = residuals
            .iter()
            .flat_map(|residual| residual.vars.iter().cloned())
            .collect::<BTreeSet<_>>();
        if vars.is_empty() {
            continue;
        }
        if std::env::var_os("YULANG_DEBUG_MONO_PIPELINE").is_some() {
            eprintln!(
                "residual runtime type vars in {:?}: {:?}",
                binding, residuals
            );
        }
        return Err(RuntimeError::ResidualPolymorphicBinding {
            path: binding,
            vars: vars.into_iter().collect(),
            source: crate::diagnostic::ResidualPolymorphicSource::RuntimeTypes,
        });
    }
    Ok(())
}

fn residual_runtime_type_vars_by_binding(
    module: &Module,
) -> Vec<(typed_ir::Path, Vec<TypeSurfaceResidual>)> {
    let mut out = Vec::<(typed_ir::Path, Vec<TypeSurfaceResidual>)>::new();
    let primitive_bindings = module
        .bindings
        .iter()
        .filter(|binding| binding_is_parametric_runtime_intrinsic(binding))
        .map(|binding| binding.name.clone())
        .collect::<HashSet<_>>();
    for item in collect_module_binding_runtime_type_residuals(module) {
        if primitive_bindings.contains(&item.binding) {
            continue;
        }
        if let Some((_, residuals)) = out.iter_mut().find(|(binding, _)| binding == &item.binding) {
            residuals.push(item.residual);
        } else {
            out.push((item.binding, vec![item.residual]));
        }
    }
    out
}

fn debug_residual_type_param_referrers(module: &Module, binding: &Binding) {
    let mut referrers = Vec::new();
    for candidate in &module.bindings {
        let mut vars = HashSet::new();
        collect_expr_vars(&candidate.body, &mut vars);
        if vars.contains(&binding.name) {
            referrers.push(candidate.name.clone());
        }
    }
    let mut root_refs = Vec::new();
    for (index, root) in module.root_exprs.iter().enumerate() {
        let mut vars = HashSet::new();
        collect_expr_vars(root, &mut vars);
        if vars.contains(&binding.name) {
            root_refs.push(index);
        }
    }
    eprintln!(
        "residual polymorphic binding {:?} is referenced by {:?}; root refs {:?}",
        binding.name, referrers, root_refs
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn audit_reports_residual_type_params() {
        let var = typed_ir::TypeVar("a".to_string());
        let module = module_with_binding(Binding {
            name: path("main"),
            type_params: vec![var.clone()],
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: unit_type(),
            },
            body: unit_expr(),
        });

        let err = audit_monomorphized_module(&module).unwrap_err();

        assert!(matches!(
            err,
            RuntimeError::ResidualPolymorphicBinding {
                source: crate::diagnostic::ResidualPolymorphicSource::TypeParams,
                ..
            }
        ));
    }

    #[test]
    fn audit_reports_runtime_type_surface_residuals() {
        let var = typed_ir::TypeVar("a".to_string());
        let module = module_with_binding(Binding {
            name: path("main"),
            type_params: Vec::new(),
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: typed_ir::Type::Var(var.clone()),
            },
            body: unit_expr(),
        });

        let err = audit_monomorphized_module(&module).unwrap_err();

        assert!(matches!(
            err,
            RuntimeError::ResidualPolymorphicBinding {
                source: crate::diagnostic::ResidualPolymorphicSource::RuntimeTypes,
                ..
            }
        ));
    }

    fn module_with_binding(binding: Binding) -> Module {
        Module {
            path: path("test"),
            bindings: vec![binding],
            root_exprs: Vec::new(),
            roots: Vec::new(),
            role_impls: Vec::new(),
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
