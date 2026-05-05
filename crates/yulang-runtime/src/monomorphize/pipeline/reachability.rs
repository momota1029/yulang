use super::*;

fn reachable_expr_binding_paths(
    bindings: &[Binding],
    root_exprs: &[Expr],
    _roots: &[Root],
) -> HashSet<core_ir::Path> {
    let bindings_by_path = bindings
        .iter()
        .map(|binding| (binding.name.clone(), binding))
        .collect::<HashMap<_, _>>();
    let mut reachable = HashSet::new();
    let mut stack = Vec::new();
    for expr in root_exprs {
        let mut vars = HashSet::new();
        collect_expr_vars(expr, &mut vars);
        stack.extend(vars);
    }
    while let Some(path) = stack.pop() {
        if !reachable.insert(path.clone()) {
            continue;
        }
        let Some(binding) = bindings_by_path.get(&path) else {
            continue;
        };
        let mut vars = HashSet::new();
        collect_expr_vars(&binding.body, &mut vars);
        stack.extend(vars);
    }
    reachable
}

pub(super) fn final_reachable_binding_paths(module: &Module) -> HashSet<core_ir::Path> {
    module
        .bindings
        .iter()
        .map(|binding| binding.name.clone())
        .collect()
}

pub(super) fn root_reachable_binding_paths(module: &Module) -> HashSet<core_ir::Path> {
    reachable_expr_binding_paths(&module.bindings, &module.root_exprs, &[])
}

pub(super) fn prune_unreachable_bindings(module: Module) -> Module {
    let reachable =
        reachable_expr_binding_paths(&module.bindings, &module.root_exprs, &module.roots);
    let bindings = module
        .bindings
        .into_iter()
        .filter(|binding| reachable.contains(&binding.name))
        .collect::<Vec<_>>();
    let binding_names = bindings
        .iter()
        .map(|binding| binding.name.clone())
        .collect::<HashSet<_>>();
    let roots = module
        .roots
        .into_iter()
        .filter(|root| match root {
            Root::Binding(path) => binding_names.contains(path),
            Root::Expr(_) => true,
        })
        .collect();
    Module {
        path: module.path,
        bindings,
        root_exprs: module.root_exprs,
        roots,
    }
}

pub(super) fn prune_unreachable_specializations(module: Module) -> Module {
    let reachable =
        reachable_expr_binding_paths(&module.bindings, &module.root_exprs, &module.roots);
    let bindings = module
        .bindings
        .into_iter()
        .filter(|binding| {
            !is_demand_specialization_path(&binding.name) || reachable.contains(&binding.name)
        })
        .collect::<Vec<_>>();
    Module {
        path: module.path,
        bindings,
        root_exprs: module.root_exprs,
        roots: module.roots,
    }
}

fn is_demand_specialization_path(path: &core_ir::Path) -> bool {
    path.segments
        .last()
        .and_then(|name| name.0.rsplit_once("__ddmono"))
        .is_some_and(|(_, suffix)| {
            !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
        })
}

pub(super) fn ensure_monomorphic_bindings(module: &Module) -> RuntimeResult<()> {
    for binding in &module.bindings {
        if !binding.type_params.is_empty() {
            if std::env::var_os("YULANG_DEBUG_MONO_PIPELINE").is_some() {
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
            return Err(RuntimeError::ResidualPolymorphicBinding {
                path: binding.name.clone(),
                vars: binding.type_params.clone(),
                source: crate::diagnostic::ResidualPolymorphicSource::TypeParams,
            });
        }
        let mut vars = BTreeSet::new();
        collect_expr_type_vars(&binding.body, &mut vars);
        collect_core_type_vars(&binding.scheme.body, &mut vars);
        for requirement in &binding.scheme.requirements {
            for arg in &requirement.args {
                match arg {
                    core_ir::RoleRequirementArg::Input(bounds)
                    | core_ir::RoleRequirementArg::Associated { bounds, .. } => {
                        if let Some(lower) = bounds.lower.as_deref() {
                            collect_core_type_vars(lower, &mut vars);
                        }
                        if let Some(upper) = bounds.upper.as_deref() {
                            collect_core_type_vars(upper, &mut vars);
                        }
                    }
                }
            }
        }
        if !vars.is_empty() {
            return Err(RuntimeError::ResidualPolymorphicBinding {
                path: binding.name.clone(),
                vars: vars.into_iter().collect(),
                source: crate::diagnostic::ResidualPolymorphicSource::RuntimeTypes,
            });
        }
    }
    Ok(())
}
