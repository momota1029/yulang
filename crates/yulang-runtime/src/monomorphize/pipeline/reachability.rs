use super::*;

fn reachable_expr_binding_paths(
    bindings: &[Binding],
    root_exprs: &[Expr],
    roots: &[Root],
) -> HashSet<typed_ir::Path> {
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
    for root in roots {
        match root {
            Root::Binding(path) => stack.push(path.clone()),
            Root::Expr(index) => {
                if let Some(expr) = root_exprs.get(*index) {
                    let mut vars = HashSet::new();
                    collect_expr_vars(expr, &mut vars);
                    stack.extend(vars);
                }
            }
        }
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

pub(super) fn final_reachable_binding_paths(module: &Module) -> HashSet<typed_ir::Path> {
    module
        .bindings
        .iter()
        .map(|binding| binding.name.clone())
        .collect()
}

pub(super) fn root_reachable_binding_paths(module: &Module) -> HashSet<typed_ir::Path> {
    reachable_expr_binding_paths(&module.bindings, &module.root_exprs, &module.roots)
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
        role_impls: module.role_impls,
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
        role_impls: module.role_impls,
    }
}

fn is_demand_specialization_path(path: &typed_ir::Path) -> bool {
    path.segments
        .last()
        .and_then(|name| name.0.rsplit_once("__ddmono"))
        .is_some_and(|(_, suffix)| {
            !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
        })
}
