use super::*;

fn reachable_expr_binding_paths(
    bindings: &[Binding],
    root_exprs: &[Expr],
    roots: &[Root],
    role_impls: &[typed_ir::RoleImplGraphNode],
) -> HashSet<typed_ir::Path> {
    reachable_expr_binding_paths_with_role_members(bindings, root_exprs, roots, role_impls, true)
}

fn directly_reachable_expr_binding_paths(module: &Module) -> HashSet<typed_ir::Path> {
    reachable_expr_binding_paths_with_role_members(
        &module.bindings,
        &module.root_exprs,
        &module.roots,
        &module.role_impls,
        false,
    )
}

fn reachable_expr_binding_paths_with_role_members(
    bindings: &[Binding],
    root_exprs: &[Expr],
    roots: &[Root],
    role_impls: &[typed_ir::RoleImplGraphNode],
    include_role_members: bool,
) -> HashSet<typed_ir::Path> {
    let bindings_by_path = bindings
        .iter()
        .map(|binding| (binding.name.clone(), binding))
        .collect::<HashMap<_, _>>();
    let role_members_by_method = role_member_paths_by_method(role_impls);
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
        if include_role_members
            && is_role_method_path(&path)
            && let Some(method) = path.segments.last()
            && let Some(members) = role_members_by_method.get(method)
        {
            stack.extend(members.iter().cloned());
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
    reachable_expr_binding_paths(
        &module.bindings,
        &module.root_exprs,
        &module.roots,
        &module.role_impls,
    )
}

pub(super) fn prune_unreachable_bindings(module: Module) -> Module {
    let mut reachable = reachable_expr_binding_paths(
        &module.bindings,
        &module.root_exprs,
        &module.roots,
        &module.role_impls,
    );
    retain_reachable_specializations_for_original_refs(&module.bindings, &mut reachable);
    retain_originals_for_reachable_specializations(&module.bindings, &mut reachable);
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
    let mut reachable = reachable_expr_binding_paths(
        &module.bindings,
        &module.root_exprs,
        &module.roots,
        &module.role_impls,
    );
    retain_reachable_specializations_for_original_refs(&module.bindings, &mut reachable);
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

pub(super) fn remove_specialized_generic_original_bindings(module: Module) -> Module {
    let specialized_originals = module
        .bindings
        .iter()
        .filter_map(|binding| unspecialized_path(&binding.name))
        .collect::<HashSet<_>>();
    let bindings = module
        .bindings
        .into_iter()
        .filter(|binding| {
            binding.type_params.is_empty() || !specialized_originals.contains(&binding.name)
        })
        .collect::<Vec<_>>();
    Module { bindings, ..module }
}

pub(super) fn remove_runtime_unreferenced_generic_bindings(module: Module) -> Module {
    let directly_reachable = directly_reachable_expr_binding_paths(&module);
    let bindings = module
        .bindings
        .into_iter()
        .filter(|binding| {
            binding.type_params.is_empty() || directly_reachable.contains(&binding.name)
        })
        .collect::<Vec<_>>();
    Module { bindings, ..module }
}

fn role_member_paths_by_method(
    role_impls: &[typed_ir::RoleImplGraphNode],
) -> HashMap<typed_ir::Name, Vec<typed_ir::Path>> {
    let mut out = HashMap::<typed_ir::Name, Vec<typed_ir::Path>>::new();
    for role_impl in role_impls {
        for member in &role_impl.members {
            out.entry(member.name.clone())
                .or_default()
                .push(member.value.clone());
        }
    }
    out
}

fn retain_reachable_specializations_for_original_refs(
    bindings: &[Binding],
    reachable: &mut HashSet<typed_ir::Path>,
) {
    let mut by_original = HashMap::<typed_ir::Path, Vec<typed_ir::Path>>::new();
    for binding in bindings {
        let Some(original) = unspecialized_path(&binding.name) else {
            continue;
        };
        by_original
            .entry(original)
            .or_default()
            .push(binding.name.clone());
    }
    let originals = reachable.iter().cloned().collect::<Vec<_>>();
    for original in originals {
        let Some(specializations) = by_original.get(&original) else {
            continue;
        };
        reachable.extend(specializations.iter().cloned());
    }
}

fn retain_originals_for_reachable_specializations(
    bindings: &[Binding],
    reachable: &mut HashSet<typed_ir::Path>,
) {
    let originals = bindings
        .iter()
        .filter_map(|binding| unspecialized_path(&binding.name))
        .collect::<Vec<_>>();
    reachable.extend(originals);
}

fn is_demand_specialization_path(path: &typed_ir::Path) -> bool {
    path.segments
        .last()
        .and_then(|name| name.0.rsplit_once("__ddmono"))
        .is_some_and(|(_, suffix)| {
            !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn runtime_unreferenced_generic_bindings_are_removed_after_dispatch() {
        let role_method = path(&["std", "Debug", "debug"]);
        let impl_member = path(&["std", "prelude", "&impl#tuple2", "debug"]);
        let main = path(&["main"]);
        let module = Module {
            path: path(&["test"]),
            bindings: vec![
                binding(
                    main.clone(),
                    Vec::new(),
                    Expr::typed(
                        ExprKind::Lit(typed_ir::Lit::Unit),
                        RuntimeType::core(unit_type()),
                    ),
                ),
                binding(
                    impl_member.clone(),
                    vec![typed_ir::TypeVar("a".to_string())],
                    Expr::typed(
                        ExprKind::Lit(typed_ir::Lit::Unit),
                        RuntimeType::core(unit_type()),
                    ),
                ),
            ],
            root_exprs: Vec::new(),
            roots: vec![Root::Binding(main)],
            role_impls: vec![typed_ir::RoleImplGraphNode {
                role: path(&["std", "Debug"]),
                inputs: Vec::new(),
                associated_types: Vec::new(),
                members: vec![typed_ir::RecordField {
                    name: typed_ir::Name("debug".to_string()),
                    value: impl_member.clone(),
                    optional: false,
                }],
            }],
        };

        let pruned = remove_runtime_unreferenced_generic_bindings(module);

        assert!(
            pruned
                .bindings
                .iter()
                .all(|binding| binding.name != impl_member)
        );
        assert!(
            !directly_reachable_expr_binding_paths(&pruned).contains(&role_method),
            "test fixture should not keep dispatch metadata alive through expressions",
        );
    }

    #[test]
    fn runtime_directly_referenced_generic_bindings_are_kept_for_audit() {
        let generic = path(&["generic"]);
        let module = Module {
            path: path(&["test"]),
            bindings: vec![binding(
                generic.clone(),
                vec![typed_ir::TypeVar("a".to_string())],
                Expr::typed(
                    ExprKind::Lit(typed_ir::Lit::Unit),
                    RuntimeType::core(unit_type()),
                ),
            )],
            root_exprs: Vec::new(),
            roots: vec![Root::Binding(generic.clone())],
            role_impls: Vec::new(),
        };

        let pruned = remove_runtime_unreferenced_generic_bindings(module);

        assert!(
            pruned
                .bindings
                .iter()
                .any(|binding| binding.name == generic)
        );
    }

    fn binding(name: typed_ir::Path, type_params: Vec<typed_ir::TypeVar>, body: Expr) -> Binding {
        Binding {
            name,
            type_params,
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: unit_type(),
            },
            body,
        }
    }

    fn unit_type() -> typed_ir::Type {
        typed_ir::Type::Tuple(Vec::new())
    }

    fn path(segments: &[&str]) -> typed_ir::Path {
        typed_ir::Path {
            segments: segments
                .iter()
                .map(|segment| typed_ir::Name((*segment).to_string()))
                .collect(),
        }
    }
}
