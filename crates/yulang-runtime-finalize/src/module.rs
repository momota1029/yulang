use std::collections::HashMap;

use yulang_runtime_ir::{Module, Root, Type as RuntimeType};
use yulang_typed_ir as typed_ir;

use crate::diagnostic::{FinalizeDiagnostic, FinalizeError, FinalizeResult};
use crate::emit::{InstanceAliases, emit_instance_bindings_with_aliases};
use crate::output::{FinalizeOutput, RootInstance};
use crate::planner::InstancePlanner;

pub fn finalize_root_bindings(
    mut module: Module,
    requests: impl IntoIterator<Item = RootBindingRequest>,
) -> FinalizeResult<FinalizeOutput> {
    let mut planner = InstancePlanner::new(module.bindings.clone());
    let mut roots = Vec::new();
    for request in requests {
        let key = planner.request_root(&request.binding, request.arg_lower)?;
        roots.push((request.binding, key));
    }

    let plan = planner.run()?;
    let aliases = InstanceAliases::from_plan(&plan);
    let emitted = emit_instance_bindings_with_aliases(&plan, &aliases);
    let mut report = plan.report;
    for (original, key) in roots {
        if let Some(alias) = aliases.alias_for(&key) {
            report.root_instances.push(RootInstance {
                original,
                key,
                alias: alias.clone(),
            });
        }
    }
    rewrite_unambiguous_roots(&mut module, &report.root_instances);
    module.bindings.extend(emitted);

    Ok(FinalizeOutput { module, report })
}

pub fn finalize_simple_root_exprs(mut module: Module) -> FinalizeResult<FinalizeOutput> {
    let mut planner = InstancePlanner::new(module.bindings.clone());
    let mut roots = Vec::new();
    for (index, expr) in module.root_exprs.iter().enumerate() {
        let Some((binding, arg_lower)) = simple_root_apply(expr) else {
            continue;
        };
        let key = planner.request_root(binding, arg_lower)?;
        roots.push((index, binding.clone(), key));
    }

    let plan = planner.run()?;
    let aliases = InstanceAliases::from_plan(&plan);
    let emitted = emit_instance_bindings_with_aliases(&plan, &aliases);
    let mut report = plan.report;
    for (index, original, key) in roots {
        let Some(alias) = aliases.alias_for(&key).cloned() else {
            continue;
        };
        let Some(expr) = module.root_exprs.get_mut(index) else {
            return Err(FinalizeError::Diagnostic(
                FinalizeDiagnostic::MissingRootExpr { index },
            ));
        };
        rewrite_simple_root_apply(expr, &key, alias.clone())?;
        report.root_instances.push(RootInstance {
            original,
            key,
            alias,
        });
    }
    module.bindings.extend(emitted);

    Ok(FinalizeOutput { module, report })
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RootBindingRequest {
    pub binding: typed_ir::Path,
    pub arg_lower: RuntimeType,
}

fn rewrite_unambiguous_roots(module: &mut Module, roots: &[RootInstance]) {
    let mut aliases = HashMap::<typed_ir::Path, Option<typed_ir::Path>>::new();
    for root in roots {
        aliases
            .entry(root.original.clone())
            .and_modify(|current| {
                if current.as_ref() != Some(&root.alias) {
                    *current = None;
                }
            })
            .or_insert_with(|| Some(root.alias.clone()));
    }

    for root in &mut module.roots {
        let Root::Binding(path) = root else {
            continue;
        };
        if let Some(Some(alias)) = aliases.get(path) {
            *path = alias.clone();
        }
    }
}

fn simple_root_apply(expr: &yulang_runtime_ir::Expr) -> Option<(&typed_ir::Path, RuntimeType)> {
    let yulang_runtime_ir::ExprKind::Apply { callee, arg, .. } = &expr.kind else {
        return None;
    };
    let yulang_runtime_ir::ExprKind::Var(path) = &callee.kind else {
        return None;
    };
    if !runtime_type_is_closed_for_root(&arg.ty) {
        return None;
    }
    Some((path, arg.ty.clone()))
}

fn rewrite_simple_root_apply(
    expr: &mut yulang_runtime_ir::Expr,
    key: &crate::InstanceKey,
    alias: typed_ir::Path,
) -> FinalizeResult<()> {
    let yulang_runtime_ir::ExprKind::Apply { callee, arg, .. } = &mut expr.kind else {
        return Ok(());
    };
    callee.kind = yulang_runtime_ir::ExprKind::Var(alias);
    callee.ty = RuntimeType::Fun {
        param: Box::new(arg.ty.clone()),
        ret: Box::new(key.closed_result_type.clone()),
    };
    expr.ty = key.closed_result_type.clone();
    Ok(())
}

fn runtime_type_is_closed_for_root(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Unknown => false,
        RuntimeType::Core(ty) => core_type_is_closed_for_root(ty),
        RuntimeType::Fun { param, ret } => {
            runtime_type_is_closed_for_root(param) && runtime_type_is_closed_for_root(ret)
        }
        RuntimeType::Thunk { effect, value } => {
            core_type_is_closed_for_root(effect) && runtime_type_is_closed_for_root(value)
        }
    }
}

fn core_type_is_closed_for_root(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Unknown | typed_ir::Type::Var(_) => false,
        typed_ir::Type::Never | typed_ir::Type::Any => true,
        typed_ir::Type::Named { args, .. } => args.iter().all(type_arg_is_closed_for_root),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            core_type_is_closed_for_root(param)
                && core_type_is_closed_for_root(param_effect)
                && core_type_is_closed_for_root(ret_effect)
                && core_type_is_closed_for_root(ret)
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => items.iter().all(core_type_is_closed_for_root),
        typed_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .all(|field| core_type_is_closed_for_root(&field.value))
                && record.spread.as_ref().is_none_or(|spread| match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        core_type_is_closed_for_root(ty)
                    }
                })
        }
        typed_ir::Type::Variant(variant) => {
            variant
                .cases
                .iter()
                .all(|case| case.payloads.iter().all(core_type_is_closed_for_root))
                && variant
                    .tail
                    .as_ref()
                    .is_none_or(|tail| core_type_is_closed_for_root(tail))
        }
        typed_ir::Type::Row { items, tail } => {
            items.iter().all(core_type_is_closed_for_root) && core_type_is_closed_for_root(tail)
        }
        typed_ir::Type::Recursive { body, .. } => core_type_is_closed_for_root(body),
    }
}

fn type_arg_is_closed_for_root(arg: &typed_ir::TypeArg) -> bool {
    match arg {
        typed_ir::TypeArg::Type(ty) => core_type_is_closed_for_root(ty),
        typed_ir::TypeArg::Bounds(bounds) => {
            bounds
                .lower
                .as_ref()
                .is_none_or(|ty| core_type_is_closed_for_root(ty))
                && bounds
                    .upper
                    .as_ref()
                    .is_none_or(|ty| core_type_is_closed_for_root(ty))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use yulang_runtime_ir::{Binding, Expr, ExprKind, Root};

    #[test]
    fn finalize_root_bindings_appends_emitted_bindings_and_reports_alias() {
        let module = Module {
            path: path(&["test"]),
            bindings: vec![use_id_binding(), id_binding()],
            root_exprs: Vec::new(),
            roots: vec![Root::Binding(path(&["use_id"]))],
            role_impls: Vec::new(),
        };

        let output = finalize_root_bindings(
            module,
            [RootBindingRequest {
                binding: path(&["use_id"]),
                arg_lower: RuntimeType::Core(int_type()),
            }],
        )
        .unwrap();

        assert_eq!(output.module.bindings.len(), 4);
        assert_eq!(output.module.bindings[2].name, path(&["use_id", "mono0"]));
        assert_eq!(output.module.bindings[3].name, path(&["id", "mono1"]));
        assert_eq!(output.report.root_instances.len(), 1);
        assert_eq!(
            output.report.root_instances[0].alias,
            path(&["use_id", "mono0"])
        );
        assert_eq!(
            output.module.roots,
            vec![Root::Binding(path(&["use_id", "mono0"]))]
        );
    }

    #[test]
    fn finalize_root_bindings_keeps_ambiguous_root_binding_unrewritten() {
        let module = Module {
            path: path(&["test"]),
            bindings: vec![id_binding()],
            root_exprs: Vec::new(),
            roots: vec![Root::Binding(path(&["id"]))],
            role_impls: Vec::new(),
        };

        let output = finalize_root_bindings(
            module,
            [
                RootBindingRequest {
                    binding: path(&["id"]),
                    arg_lower: RuntimeType::Core(int_type()),
                },
                RootBindingRequest {
                    binding: path(&["id"]),
                    arg_lower: RuntimeType::Core(bool_type()),
                },
            ],
        )
        .unwrap();

        assert_eq!(output.report.root_instances.len(), 2);
        assert_eq!(output.module.roots, vec![Root::Binding(path(&["id"]))]);
    }

    #[test]
    fn finalize_simple_root_exprs_emits_and_rewrites_closed_apply_root() {
        let module = Module {
            path: path(&["test"]),
            bindings: vec![id_binding()],
            root_exprs: vec![Expr::typed(
                ExprKind::Apply {
                    callee: Box::new(Expr::typed(
                        ExprKind::Var(path(&["id"])),
                        RuntimeType::Unknown,
                    )),
                    arg: Box::new(Expr::typed(
                        ExprKind::Lit(typed_ir::Lit::Int("1".into())),
                        RuntimeType::Core(int_type()),
                    )),
                    evidence: None,
                    instantiation: None,
                },
                RuntimeType::Unknown,
            )],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        };

        let output = finalize_simple_root_exprs(module).unwrap();

        assert_eq!(output.module.bindings.len(), 2);
        assert_eq!(output.module.bindings[1].name, path(&["id", "mono0"]));
        assert_eq!(
            output.module.root_exprs[0].ty,
            RuntimeType::Core(int_type())
        );
        let ExprKind::Apply { callee, .. } = &output.module.root_exprs[0].kind else {
            panic!("expected root apply");
        };
        let expected = path(&["id", "mono0"]);
        assert!(matches!(&callee.kind, ExprKind::Var(path) if path == &expected));
        assert_eq!(
            output.report.root_instances[0].alias,
            path(&["id", "mono0"])
        );
    }

    fn id_binding() -> Binding {
        Binding {
            name: path(&["id"]),
            type_params: vec![typed_ir::TypeVar("a".into())],
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: function_type(
                    typed_ir::Type::Var(typed_ir::TypeVar("a".into())),
                    typed_ir::Type::Var(typed_ir::TypeVar("a".into())),
                ),
            },
            body: Expr::typed(
                ExprKind::Lambda {
                    param: typed_ir::Name("x".into()),
                    param_effect_annotation: None,
                    param_function_allowed_effects: None,
                    body: Box::new(Expr::typed(
                        ExprKind::Var(path(&["x"])),
                        RuntimeType::Core(typed_ir::Type::Var(typed_ir::TypeVar("a".into()))),
                    )),
                },
                RuntimeType::Unknown,
            ),
        }
    }

    fn use_id_binding() -> Binding {
        Binding {
            name: path(&["use_id"]),
            type_params: vec![typed_ir::TypeVar("a".into())],
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: function_type(
                    typed_ir::Type::Var(typed_ir::TypeVar("a".into())),
                    typed_ir::Type::Var(typed_ir::TypeVar("a".into())),
                ),
            },
            body: Expr::typed(
                ExprKind::Lambda {
                    param: typed_ir::Name("x".into()),
                    param_effect_annotation: None,
                    param_function_allowed_effects: None,
                    body: Box::new(Expr::typed(
                        ExprKind::Apply {
                            callee: Box::new(Expr::typed(
                                ExprKind::Var(path(&["id"])),
                                RuntimeType::Unknown,
                            )),
                            arg: Box::new(Expr::typed(
                                ExprKind::Var(path(&["x"])),
                                RuntimeType::Core(typed_ir::Type::Var(typed_ir::TypeVar(
                                    "a".into(),
                                ))),
                            )),
                            evidence: None,
                            instantiation: None,
                        },
                        RuntimeType::Unknown,
                    )),
                },
                RuntimeType::Unknown,
            ),
        }
    }

    fn function_type(param: typed_ir::Type, ret: typed_ir::Type) -> typed_ir::Type {
        typed_ir::Type::Fun {
            param: Box::new(param),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(typed_ir::Type::Never),
            ret: Box::new(ret),
        }
    }

    fn int_type() -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path(&["std", "int", "Int"]),
            args: Vec::new(),
        }
    }

    fn bool_type() -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path(&["std", "bool", "Bool"]),
            args: Vec::new(),
        }
    }

    fn path(segments: &[&str]) -> typed_ir::Path {
        typed_ir::Path::new(
            segments
                .iter()
                .map(|segment| typed_ir::Name((*segment).into()))
                .collect(),
        )
    }
}
