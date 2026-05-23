use std::collections::HashMap;

use yulang_runtime_ir::{
    Binding, Expr, ExprKind, RecordExprField, RecordSpreadExpr, Stmt, Type as RuntimeType,
};
use yulang_typed_ir as typed_ir;

use crate::planner::{FinalizedInstance, InstancePlan};
use crate::principal::InstanceKey;

pub fn emit_instance_bindings(plan: &InstancePlan) -> Vec<Binding> {
    let aliases = InstanceAliases::from_plan(plan);
    emit_instance_bindings_with_aliases(plan, &aliases)
}

pub fn emit_instance_bindings_with_aliases(
    plan: &InstancePlan,
    aliases: &InstanceAliases,
) -> Vec<Binding> {
    plan.finalized_instances
        .iter()
        .map(|instance| emit_instance_binding(instance, &aliases))
        .collect()
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstanceAliases {
    by_key: HashMap<InstanceKey, typed_ir::Path>,
    by_call: HashMap<InstanceCallKey, typed_ir::Path>,
}

impl InstanceAliases {
    pub fn from_plan(plan: &InstancePlan) -> Self {
        let mut by_key = HashMap::new();
        let mut by_call = HashMap::new();
        for (index, instance) in plan.finalized_instances.iter().enumerate() {
            let alias = alias_path(&instance.key, index);
            by_call.insert(InstanceCallKey::from_instance(&instance.key), alias.clone());
            by_key.insert(instance.key.clone(), alias);
        }
        Self { by_key, by_call }
    }

    pub fn alias_for(&self, key: &InstanceKey) -> Option<&typed_ir::Path> {
        self.by_key.get(key)
    }

    fn alias_for_call(&self, path: &typed_ir::Path, ty: &RuntimeType) -> Option<&typed_ir::Path> {
        let (params, result) = runtime_function_chain(ty)?;
        self.by_call.get(&InstanceCallKey {
            original_binding: path.clone(),
            params,
            result,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct InstanceCallKey {
    original_binding: typed_ir::Path,
    params: Vec<RuntimeType>,
    result: RuntimeType,
}

impl InstanceCallKey {
    fn from_instance(key: &InstanceKey) -> Self {
        Self {
            original_binding: key.original_binding.clone(),
            params: key.closed_param_types.clone(),
            result: key.closed_result_type.clone(),
        }
    }
}

fn emit_instance_binding(instance: &FinalizedInstance, aliases: &InstanceAliases) -> Binding {
    let alias = aliases
        .alias_for(&instance.key)
        .cloned()
        .unwrap_or_else(|| instance.key.original_binding.clone());
    let params = solution_params(&instance.body);
    let param_types = params.iter().map(|(_, ty)| ty.clone()).collect::<Vec<_>>();
    let runtime_result_type = instance.body.result_type.clone();
    let scheme_result_type = instance.key.closed_result_type.clone();
    let body = rewrite_expr_aliases(instance.body.body.clone(), aliases);
    let body = wrap_lambdas(params, body, runtime_result_type.clone());
    Binding {
        name: alias,
        type_params: Vec::new(),
        scheme: typed_ir::Scheme {
            requirements: Vec::new(),
            body: function_scheme_type_chain(
                &param_types,
                &instance.key.closed_effect,
                &scheme_result_type,
            ),
        },
        body,
    }
}

fn rewrite_expr_aliases(expr: Expr, aliases: &InstanceAliases) -> Expr {
    let ty = expr.ty;
    match expr.kind {
        ExprKind::Var(path) => {
            let path = aliases.alias_for_call(&path, &ty).cloned().unwrap_or(path);
            Expr::typed(ExprKind::Var(path), ty)
        }
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        } => Expr::typed(
            ExprKind::Apply {
                callee: Box::new(rewrite_expr_aliases(*callee, aliases)),
                arg: Box::new(rewrite_expr_aliases(*arg, aliases)),
                evidence,
                instantiation,
            },
            ty,
        ),
        ExprKind::Tuple(items) => Expr::typed(
            ExprKind::Tuple(
                items
                    .into_iter()
                    .map(|item| rewrite_expr_aliases(item, aliases))
                    .collect(),
            ),
            ty,
        ),
        ExprKind::Block { stmts, tail } => Expr::typed(
            ExprKind::Block {
                stmts: stmts
                    .into_iter()
                    .map(|stmt| rewrite_stmt_aliases(stmt, aliases))
                    .collect(),
                tail: tail.map(|tail| Box::new(rewrite_expr_aliases(*tail, aliases))),
            },
            ty,
        ),
        ExprKind::Record { fields, spread } => Expr::typed(
            ExprKind::Record {
                fields: fields
                    .into_iter()
                    .map(|field| RecordExprField {
                        name: field.name,
                        value: rewrite_expr_aliases(field.value, aliases),
                    })
                    .collect(),
                spread: spread.map(|spread| rewrite_record_spread_aliases(spread, aliases)),
            },
            ty,
        ),
        ExprKind::Variant { tag, value } => Expr::typed(
            ExprKind::Variant {
                tag,
                value: value.map(|value| Box::new(rewrite_expr_aliases(*value, aliases))),
            },
            ty,
        ),
        ExprKind::Handle {
            body,
            arms,
            evidence,
            handler,
        } => Expr::typed(
            ExprKind::Handle {
                body: Box::new(rewrite_expr_aliases(*body, aliases)),
                arms: arms
                    .into_iter()
                    .map(|arm| rewrite_handle_arm_aliases(arm, aliases))
                    .collect(),
                evidence,
                handler,
            },
            ty,
        ),
        ExprKind::BindHere { expr } => Expr::typed(
            ExprKind::BindHere {
                expr: Box::new(rewrite_expr_aliases(*expr, aliases)),
            },
            ty,
        ),
        ExprKind::Thunk {
            effect,
            value,
            expr,
        } => Expr::typed(
            ExprKind::Thunk {
                effect,
                value,
                expr: Box::new(rewrite_expr_aliases(*expr, aliases)),
            },
            ty,
        ),
        ExprKind::LocalPushId { id, body } => Expr::typed(
            ExprKind::LocalPushId {
                id,
                body: Box::new(rewrite_expr_aliases(*body, aliases)),
            },
            ty,
        ),
        ExprKind::AddId {
            id,
            allowed,
            active,
            thunk,
        } => Expr::typed(
            ExprKind::AddId {
                id,
                allowed,
                active,
                thunk: Box::new(rewrite_expr_aliases(*thunk, aliases)),
            },
            ty,
        ),
        ExprKind::Coerce { from, to, expr } => Expr::typed(
            ExprKind::Coerce {
                from,
                to,
                expr: Box::new(rewrite_expr_aliases(*expr, aliases)),
            },
            ty,
        ),
        ExprKind::Pack { var, expr } => Expr::typed(
            ExprKind::Pack {
                var,
                expr: Box::new(rewrite_expr_aliases(*expr, aliases)),
            },
            ty,
        ),
        kind => Expr::typed(kind, ty),
    }
}

fn rewrite_handle_arm_aliases(
    arm: yulang_runtime_ir::HandleArm,
    aliases: &InstanceAliases,
) -> yulang_runtime_ir::HandleArm {
    yulang_runtime_ir::HandleArm {
        effect: arm.effect,
        payload: arm.payload,
        resume: arm.resume,
        guard: arm.guard.map(|guard| rewrite_expr_aliases(guard, aliases)),
        body: rewrite_expr_aliases(arm.body, aliases),
    }
}

fn rewrite_stmt_aliases(stmt: Stmt, aliases: &InstanceAliases) -> Stmt {
    match stmt {
        Stmt::Let { pattern, value } => Stmt::Let {
            pattern,
            value: rewrite_expr_aliases(value, aliases),
        },
        Stmt::Expr(expr) => Stmt::Expr(rewrite_expr_aliases(expr, aliases)),
        Stmt::Module { def, body } => Stmt::Module {
            def,
            body: rewrite_expr_aliases(body, aliases),
        },
    }
}

fn rewrite_record_spread_aliases(
    spread: RecordSpreadExpr,
    aliases: &InstanceAliases,
) -> RecordSpreadExpr {
    match spread {
        RecordSpreadExpr::Head(expr) => {
            RecordSpreadExpr::Head(Box::new(rewrite_expr_aliases(*expr, aliases)))
        }
        RecordSpreadExpr::Tail(expr) => {
            RecordSpreadExpr::Tail(Box::new(rewrite_expr_aliases(*expr, aliases)))
        }
    }
}

fn function_scheme_type_chain(
    params: &[RuntimeType],
    effect: &typed_ir::Type,
    result: &RuntimeType,
) -> typed_ir::Type {
    let mut ret = runtime_type_core_or_unknown(result);
    for (index, param) in params.iter().enumerate().rev() {
        let ret_effect = if index + 1 == params.len() {
            effect.clone()
        } else {
            typed_ir::Type::Never
        };
        ret = typed_ir::Type::Fun {
            param: Box::new(runtime_type_core_or_unknown(param)),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(ret_effect),
            ret: Box::new(ret),
        };
    }
    ret
}

fn runtime_type_core_or_unknown(ty: &RuntimeType) -> typed_ir::Type {
    match ty {
        RuntimeType::Core(ty) => ty.clone(),
        RuntimeType::Unknown | RuntimeType::Fun { .. } | RuntimeType::Thunk { .. } => {
            typed_ir::Type::Unknown
        }
    }
}

fn solution_params(solution: &crate::BodySolution) -> Vec<(typed_ir::Name, RuntimeType)> {
    if solution.params.is_empty() {
        vec![(solution.param.clone(), solution.param_type.clone())]
    } else {
        solution.params.clone()
    }
}

fn wrap_lambdas(
    params: Vec<(typed_ir::Name, RuntimeType)>,
    body: Expr,
    result_type: RuntimeType,
) -> Expr {
    let mut expr = body;
    let mut ret_type = result_type;
    for (param, param_type) in params.into_iter().rev() {
        let lambda_type = RuntimeType::Fun {
            param: Box::new(param_type.clone()),
            ret: Box::new(ret_type),
        };
        expr = Expr::typed(
            ExprKind::Lambda {
                param,
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(expr),
            },
            lambda_type.clone(),
        );
        ret_type = lambda_type;
    }
    expr
}

fn runtime_function_chain(ty: &RuntimeType) -> Option<(Vec<RuntimeType>, RuntimeType)> {
    let mut params = Vec::new();
    let mut current = ty;
    while let RuntimeType::Fun { param, ret } = current {
        params.push((**param).clone());
        current = ret;
    }
    if params.is_empty() {
        None
    } else {
        Some((params, current.clone()))
    }
}

fn alias_path(key: &InstanceKey, index: usize) -> typed_ir::Path {
    let mut path = key.original_binding.clone();
    path.push(typed_ir::Name(format!("mono{index}")));
    path
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BodySolution, FinalizedInstance, InstancePlan, InstancePlanner};
    use yulang_runtime_ir::{Expr, ExprKind};

    #[test]
    fn emit_instance_bindings_rewrites_nested_callee_to_alias() {
        let mut planner = InstancePlanner::new([use_id_binding(), id_binding()]);
        planner
            .request_root(&path(&["use_id"]), RuntimeType::Core(int_type()))
            .unwrap();
        let plan = planner.run().unwrap();
        let emitted = emit_instance_bindings(&plan);

        assert_eq!(emitted.len(), 2);
        assert_eq!(emitted[0].name, path(&["use_id", "mono0"]));
        assert_eq!(emitted[1].name, path(&["id", "mono1"]));
        let ExprKind::Lambda { body, .. } = &emitted[0].body.kind else {
            panic!("expected emitted lambda");
        };
        let ExprKind::Apply { callee, .. } = &body.kind else {
            panic!("expected apply body");
        };
        let expected = path(&["id", "mono1"]);
        assert!(matches!(&callee.kind, ExprKind::Var(path) if path == &expected));
    }

    #[test]
    fn emit_instance_bindings_wraps_curried_instance_params() {
        let plan = InstancePlan {
            finalized_instances: vec![FinalizedInstance {
                key: InstanceKey {
                    original_binding: path(&["pair"]),
                    closed_param_types: vec![
                        RuntimeType::Core(int_type()),
                        RuntimeType::Core(bool_type()),
                    ],
                    closed_result_type: RuntimeType::Core(typed_ir::Type::Tuple(vec![
                        int_type(),
                        bool_type(),
                    ])),
                    closed_effect: typed_ir::Type::Never,
                    captured_env_shape: None,
                },
                body: BodySolution {
                    param: typed_ir::Name("x".into()),
                    param_type: RuntimeType::Core(int_type()),
                    params: vec![
                        (typed_ir::Name("x".into()), RuntimeType::Core(int_type())),
                        (typed_ir::Name("y".into()), RuntimeType::Core(bool_type())),
                    ],
                    body: Expr::typed(
                        ExprKind::Tuple(vec![
                            Expr::typed(ExprKind::Var(path(&["x"])), RuntimeType::Core(int_type())),
                            Expr::typed(
                                ExprKind::Var(path(&["y"])),
                                RuntimeType::Core(bool_type()),
                            ),
                        ]),
                        RuntimeType::Core(typed_ir::Type::Tuple(vec![int_type(), bool_type()])),
                    ),
                    result_type: RuntimeType::Core(typed_ir::Type::Tuple(vec![
                        int_type(),
                        bool_type(),
                    ])),
                    nested_instances: Vec::new(),
                },
            }],
            report: crate::FinalizeReport::default(),
        };

        let emitted = emit_instance_bindings(&plan);

        let ExprKind::Lambda { body, .. } = &emitted[0].body.kind else {
            panic!("expected first lambda");
        };
        let ExprKind::Lambda { body, .. } = &body.kind else {
            panic!("expected second lambda");
        };
        assert!(matches!(body.kind, ExprKind::Tuple(_)));
    }

    #[test]
    fn emit_instance_bindings_rewrites_nested_callee_inside_thunk() {
        let plan = InstancePlan {
            finalized_instances: vec![
                FinalizedInstance {
                    key: InstanceKey {
                        original_binding: path(&["use_id_in_thunk"]),
                        closed_param_types: vec![RuntimeType::Core(int_type())],
                        closed_result_type: RuntimeType::Core(int_type()),
                        closed_effect: io_effect(),
                        captured_env_shape: None,
                    },
                    body: BodySolution {
                        param: typed_ir::Name("x".into()),
                        param_type: RuntimeType::Core(int_type()),
                        params: vec![(typed_ir::Name("x".into()), RuntimeType::Core(int_type()))],
                        body: Expr::typed(
                            ExprKind::Thunk {
                                effect: io_effect(),
                                value: RuntimeType::Core(int_type()),
                                expr: Box::new(Expr::typed(
                                    ExprKind::Apply {
                                        callee: Box::new(Expr::typed(
                                            ExprKind::Var(path(&["id"])),
                                            RuntimeType::Fun {
                                                param: Box::new(RuntimeType::Core(int_type())),
                                                ret: Box::new(RuntimeType::Core(int_type())),
                                            },
                                        )),
                                        arg: Box::new(Expr::typed(
                                            ExprKind::Var(path(&["x"])),
                                            RuntimeType::Core(int_type()),
                                        )),
                                        evidence: None,
                                        instantiation: None,
                                    },
                                    RuntimeType::Core(int_type()),
                                )),
                            },
                            RuntimeType::Thunk {
                                effect: io_effect(),
                                value: Box::new(RuntimeType::Core(int_type())),
                            },
                        ),
                        result_type: RuntimeType::Thunk {
                            effect: io_effect(),
                            value: Box::new(RuntimeType::Core(int_type())),
                        },
                        nested_instances: Vec::new(),
                    },
                },
                FinalizedInstance {
                    key: InstanceKey {
                        original_binding: path(&["id"]),
                        closed_param_types: vec![RuntimeType::Core(int_type())],
                        closed_result_type: RuntimeType::Core(int_type()),
                        closed_effect: typed_ir::Type::Never,
                        captured_env_shape: None,
                    },
                    body: BodySolution {
                        param: typed_ir::Name("x".into()),
                        param_type: RuntimeType::Core(int_type()),
                        params: vec![(typed_ir::Name("x".into()), RuntimeType::Core(int_type()))],
                        body: Expr::typed(
                            ExprKind::Var(path(&["x"])),
                            RuntimeType::Core(int_type()),
                        ),
                        result_type: RuntimeType::Core(int_type()),
                        nested_instances: Vec::new(),
                    },
                },
            ],
            report: crate::FinalizeReport::default(),
        };
        let emitted = emit_instance_bindings(&plan);

        let ExprKind::Lambda { body, .. } = &emitted[0].body.kind else {
            panic!("expected emitted lambda");
        };
        let ExprKind::Thunk { expr, .. } = &body.kind else {
            panic!("expected thunk body");
        };
        let ExprKind::Apply { callee, .. } = &expr.kind else {
            panic!("expected nested apply");
        };
        let expected = path(&["id", "mono1"]);
        assert!(matches!(&callee.kind, ExprKind::Var(path) if path == &expected));
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

    fn io_effect() -> typed_ir::Type {
        typed_ir::Type::Row {
            items: vec![typed_ir::Type::Named {
                path: path(&["io"]),
                args: Vec::new(),
            }],
            tail: Box::new(typed_ir::Type::Never),
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
