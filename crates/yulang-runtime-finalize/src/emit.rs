use std::collections::HashMap;

use yulang_runtime_ir::{
    Binding, Expr, ExprKind, RecordExprField, RecordSpreadExpr, Stmt, Type as RuntimeType,
};
use yulang_typed_ir as typed_ir;

use crate::planner::{FinalizedInstance, InstancePlan};
use crate::principal::InstanceKey;

pub fn emit_instance_bindings(plan: &InstancePlan) -> Vec<Binding> {
    let aliases = InstanceAliases::from_plan(plan);
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
        let RuntimeType::Fun { param, ret } = ty else {
            return None;
        };
        self.by_call.get(&InstanceCallKey {
            original_binding: path.clone(),
            param: (**param).clone(),
            result: (**ret).clone(),
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct InstanceCallKey {
    original_binding: typed_ir::Path,
    param: RuntimeType,
    result: RuntimeType,
}

impl InstanceCallKey {
    fn from_instance(key: &InstanceKey) -> Self {
        Self {
            original_binding: key.original_binding.clone(),
            param: key
                .closed_param_types
                .first()
                .cloned()
                .unwrap_or(RuntimeType::Unknown),
            result: key.closed_result_type.clone(),
        }
    }
}

fn emit_instance_binding(instance: &FinalizedInstance, aliases: &InstanceAliases) -> Binding {
    let alias = aliases
        .alias_for(&instance.key)
        .cloned()
        .unwrap_or_else(|| instance.key.original_binding.clone());
    let param_type = instance.body.param_type.clone();
    let result_type = instance.body.result_type.clone();
    let body = rewrite_expr_aliases(instance.body.body.clone(), aliases);
    Binding {
        name: alias,
        type_params: Vec::new(),
        scheme: typed_ir::Scheme {
            requirements: Vec::new(),
            body: function_scheme_type(&param_type, &instance.key.closed_effect, &result_type),
        },
        body: Expr::typed(
            ExprKind::Lambda {
                param: instance.body.param.clone(),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(body),
            },
            RuntimeType::Fun {
                param: Box::new(param_type),
                ret: Box::new(result_type),
            },
        ),
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
        kind => Expr::typed(kind, ty),
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

fn function_scheme_type(
    param: &RuntimeType,
    effect: &typed_ir::Type,
    result: &RuntimeType,
) -> typed_ir::Type {
    typed_ir::Type::Fun {
        param: Box::new(runtime_type_core_or_unknown(param)),
        param_effect: Box::new(typed_ir::Type::Never),
        ret_effect: Box::new(effect.clone()),
        ret: Box::new(runtime_type_core_or_unknown(result)),
    }
}

fn runtime_type_core_or_unknown(ty: &RuntimeType) -> typed_ir::Type {
    match ty {
        RuntimeType::Core(ty) => ty.clone(),
        RuntimeType::Unknown | RuntimeType::Fun { .. } | RuntimeType::Thunk { .. } => {
            typed_ir::Type::Unknown
        }
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
    use crate::InstancePlanner;
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

    fn path(segments: &[&str]) -> typed_ir::Path {
        typed_ir::Path::new(
            segments
                .iter()
                .map(|segment| typed_ir::Name((*segment).into()))
                .collect(),
        )
    }
}
