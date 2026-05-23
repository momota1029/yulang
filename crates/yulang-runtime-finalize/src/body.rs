use std::collections::{BTreeMap, HashMap, HashSet};

use yulang_runtime_ir::{Binding, Expr, ExprKind, Stmt, Type as RuntimeType};
use yulang_typed_ir as typed_ir;

use crate::diagnostic::{BodyIncompleteReason, FinalizeDiagnostic, FinalizeError, FinalizeResult};
use crate::principal::{InstanceKey, PrincipalGraph, PrincipalSolution};
use crate::role::{RoleContext, RoleProjectionStatus, role_method_parts};
use crate::types::{
    LowerSubstitutions, materialize_expr_type, path_as_local_name, runtime_type_is_closed,
    runtime_types_match,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BodyGraph {
    binding: typed_ir::Path,
    param: typed_ir::Name,
    body: Expr,
    expected_result: RuntimeType,
    substitutions: LowerSubstitutions,
    initial_env: BTreeMap<typed_ir::Name, RuntimeType>,
    known_bindings: HashMap<typed_ir::Path, Binding>,
    roles: Option<RoleContext>,
}

impl BodyGraph {
    pub fn from_binding_instance(
        binding: &Binding,
        principal: &PrincipalSolution,
    ) -> FinalizeResult<Self> {
        let key = &principal.key;
        if binding.name != key.original_binding {
            return Err(FinalizeError::Diagnostic(
                FinalizeDiagnostic::UnsupportedBodyShape {
                    binding: binding.name.clone(),
                    reason: BodyIncompleteReason::UnsupportedExpression,
                },
            ));
        }
        let Some(param_type) = key.closed_param_types.first().cloned() else {
            return Err(FinalizeError::Diagnostic(
                FinalizeDiagnostic::UnsupportedBodyShape {
                    binding: binding.name.clone(),
                    reason: BodyIncompleteReason::MissingInstanceParameter,
                },
            ));
        };
        let ExprKind::Lambda { param, body, .. } = &binding.body.kind else {
            return Err(FinalizeError::Diagnostic(
                FinalizeDiagnostic::UnsupportedBodyShape {
                    binding: binding.name.clone(),
                    reason: BodyIncompleteReason::NonLambdaBinding,
                },
            ));
        };

        let substitutions = LowerSubstitutions::from_type_substitutions(&principal.substitutions)?;
        let mut initial_env = BTreeMap::new();
        initial_env.insert(param.clone(), param_type);

        Ok(Self {
            binding: binding.name.clone(),
            param: param.clone(),
            body: (**body).clone(),
            expected_result: key.closed_result_type.clone(),
            substitutions,
            initial_env,
            known_bindings: HashMap::new(),
            roles: None,
        })
    }

    pub fn with_known_bindings(mut self, bindings: impl IntoIterator<Item = Binding>) -> Self {
        self.known_bindings = bindings
            .into_iter()
            .map(|binding| (binding.name.clone(), binding))
            .collect();
        self
    }

    pub fn with_roles(mut self, roles: RoleContext) -> Self {
        self.roles = Some(roles);
        self
    }

    pub fn solve(&self) -> FinalizeResult<BodySolution> {
        let mut env = self.initial_env.clone();
        let mut nested_instances = Vec::new();
        let solved_body = self.solve_expr(&mut env, &mut nested_instances, self.body.clone())?;
        if !runtime_types_match(&self.expected_result, &solved_body.ty) {
            return Err(FinalizeError::Diagnostic(
                FinalizeDiagnostic::BodyResultMismatch {
                    binding: self.binding.clone(),
                    expected: self.expected_result.clone(),
                    actual: solved_body.ty,
                },
            ));
        }

        Ok(BodySolution {
            param: self.param.clone(),
            param_type: self
                .initial_env
                .get(&self.param)
                .cloned()
                .unwrap_or(RuntimeType::Unknown),
            body: solved_body,
            result_type: self.expected_result.clone(),
            nested_instances: dedupe_nested_instances(nested_instances),
        })
    }

    fn solve_expr(
        &self,
        env: &mut BTreeMap<typed_ir::Name, RuntimeType>,
        nested_instances: &mut Vec<NestedInstancePlan>,
        expr: Expr,
    ) -> FinalizeResult<Expr> {
        let materialized_ty = materialize_expr_type(expr.ty, &self.substitutions);
        match expr.kind {
            ExprKind::Var(path) => {
                let inferred = path_as_local_name(&path)
                    .and_then(|name| env.get(name))
                    .cloned();
                let ty = self.choose_expr_type(materialized_ty, inferred, &path)?;
                Ok(Expr::typed(ExprKind::Var(path), ty))
            }
            ExprKind::Lit(lit) => {
                let ty = self.require_closed_expr_type(materialized_ty)?;
                Ok(Expr::typed(ExprKind::Lit(lit), ty))
            }
            ExprKind::Tuple(items) => {
                let solved_items = items
                    .into_iter()
                    .map(|item| self.solve_expr(env, nested_instances, item))
                    .collect::<FinalizeResult<Vec<_>>>()?;
                let inferred = RuntimeType::Core(typed_ir::Type::Tuple(
                    solved_items
                        .iter()
                        .map(|item| match &item.ty {
                            RuntimeType::Core(ty) => ty.clone(),
                            RuntimeType::Unknown
                            | RuntimeType::Fun { .. }
                            | RuntimeType::Thunk { .. } => typed_ir::Type::Unknown,
                        })
                        .collect(),
                ));
                let ty = self.choose_known_type(materialized_ty, Some(inferred))?;
                Ok(Expr::typed(ExprKind::Tuple(solved_items), ty))
            }
            ExprKind::Block { stmts, tail } => {
                let mut block_env = env.clone();
                let mut solved_stmts = Vec::with_capacity(stmts.len());
                for stmt in stmts {
                    solved_stmts.push(self.solve_stmt(&mut block_env, nested_instances, stmt)?);
                }
                let solved_tail = tail
                    .map(|tail| self.solve_expr(&mut block_env, nested_instances, *tail))
                    .transpose()?;
                let inferred = solved_tail
                    .as_ref()
                    .map(|tail| tail.ty.clone())
                    .unwrap_or_else(|| RuntimeType::Core(typed_ir::Type::Tuple(Vec::new())));
                let ty = self.choose_known_type(materialized_ty, Some(inferred))?;
                Ok(Expr::typed(
                    ExprKind::Block {
                        stmts: solved_stmts,
                        tail: solved_tail.map(Box::new),
                    },
                    ty,
                ))
            }
            ExprKind::Apply {
                callee,
                arg,
                evidence,
                instantiation,
            } => {
                let solved_arg = self.solve_expr(env, nested_instances, *arg)?;
                if let Some(path) = callee_var_path(&callee) {
                    if let Some((target_path, binding)) =
                        self.resolve_runtime_callee_binding(path, &solved_arg)?
                    {
                        let nested = self.solve_nested_polymorphic_call(binding, &solved_arg)?;
                        let ty = self.choose_known_type(
                            materialized_ty,
                            Some(nested.key.closed_result_type.clone()),
                        )?;
                        let callee_ty = RuntimeType::Fun {
                            param: Box::new(solved_arg.ty.clone()),
                            ret: Box::new(ty.clone()),
                        };
                        let solved_callee = Expr::typed(ExprKind::Var(target_path), callee_ty);
                        nested_instances.push(nested);
                        return Ok(Expr::typed(
                            ExprKind::Apply {
                                callee: Box::new(solved_callee),
                                arg: Box::new(solved_arg),
                                evidence,
                                instantiation,
                            },
                            ty,
                        ));
                    }
                }
                Err(FinalizeError::Diagnostic(
                    FinalizeDiagnostic::UnsupportedBodyShape {
                        binding: self.binding.clone(),
                        reason: BodyIncompleteReason::UnsupportedExpression,
                    },
                ))
            }
            _ => Err(FinalizeError::Diagnostic(
                FinalizeDiagnostic::UnsupportedBodyShape {
                    binding: self.binding.clone(),
                    reason: BodyIncompleteReason::UnsupportedExpression,
                },
            )),
        }
    }

    fn solve_stmt(
        &self,
        env: &mut BTreeMap<typed_ir::Name, RuntimeType>,
        nested_instances: &mut Vec<NestedInstancePlan>,
        stmt: Stmt,
    ) -> FinalizeResult<Stmt> {
        match stmt {
            Stmt::Let { pattern, value } => {
                let solved_value = self.solve_expr(env, nested_instances, value)?;
                self.bind_pattern(env, &pattern, solved_value.ty.clone())?;
                Ok(Stmt::Let {
                    pattern,
                    value: solved_value,
                })
            }
            Stmt::Expr(expr) => Ok(Stmt::Expr(self.solve_expr(env, nested_instances, expr)?)),
            Stmt::Module { def, body } => Ok(Stmt::Module {
                def,
                body: self.solve_expr(env, nested_instances, body)?,
            }),
        }
    }

    fn resolve_runtime_callee_binding(
        &self,
        path: &typed_ir::Path,
        arg: &Expr,
    ) -> FinalizeResult<Option<(typed_ir::Path, &Binding)>> {
        if let Some(binding) = self.known_bindings.get(path) {
            return Ok(Some((path.clone(), binding)));
        }
        let Some(roles) = self.roles.as_ref() else {
            return Ok(None);
        };
        let Some((role, member_name)) = role_method_parts(path) else {
            return Ok(None);
        };
        let Some(input_lower) = runtime_core_type(&arg.ty) else {
            return Ok(None);
        };
        let resolution = roles.resolve_member(&role, &[input_lower], &member_name)?;
        if resolution.status != RoleProjectionStatus::Resolved {
            return Ok(None);
        }
        let Some(binding_path) = resolution.binding else {
            return Ok(None);
        };
        let Some(binding) = self.known_bindings.get(&binding_path) else {
            return Ok(None);
        };
        Ok(Some((binding_path, binding)))
    }

    fn solve_nested_polymorphic_call(
        &self,
        binding: &Binding,
        arg: &Expr,
    ) -> FinalizeResult<NestedInstancePlan> {
        if binding.name == self.binding {
            return Err(FinalizeError::Diagnostic(
                FinalizeDiagnostic::UnsupportedBodyShape {
                    binding: self.binding.clone(),
                    reason: BodyIncompleteReason::UnsupportedExpression,
                },
            ));
        }
        let principal = PrincipalGraph::from_binding(binding)?
            .solve_call_with_roles(arg.ty.clone(), self.roles.as_ref())?;
        let result_type = principal.key.closed_result_type.clone();
        Ok(NestedInstancePlan {
            key: principal.key.clone(),
            principal,
            result_type,
        })
    }

    fn bind_pattern(
        &self,
        env: &mut BTreeMap<typed_ir::Name, RuntimeType>,
        pattern: &yulang_runtime_ir::Pattern,
        value_ty: RuntimeType,
    ) -> FinalizeResult<()> {
        match pattern {
            yulang_runtime_ir::Pattern::Bind { name, ty } => {
                let ty = self.choose_known_type(
                    materialize_expr_type(ty.clone(), &self.substitutions),
                    Some(value_ty),
                )?;
                env.insert(name.clone(), ty);
                Ok(())
            }
            yulang_runtime_ir::Pattern::Wildcard { .. } => Ok(()),
            _ => Err(FinalizeError::Diagnostic(
                FinalizeDiagnostic::UnsupportedBodyShape {
                    binding: self.binding.clone(),
                    reason: BodyIncompleteReason::UnsupportedExpression,
                },
            )),
        }
    }

    fn choose_expr_type(
        &self,
        annotated: RuntimeType,
        inferred: Option<RuntimeType>,
        path: &typed_ir::Path,
    ) -> FinalizeResult<RuntimeType> {
        match inferred {
            Some(inferred) => self.choose_known_type(annotated, Some(inferred)),
            None => {
                if runtime_type_is_closed(&annotated) {
                    Ok(annotated)
                } else {
                    Err(FinalizeError::Diagnostic(
                        FinalizeDiagnostic::UnboundLocal { name: path.clone() },
                    ))
                }
            }
        }
    }

    fn choose_known_type(
        &self,
        annotated: RuntimeType,
        inferred: Option<RuntimeType>,
    ) -> FinalizeResult<RuntimeType> {
        match (runtime_type_is_closed(&annotated), inferred) {
            (true, Some(inferred)) if runtime_types_match(&annotated, &inferred) => Ok(annotated),
            (true, Some(inferred)) => Err(FinalizeError::Diagnostic(
                FinalizeDiagnostic::BodyResultMismatch {
                    binding: self.binding.clone(),
                    expected: annotated,
                    actual: inferred,
                },
            )),
            (true, None) => Ok(annotated),
            (false, Some(inferred)) if runtime_type_is_closed(&inferred) => Ok(inferred),
            _ => Err(FinalizeError::Diagnostic(
                FinalizeDiagnostic::UnsupportedBodyShape {
                    binding: self.binding.clone(),
                    reason: BodyIncompleteReason::OpenExpressionType,
                },
            )),
        }
    }

    fn require_closed_expr_type(&self, ty: RuntimeType) -> FinalizeResult<RuntimeType> {
        if runtime_type_is_closed(&ty) {
            Ok(ty)
        } else {
            Err(FinalizeError::Diagnostic(
                FinalizeDiagnostic::UnsupportedBodyShape {
                    binding: self.binding.clone(),
                    reason: BodyIncompleteReason::OpenExpressionType,
                },
            ))
        }
    }
}

fn runtime_core_type(ty: &RuntimeType) -> Option<typed_ir::Type> {
    match ty {
        RuntimeType::Core(ty) => Some(ty.clone()),
        RuntimeType::Unknown | RuntimeType::Fun { .. } | RuntimeType::Thunk { .. } => None,
    }
}

fn callee_var_path(expr: &Expr) -> Option<&typed_ir::Path> {
    match &expr.kind {
        ExprKind::Var(path) => Some(path),
        ExprKind::BindHere { expr }
        | ExprKind::Coerce { expr, .. }
        | ExprKind::Pack { expr, .. } => callee_var_path(expr),
        _ => None,
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BodySolution {
    pub param: typed_ir::Name,
    pub param_type: RuntimeType,
    pub body: Expr,
    pub result_type: RuntimeType,
    pub nested_instances: Vec<NestedInstancePlan>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NestedInstancePlan {
    pub key: InstanceKey,
    pub principal: PrincipalSolution,
    pub result_type: RuntimeType,
}

fn dedupe_nested_instances(instances: Vec<NestedInstancePlan>) -> Vec<NestedInstancePlan> {
    let mut seen = HashSet::new();
    let mut deduped = Vec::new();
    for instance in instances {
        if seen.insert(instance.key.clone()) {
            deduped.push(instance);
        }
    }
    deduped
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{InstanceKey, PrincipalSolution};
    use yulang_runtime_ir::{Expr, ExprKind};

    #[test]
    fn body_graph_materializes_identity_body_from_instance_lower() {
        let principal = PrincipalSolution {
            key: InstanceKey {
                original_binding: path(&["id"]),
                closed_param_types: vec![RuntimeType::Core(int_type())],
                closed_result_type: RuntimeType::Core(int_type()),
                closed_effect: typed_ir::Type::Never,
                captured_env_shape: None,
            },
            substitutions: vec![typed_ir::TypeSubstitution {
                var: typed_ir::TypeVar("a".into()),
                ty: int_type(),
            }],
        };

        let graph = BodyGraph::from_binding_instance(&id_binding(), &principal).unwrap();
        let solution = graph.solve().unwrap();

        assert_eq!(solution.result_type, RuntimeType::Core(int_type()));
        assert_eq!(solution.body.ty, RuntimeType::Core(int_type()));
    }

    #[test]
    fn body_graph_uses_local_let_lower() {
        let principal = PrincipalSolution {
            key: InstanceKey {
                original_binding: path(&["let_id"]),
                closed_param_types: vec![RuntimeType::Core(int_type())],
                closed_result_type: RuntimeType::Core(int_type()),
                closed_effect: typed_ir::Type::Never,
                captured_env_shape: None,
            },
            substitutions: vec![typed_ir::TypeSubstitution {
                var: typed_ir::TypeVar("a".into()),
                ty: int_type(),
            }],
        };

        let graph = BodyGraph::from_binding_instance(&let_id_binding(), &principal).unwrap();
        let solution = graph.solve().unwrap();

        assert_eq!(solution.body.ty, RuntimeType::Core(int_type()));
    }

    #[test]
    fn body_graph_records_nested_polymorphic_call_instance() {
        let principal = PrincipalSolution {
            key: InstanceKey {
                original_binding: path(&["use_id"]),
                closed_param_types: vec![RuntimeType::Core(int_type())],
                closed_result_type: RuntimeType::Core(int_type()),
                closed_effect: typed_ir::Type::Never,
                captured_env_shape: None,
            },
            substitutions: vec![typed_ir::TypeSubstitution {
                var: typed_ir::TypeVar("a".into()),
                ty: int_type(),
            }],
        };

        let graph = BodyGraph::from_binding_instance(&use_id_binding(), &principal)
            .unwrap()
            .with_known_bindings([id_binding()]);
        let solution = graph.solve().unwrap();

        assert_eq!(solution.body.ty, RuntimeType::Core(int_type()));
        assert_eq!(solution.nested_instances.len(), 1);
        assert_eq!(
            solution.nested_instances[0].key,
            InstanceKey {
                original_binding: path(&["id"]),
                closed_param_types: vec![RuntimeType::Core(int_type())],
                closed_result_type: RuntimeType::Core(int_type()),
                closed_effect: typed_ir::Type::Never,
                captured_env_shape: None,
            }
        );
    }

    #[test]
    fn body_graph_deduplicates_repeated_nested_instances() {
        let principal = PrincipalSolution {
            key: InstanceKey {
                original_binding: path(&["use_id_twice"]),
                closed_param_types: vec![RuntimeType::Core(int_type())],
                closed_result_type: RuntimeType::Core(typed_ir::Type::Tuple(vec![
                    int_type(),
                    int_type(),
                ])),
                closed_effect: typed_ir::Type::Never,
                captured_env_shape: None,
            },
            substitutions: vec![typed_ir::TypeSubstitution {
                var: typed_ir::TypeVar("a".into()),
                ty: int_type(),
            }],
        };

        let graph = BodyGraph::from_binding_instance(&use_id_twice_binding(), &principal)
            .unwrap()
            .with_known_bindings([id_binding()]);
        let solution = graph.solve().unwrap();

        assert_eq!(
            solution.body.ty,
            RuntimeType::Core(typed_ir::Type::Tuple(vec![int_type(), int_type()]))
        );
        assert_eq!(solution.nested_instances.len(), 1);
        assert_eq!(
            solution.nested_instances[0].key.original_binding,
            path(&["id"])
        );
    }

    #[test]
    fn body_graph_accepts_wrapped_polymorphic_callee() {
        let principal = PrincipalSolution {
            key: InstanceKey {
                original_binding: path(&["use_wrapped_id"]),
                closed_param_types: vec![RuntimeType::Core(int_type())],
                closed_result_type: RuntimeType::Core(int_type()),
                closed_effect: typed_ir::Type::Never,
                captured_env_shape: None,
            },
            substitutions: vec![typed_ir::TypeSubstitution {
                var: typed_ir::TypeVar("a".into()),
                ty: int_type(),
            }],
        };

        let graph = BodyGraph::from_binding_instance(&use_wrapped_id_binding(), &principal)
            .unwrap()
            .with_known_bindings([id_binding()]);
        let solution = graph.solve().unwrap();

        assert_eq!(solution.body.ty, RuntimeType::Core(int_type()));
        assert_eq!(solution.nested_instances.len(), 1);
        assert_eq!(
            solution.nested_instances[0].key.original_binding,
            path(&["id"])
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

    fn let_id_binding() -> Binding {
        Binding {
            name: path(&["let_id"]),
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
                        ExprKind::Block {
                            stmts: vec![Stmt::Let {
                                pattern: yulang_runtime_ir::Pattern::Bind {
                                    name: typed_ir::Name("y".into()),
                                    ty: RuntimeType::Unknown,
                                },
                                value: Expr::typed(
                                    ExprKind::Var(path(&["x"])),
                                    RuntimeType::Core(typed_ir::Type::Var(typed_ir::TypeVar(
                                        "a".into(),
                                    ))),
                                ),
                            }],
                            tail: Some(Box::new(Expr::typed(
                                ExprKind::Var(path(&["y"])),
                                RuntimeType::Unknown,
                            ))),
                        },
                        RuntimeType::Unknown,
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

    fn use_id_twice_binding() -> Binding {
        Binding {
            name: path(&["use_id_twice"]),
            type_params: vec![typed_ir::TypeVar("a".into())],
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: function_type(
                    typed_ir::Type::Var(typed_ir::TypeVar("a".into())),
                    typed_ir::Type::Tuple(vec![
                        typed_ir::Type::Var(typed_ir::TypeVar("a".into())),
                        typed_ir::Type::Var(typed_ir::TypeVar("a".into())),
                    ]),
                ),
            },
            body: Expr::typed(
                ExprKind::Lambda {
                    param: typed_ir::Name("x".into()),
                    param_effect_annotation: None,
                    param_function_allowed_effects: None,
                    body: Box::new(Expr::typed(
                        ExprKind::Tuple(vec![id_call_expr(), id_call_expr()]),
                        RuntimeType::Unknown,
                    )),
                },
                RuntimeType::Unknown,
            ),
        }
    }

    fn use_wrapped_id_binding() -> Binding {
        Binding {
            name: path(&["use_wrapped_id"]),
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
                                ExprKind::BindHere {
                                    expr: Box::new(Expr::typed(
                                        ExprKind::Var(path(&["id"])),
                                        RuntimeType::Unknown,
                                    )),
                                },
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

    fn id_call_expr() -> Expr {
        Expr::typed(
            ExprKind::Apply {
                callee: Box::new(Expr::typed(
                    ExprKind::Var(path(&["id"])),
                    RuntimeType::Unknown,
                )),
                arg: Box::new(Expr::typed(
                    ExprKind::Var(path(&["x"])),
                    RuntimeType::Core(typed_ir::Type::Var(typed_ir::TypeVar("a".into()))),
                )),
                evidence: None,
                instantiation: None,
            },
            RuntimeType::Unknown,
        )
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
