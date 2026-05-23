use std::collections::{HashMap, VecDeque};

use yulang_runtime_ir::{Binding, Type as RuntimeType};
use yulang_typed_ir as typed_ir;

use crate::body::{BodyGraph, BodySolution};
use crate::diagnostic::{FinalizeDiagnostic, FinalizeError, FinalizeResult};
use crate::output::FinalizeReport;
use crate::principal::{InstanceKey, PrincipalGraph, PrincipalSolution};
use crate::role::RoleContext;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstancePlanner {
    bindings: HashMap<typed_ir::Path, Binding>,
    roles: RoleContext,
    states: HashMap<InstanceKey, InstanceState>,
    queue: VecDeque<PrincipalSolution>,
    finalized: Vec<FinalizedInstance>,
    report: FinalizeReport,
}

impl InstancePlanner {
    pub fn new(bindings: impl IntoIterator<Item = Binding>) -> Self {
        Self::new_with_roles(bindings, std::iter::empty::<typed_ir::RoleImplGraphNode>())
    }

    pub fn new_with_roles(
        bindings: impl IntoIterator<Item = Binding>,
        role_impls: impl IntoIterator<Item = typed_ir::RoleImplGraphNode>,
    ) -> Self {
        Self {
            bindings: bindings
                .into_iter()
                .map(|binding| (binding.name.clone(), binding))
                .collect(),
            roles: RoleContext::new(role_impls),
            states: HashMap::new(),
            queue: VecDeque::new(),
            finalized: Vec::new(),
            report: FinalizeReport::default(),
        }
    }

    pub fn request_root(
        &mut self,
        binding: &typed_ir::Path,
        arg_lower: RuntimeType,
    ) -> FinalizeResult<InstanceKey> {
        let binding = self.binding(binding)?.clone();
        let principal = PrincipalGraph::from_binding(&binding)?
            .solve_call_with_roles(arg_lower, Some(&self.roles))?;
        let key = principal.key.clone();
        self.enqueue(principal);
        Ok(key)
    }

    pub fn run(mut self) -> FinalizeResult<InstancePlan> {
        while let Some(principal) = self.queue.pop_front() {
            if matches!(
                self.states.get(&principal.key),
                Some(InstanceState::Finalizing | InstanceState::Finalized)
            ) {
                continue;
            }
            self.states
                .insert(principal.key.clone(), InstanceState::Finalizing);
            let binding = self.binding(&principal.key.original_binding)?.clone();
            let solution = BodyGraph::from_binding_instance(&binding, &principal)?
                .with_known_bindings(self.bindings.values().cloned())
                .with_roles(self.roles.clone())
                .solve()?;
            for nested in &solution.nested_instances {
                self.enqueue(nested.principal.clone());
            }
            self.report.record_body_solution(&solution);
            self.finalized.push(FinalizedInstance {
                key: principal.key.clone(),
                body: solution,
            });
            self.states
                .insert(principal.key.clone(), InstanceState::Finalized);
        }

        Ok(InstancePlan {
            finalized_instances: self.finalized,
            report: self.report,
        })
    }

    fn enqueue(&mut self, principal: PrincipalSolution) {
        if self.states.contains_key(&principal.key) {
            return;
        }
        self.states
            .insert(principal.key.clone(), InstanceState::Reserved);
        self.queue.push_back(principal);
    }

    fn binding(&self, path: &typed_ir::Path) -> FinalizeResult<&Binding> {
        self.bindings.get(path).ok_or_else(|| {
            FinalizeError::Diagnostic(FinalizeDiagnostic::MissingBinding {
                binding: path.clone(),
            })
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InstanceState {
    Reserved,
    Finalizing,
    Finalized,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstancePlan {
    pub finalized_instances: Vec<FinalizedInstance>,
    pub report: FinalizeReport,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FinalizedInstance {
    pub key: InstanceKey,
    pub body: BodySolution,
}

#[cfg(test)]
mod tests {
    use super::*;
    use yulang_runtime_ir::{Expr, ExprKind};

    #[test]
    fn planner_processes_root_and_nested_instances_once() {
        let mut planner = InstancePlanner::new([use_id_twice_binding(), id_binding()]);
        let root_key = planner
            .request_root(&path(&["use_id_twice"]), RuntimeType::Core(int_type()))
            .unwrap();
        let plan = planner.run().unwrap();

        assert_eq!(root_key.original_binding, path(&["use_id_twice"]));
        assert_eq!(plan.finalized_instances.len(), 2);
        assert_eq!(
            plan.finalized_instances
                .iter()
                .map(|instance| instance.key.original_binding.clone())
                .collect::<Vec<_>>(),
            vec![path(&["use_id_twice"]), path(&["id"])]
        );
        assert_eq!(plan.report.planned_instances, vec![id_key()]);
    }

    #[test]
    fn planner_deduplicates_repeated_root_requests() {
        let mut planner = InstancePlanner::new([id_binding()]);
        let first = planner
            .request_root(&path(&["id"]), RuntimeType::Core(int_type()))
            .unwrap();
        let second = planner
            .request_root(&path(&["id"]), RuntimeType::Core(int_type()))
            .unwrap();
        let plan = planner.run().unwrap();

        assert_eq!(first, second);
        assert_eq!(plan.finalized_instances.len(), 1);
    }

    #[test]
    fn planner_passes_role_context_to_nested_principal_calls() {
        let mut planner = InstancePlanner::new_with_roles(
            [use_index_binding(), index_value_binding()],
            [index_lines_bool_impl()],
        );

        let root = planner
            .request_root(
                &path(&["use_index"]),
                RuntimeType::Core(lines_type(typed_ir::Type::Never)),
            )
            .unwrap();
        let plan = planner.run().unwrap();

        assert_eq!(root.closed_result_type, RuntimeType::Core(bool_type()));
        assert_eq!(plan.finalized_instances.len(), 2);
        assert_eq!(
            plan.finalized_instances
                .iter()
                .map(|instance| instance.key.original_binding.clone())
                .collect::<Vec<_>>(),
            vec![path(&["use_index"]), path(&["index_value"])]
        );
        assert_eq!(
            plan.finalized_instances[1].key.closed_result_type,
            RuntimeType::Core(bool_type())
        );
    }

    #[test]
    fn planner_resolves_role_method_callee_to_impl_member() {
        let mut planner = InstancePlanner::new_with_roles(
            [use_role_get_binding(), index_lines_get_binding()],
            [index_lines_bool_impl()],
        );

        let root = planner
            .request_root(
                &path(&["use_role_get"]),
                RuntimeType::Core(lines_type(typed_ir::Type::Never)),
            )
            .unwrap();
        let plan = planner.run().unwrap();

        assert_eq!(root.closed_result_type, RuntimeType::Core(bool_type()));
        assert_eq!(
            plan.finalized_instances
                .iter()
                .map(|instance| instance.key.original_binding.clone())
                .collect::<Vec<_>>(),
            vec![
                path(&["use_role_get"]),
                path(&["std", "index", "&impl#lines", "get"])
            ]
        );
    }

    fn id_key() -> InstanceKey {
        InstanceKey {
            original_binding: path(&["id"]),
            closed_param_types: vec![RuntimeType::Core(int_type())],
            closed_result_type: RuntimeType::Core(int_type()),
            closed_effect: typed_ir::Type::Never,
            captured_env_shape: None,
        }
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

    fn index_value_binding() -> Binding {
        Binding {
            name: path(&["index_value"]),
            type_params: vec![
                typed_ir::TypeVar("input".into()),
                typed_ir::TypeVar("value".into()),
            ],
            scheme: typed_ir::Scheme {
                requirements: vec![typed_ir::RoleRequirement {
                    role: path(&["std", "index", "Index"]),
                    args: vec![
                        typed_ir::RoleRequirementArg::Input(typed_ir::TypeBounds::lower(
                            typed_ir::Type::Var(typed_ir::TypeVar("input".into())),
                        )),
                        typed_ir::RoleRequirementArg::Associated {
                            name: typed_ir::Name("value".into()),
                            bounds: typed_ir::TypeBounds::lower(typed_ir::Type::Var(
                                typed_ir::TypeVar("value".into()),
                            )),
                        },
                    ],
                }],
                body: function_type(
                    typed_ir::Type::Var(typed_ir::TypeVar("input".into())),
                    typed_ir::Type::Var(typed_ir::TypeVar("value".into())),
                ),
            },
            body: Expr::typed(
                ExprKind::Lambda {
                    param: typed_ir::Name("_input".into()),
                    param_effect_annotation: None,
                    param_function_allowed_effects: None,
                    body: Box::new(Expr::typed(
                        ExprKind::Lit(typed_ir::Lit::Bool(true)),
                        RuntimeType::Core(typed_ir::Type::Var(typed_ir::TypeVar("value".into()))),
                    )),
                },
                RuntimeType::Unknown,
            ),
        }
    }

    fn use_index_binding() -> Binding {
        Binding {
            name: path(&["use_index"]),
            type_params: vec![typed_ir::TypeVar("input".into())],
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: function_type(
                    typed_ir::Type::Var(typed_ir::TypeVar("input".into())),
                    bool_type(),
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
                                ExprKind::Var(path(&["index_value"])),
                                RuntimeType::Unknown,
                            )),
                            arg: Box::new(Expr::typed(
                                ExprKind::Var(path(&["x"])),
                                RuntimeType::Core(typed_ir::Type::Var(typed_ir::TypeVar(
                                    "input".into(),
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

    fn use_role_get_binding() -> Binding {
        Binding {
            name: path(&["use_role_get"]),
            type_params: vec![typed_ir::TypeVar("input".into())],
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: function_type(
                    typed_ir::Type::Var(typed_ir::TypeVar("input".into())),
                    bool_type(),
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
                                ExprKind::Var(path(&["std", "index", "Index", "get"])),
                                RuntimeType::Unknown,
                            )),
                            arg: Box::new(Expr::typed(
                                ExprKind::Var(path(&["x"])),
                                RuntimeType::Core(typed_ir::Type::Var(typed_ir::TypeVar(
                                    "input".into(),
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

    fn index_lines_get_binding() -> Binding {
        Binding {
            name: path(&["std", "index", "&impl#lines", "get"]),
            type_params: Vec::new(),
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: function_type(lines_type(typed_ir::Type::Never), bool_type()),
            },
            body: Expr::typed(
                ExprKind::Lambda {
                    param: typed_ir::Name("_lines".into()),
                    param_effect_annotation: None,
                    param_function_allowed_effects: None,
                    body: Box::new(Expr::typed(
                        ExprKind::Lit(typed_ir::Lit::Bool(true)),
                        RuntimeType::Core(bool_type()),
                    )),
                },
                RuntimeType::Unknown,
            ),
        }
    }

    fn index_lines_bool_impl() -> typed_ir::RoleImplGraphNode {
        typed_ir::RoleImplGraphNode {
            role: path(&["std", "index", "Index"]),
            inputs: vec![typed_ir::TypeBounds::lower(lines_type(
                typed_ir::Type::Var(typed_ir::TypeVar("e".into())),
            ))],
            associated_types: vec![typed_ir::RecordField {
                name: typed_ir::Name("value".into()),
                value: typed_ir::TypeBounds::lower(bool_type()),
                optional: false,
            }],
            members: vec![typed_ir::RecordField {
                name: typed_ir::Name("get".into()),
                value: path(&["std", "index", "&impl#lines", "get"]),
                optional: false,
            }],
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

    fn bool_type() -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path(&["std", "bool", "Bool"]),
            args: Vec::new(),
        }
    }

    fn lines_type(effect: typed_ir::Type) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path(&["std", "string", "Lines"]),
            args: vec![typed_ir::TypeArg::Type(effect)],
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
