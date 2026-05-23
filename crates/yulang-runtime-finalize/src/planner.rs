use std::collections::{HashMap, VecDeque};

use yulang_runtime_ir::{Binding, Type as RuntimeType};
use yulang_typed_ir as typed_ir;

use crate::body::{BodyGraph, BodySolution};
use crate::diagnostic::{FinalizeDiagnostic, FinalizeError, FinalizeResult};
use crate::output::FinalizeReport;
use crate::principal::{InstanceKey, PrincipalGraph, PrincipalSolution};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstancePlanner {
    bindings: HashMap<typed_ir::Path, Binding>,
    states: HashMap<InstanceKey, InstanceState>,
    queue: VecDeque<PrincipalSolution>,
    finalized: Vec<FinalizedInstance>,
    report: FinalizeReport,
}

impl InstancePlanner {
    pub fn new(bindings: impl IntoIterator<Item = Binding>) -> Self {
        Self {
            bindings: bindings
                .into_iter()
                .map(|binding| (binding.name.clone(), binding))
                .collect(),
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
        let principal = PrincipalGraph::from_binding(&binding)?.solve_call(arg_lower)?;
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

    fn path(segments: &[&str]) -> typed_ir::Path {
        typed_ir::Path::new(
            segments
                .iter()
                .map(|segment| typed_ir::Name((*segment).into()))
                .collect(),
        )
    }
}
