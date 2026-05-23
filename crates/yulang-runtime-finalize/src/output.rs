use yulang_runtime_ir::{Module, Type as RuntimeType};
use yulang_typed_ir as typed_ir;

use crate::body::BodySolution;
use crate::diagnostic::{FinalizeDiagnostic, FinalizeResult};
use crate::principal::InstanceKey;

pub fn finalize_module(module: Module) -> FinalizeResult<FinalizeOutput> {
    Ok(FinalizeOutput {
        module,
        report: FinalizeReport::default(),
    })
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FinalizeOutput {
    pub module: Module,
    pub report: FinalizeReport,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FinalizeReport {
    pub planned_instances: Vec<InstanceKey>,
    pub root_instances: Vec<RootInstance>,
    pub diagnostics: Vec<FinalizeDiagnostic>,
}

impl FinalizeReport {
    pub fn record_body_solution(&mut self, solution: &BodySolution) {
        for instance in &solution.nested_instances {
            self.push_planned_instance(instance.key.clone());
        }
    }

    pub fn push_planned_instance(&mut self, key: InstanceKey) {
        if !self.planned_instances.contains(&key) {
            self.planned_instances.push(key);
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RootInstance {
    pub original: typed_ir::Path,
    pub key: InstanceKey,
    pub alias: typed_ir::Path,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TopLevelDemand {
    pub root: TopLevelRoot,
    pub expected_value: RuntimeType,
    pub expected_effect: typed_ir::Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TopLevelRoot {
    Expr(usize),
    Named(typed_ir::Path),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::body::NestedInstancePlan;
    use crate::principal::PrincipalSolution;

    #[test]
    fn report_records_body_solution_instances_once() {
        let key = instance_key("id");
        let solution = BodySolution {
            param: typed_ir::Name("x".into()),
            param_type: RuntimeType::Core(typed_ir::Type::Tuple(Vec::new())),
            body: yulang_runtime_ir::Expr::typed(
                yulang_runtime_ir::ExprKind::Tuple(Vec::new()),
                RuntimeType::Core(typed_ir::Type::Tuple(Vec::new())),
            ),
            result_type: RuntimeType::Core(typed_ir::Type::Tuple(Vec::new())),
            nested_instances: vec![
                NestedInstancePlan {
                    key: key.clone(),
                    principal: PrincipalSolution {
                        key: key.clone(),
                        substitutions: Vec::new(),
                    },
                    result_type: RuntimeType::Core(typed_ir::Type::Tuple(Vec::new())),
                },
                NestedInstancePlan {
                    key: key.clone(),
                    principal: PrincipalSolution {
                        key: key.clone(),
                        substitutions: Vec::new(),
                    },
                    result_type: RuntimeType::Core(typed_ir::Type::Tuple(Vec::new())),
                },
            ],
        };

        let mut report = FinalizeReport::default();
        report.record_body_solution(&solution);

        assert_eq!(report.planned_instances, vec![key]);
    }

    fn instance_key(name: &str) -> InstanceKey {
        InstanceKey {
            original_binding: typed_ir::Path::from_name(typed_ir::Name(name.into())),
            closed_param_types: vec![RuntimeType::Core(typed_ir::Type::Tuple(Vec::new()))],
            closed_result_type: RuntimeType::Core(typed_ir::Type::Tuple(Vec::new())),
            closed_effect: typed_ir::Type::Never,
            captured_env_shape: None,
        }
    }
}
