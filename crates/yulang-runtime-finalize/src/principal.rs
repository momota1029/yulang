use yulang_runtime_ir::{Binding, Type as RuntimeType};
use yulang_typed_ir as typed_ir;

use crate::diagnostic::{
    FinalizeDiagnostic, FinalizeError, FinalizeResult, PrincipalIncompleteReason,
};
use crate::types::{
    LowerSubstitutions, materialize_core_type, materialize_runtime_type, runtime_type_is_closed,
    unify_runtime_with_core,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InstanceKey {
    pub original_binding: typed_ir::Path,
    pub closed_param_types: Vec<RuntimeType>,
    pub closed_result_type: RuntimeType,
    pub closed_effect: typed_ir::Type,
    pub captured_env_shape: Option<RuntimeType>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrincipalGraph {
    original_binding: typed_ir::Path,
    param: typed_ir::Type,
    param_effect: typed_ir::Type,
    ret_effect: typed_ir::Type,
    ret: typed_ir::Type,
}

impl PrincipalGraph {
    pub fn from_binding(binding: &Binding) -> FinalizeResult<Self> {
        match &binding.scheme.body {
            typed_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            } => Ok(Self {
                original_binding: binding.name.clone(),
                param: (**param).clone(),
                param_effect: (**param_effect).clone(),
                ret_effect: (**ret_effect).clone(),
                ret: (**ret).clone(),
            }),
            body => Err(FinalizeError::Diagnostic(
                FinalizeDiagnostic::PrincipalTypeIsNotCallable {
                    binding: binding.name.clone(),
                    actual: body.clone(),
                },
            )),
        }
    }

    pub fn solve_call(&self, arg_lower: RuntimeType) -> FinalizeResult<PrincipalSolution> {
        let mut substitutions = LowerSubstitutions::default();
        unify_runtime_with_core(&mut substitutions, &self.param, &arg_lower)?;
        let closed_param =
            materialize_runtime_type(RuntimeType::Core(self.param.clone()), &substitutions);
        if !runtime_type_is_closed(&closed_param) {
            return Err(FinalizeError::Diagnostic(
                FinalizeDiagnostic::IncompletePrincipalInstance {
                    binding: self.original_binding.clone(),
                    reason: PrincipalIncompleteReason::OpenParameter,
                },
            ));
        }

        let closed_result =
            materialize_runtime_type(RuntimeType::Core(self.ret.clone()), &substitutions);
        if !runtime_type_is_closed(&closed_result) {
            return Err(FinalizeError::Diagnostic(
                FinalizeDiagnostic::IncompletePrincipalInstance {
                    binding: self.original_binding.clone(),
                    reason: PrincipalIncompleteReason::OpenResult,
                },
            ));
        }

        let closed_effect = materialize_core_type(self.ret_effect.clone(), &substitutions);
        if !crate::types::runtime_type_is_closed(&RuntimeType::Core(closed_effect.clone())) {
            return Err(FinalizeError::Diagnostic(
                FinalizeDiagnostic::IncompletePrincipalInstance {
                    binding: self.original_binding.clone(),
                    reason: PrincipalIncompleteReason::OpenEffect,
                },
            ));
        }

        let key = InstanceKey {
            original_binding: self.original_binding.clone(),
            closed_param_types: vec![closed_param],
            closed_result_type: closed_result,
            closed_effect,
            captured_env_shape: None,
        };

        Ok(PrincipalSolution {
            key,
            substitutions: substitutions.into_vec(),
        })
    }

    pub fn param_effect(&self) -> &typed_ir::Type {
        &self.param_effect
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrincipalSolution {
    pub key: InstanceKey,
    pub substitutions: Vec<typed_ir::TypeSubstitution>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use yulang_runtime_ir::{Expr, ExprKind};

    #[test]
    fn principal_graph_makes_closed_instance_key_from_argument_lower() {
        let binding = id_binding();
        let graph = PrincipalGraph::from_binding(&binding).unwrap();

        let solution = graph.solve_call(RuntimeType::Core(int_type())).unwrap();

        assert_eq!(
            solution.key,
            InstanceKey {
                original_binding: path(&["id"]),
                closed_param_types: vec![RuntimeType::Core(int_type())],
                closed_result_type: RuntimeType::Core(int_type()),
                closed_effect: typed_ir::Type::Never,
                captured_env_shape: None,
            }
        );
        assert_eq!(
            solution.substitutions,
            vec![typed_ir::TypeSubstitution {
                var: typed_ir::TypeVar("a".into()),
                ty: int_type(),
            }]
        );
    }

    #[test]
    fn principal_graph_keeps_call_site_lowers_separate() {
        let binding = id_binding();
        let graph = PrincipalGraph::from_binding(&binding).unwrap();

        let int_solution = graph.solve_call(RuntimeType::Core(int_type())).unwrap();
        let bool_solution = graph.solve_call(RuntimeType::Core(bool_type())).unwrap();

        assert_ne!(int_solution.key, bool_solution.key);
        assert_eq!(
            int_solution.key.closed_param_types,
            vec![RuntimeType::Core(int_type())]
        );
        assert_eq!(
            bool_solution.key.closed_param_types,
            vec![RuntimeType::Core(bool_type())]
        );
    }

    #[test]
    fn principal_graph_rejects_open_result() {
        let binding = const_open_binding();
        let graph = PrincipalGraph::from_binding(&binding).unwrap();

        let err = graph.solve_call(RuntimeType::Core(int_type())).unwrap_err();

        assert_eq!(
            err,
            FinalizeError::Diagnostic(FinalizeDiagnostic::IncompletePrincipalInstance {
                binding: path(&["open"]),
                reason: PrincipalIncompleteReason::OpenResult,
            })
        );
    }

    fn id_binding() -> Binding {
        Binding {
            name: path(&["id"]),
            type_params: vec![typed_ir::TypeVar("a".into())],
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: typed_ir::Type::Fun {
                    param: Box::new(typed_ir::Type::Var(typed_ir::TypeVar("a".into()))),
                    param_effect: Box::new(typed_ir::Type::Never),
                    ret_effect: Box::new(typed_ir::Type::Never),
                    ret: Box::new(typed_ir::Type::Var(typed_ir::TypeVar("a".into()))),
                },
            },
            body: Expr::typed(ExprKind::Tuple(Vec::new()), RuntimeType::Unknown),
        }
    }

    fn const_open_binding() -> Binding {
        Binding {
            name: path(&["open"]),
            type_params: vec![typed_ir::TypeVar("a".into()), typed_ir::TypeVar("b".into())],
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: typed_ir::Type::Fun {
                    param: Box::new(typed_ir::Type::Var(typed_ir::TypeVar("a".into()))),
                    param_effect: Box::new(typed_ir::Type::Never),
                    ret_effect: Box::new(typed_ir::Type::Never),
                    ret: Box::new(typed_ir::Type::Var(typed_ir::TypeVar("b".into()))),
                },
            },
            body: Expr::typed(ExprKind::Tuple(Vec::new()), RuntimeType::Unknown),
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
