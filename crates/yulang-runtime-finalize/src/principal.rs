use yulang_runtime_ir::{Binding, Type as RuntimeType};
use yulang_typed_ir as typed_ir;

use crate::diagnostic::{
    FinalizeDiagnostic, FinalizeError, FinalizeResult, PrincipalIncompleteReason,
};
use crate::effect::EffectLane;
use crate::role::{RoleContext, RoleProjectionStatus};
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
    requirements: Vec<typed_ir::RoleRequirement>,
    params: Vec<typed_ir::Type>,
    param_effects: Vec<typed_ir::Type>,
    ret_effects: Vec<typed_ir::Type>,
    ret: typed_ir::Type,
}

impl PrincipalGraph {
    pub fn from_binding(binding: &Binding) -> FinalizeResult<Self> {
        let mut params = Vec::new();
        let mut param_effects = Vec::new();
        let mut ret_effects = Vec::new();
        let mut current = &binding.scheme.body;
        while let typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } = current
        {
            params.push((**param).clone());
            param_effects.push((**param_effect).clone());
            ret_effects.push((**ret_effect).clone());
            current = ret;
        }
        if params.is_empty() {
            return Err(FinalizeError::Diagnostic(
                FinalizeDiagnostic::PrincipalTypeIsNotCallable {
                    binding: binding.name.clone(),
                    actual: binding.scheme.body.clone(),
                },
            ));
        }
        Ok(Self {
            original_binding: binding.name.clone(),
            requirements: binding.scheme.requirements.clone(),
            params,
            param_effects,
            ret_effects,
            ret: current.clone(),
        })
    }

    pub fn solve_call(&self, arg_lower: RuntimeType) -> FinalizeResult<PrincipalSolution> {
        self.solve_call_with_roles(arg_lower, None)
    }

    pub fn solve_call_with_roles(
        &self,
        arg_lower: RuntimeType,
        roles: Option<&RoleContext>,
    ) -> FinalizeResult<PrincipalSolution> {
        self.solve_call_args_with_roles(vec![arg_lower], roles)
    }

    pub fn solve_call_args_with_roles(
        &self,
        arg_lowers: Vec<RuntimeType>,
        roles: Option<&RoleContext>,
    ) -> FinalizeResult<PrincipalSolution> {
        let mut substitutions = LowerSubstitutions::default();
        if arg_lowers.is_empty() || arg_lowers.len() > self.params.len() {
            return Err(FinalizeError::Diagnostic(
                FinalizeDiagnostic::PrincipalTypeIsNotCallable {
                    binding: self.original_binding.clone(),
                    actual: self.principal_type(),
                },
            ));
        }
        for (param, arg_lower) in self.params.iter().zip(&arg_lowers) {
            unify_runtime_with_core(&mut substitutions, param, arg_lower)?;
        }
        if let Some(roles) = roles {
            solve_role_associated_lowers(&mut substitutions, roles, &self.requirements)?;
        }
        let mut closed_params = Vec::with_capacity(arg_lowers.len());
        for param in self.params.iter().take(arg_lowers.len()) {
            let closed_param =
                materialize_runtime_type(RuntimeType::Core(param.clone()), &substitutions);
            if !runtime_type_is_closed(&closed_param) {
                return Err(FinalizeError::Diagnostic(
                    FinalizeDiagnostic::IncompletePrincipalInstance {
                        binding: self.original_binding.clone(),
                        reason: PrincipalIncompleteReason::OpenParameter,
                    },
                ));
            }
            closed_params.push(closed_param);
        }

        let result = self.result_after_args(arg_lowers.len());
        let closed_result = materialize_runtime_type(RuntimeType::Core(result), &substitutions);
        if !runtime_type_is_closed(&closed_result) {
            return Err(FinalizeError::Diagnostic(
                FinalizeDiagnostic::IncompletePrincipalInstance {
                    binding: self.original_binding.clone(),
                    reason: PrincipalIncompleteReason::OpenResult,
                },
            ));
        }

        let effect_lane =
            EffectLane::from_return_effect(self.ret_effects[arg_lowers.len() - 1].clone());
        let effect = effect_lane.solve(&substitutions);
        if !effect.is_closed {
            return Err(FinalizeError::Diagnostic(
                FinalizeDiagnostic::IncompletePrincipalInstance {
                    binding: self.original_binding.clone(),
                    reason: PrincipalIncompleteReason::OpenEffect,
                },
            ));
        }

        let key = InstanceKey {
            original_binding: self.original_binding.clone(),
            closed_param_types: closed_params,
            closed_result_type: closed_result,
            closed_effect: effect.closed_effect,
            captured_env_shape: None,
        };

        Ok(PrincipalSolution {
            key,
            substitutions: substitutions.into_vec(),
        })
    }

    pub fn param_effect(&self) -> &typed_ir::Type {
        &self.param_effects[0]
    }

    fn result_after_args(&self, arg_count: usize) -> typed_ir::Type {
        let mut result = self.ret.clone();
        for index in (arg_count..self.params.len()).rev() {
            result = typed_ir::Type::Fun {
                param: Box::new(self.params[index].clone()),
                param_effect: Box::new(self.param_effects[index].clone()),
                ret_effect: Box::new(self.ret_effects[index].clone()),
                ret: Box::new(result),
            };
        }
        result
    }

    fn principal_type(&self) -> typed_ir::Type {
        let mut result = self.ret.clone();
        for index in (0..self.params.len()).rev() {
            result = typed_ir::Type::Fun {
                param: Box::new(self.params[index].clone()),
                param_effect: Box::new(self.param_effects[index].clone()),
                ret_effect: Box::new(self.ret_effects[index].clone()),
                ret: Box::new(result),
            };
        }
        result
    }
}

fn solve_role_associated_lowers(
    substitutions: &mut LowerSubstitutions,
    roles: &RoleContext,
    requirements: &[typed_ir::RoleRequirement],
) -> FinalizeResult<()> {
    for requirement in requirements {
        let input_lowers = role_input_lowers(substitutions, requirement);
        if input_lowers.is_empty() {
            continue;
        }
        for arg in &requirement.args {
            let typed_ir::RoleRequirementArg::Associated { name, bounds } = arg else {
                continue;
            };
            let Some(target_var) = associated_lower_target_var(bounds) else {
                continue;
            };
            let projection = roles.project_associated(&requirement.role, &input_lowers, name)?;
            if projection.status == RoleProjectionStatus::Resolved {
                if let Some(ty) = projection.ty {
                    substitutions.insert(target_var.clone(), ty)?;
                }
            }
        }
    }
    Ok(())
}

fn role_input_lowers(
    substitutions: &LowerSubstitutions,
    requirement: &typed_ir::RoleRequirement,
) -> Vec<typed_ir::Type> {
    requirement
        .args
        .iter()
        .filter_map(|arg| {
            let typed_ir::RoleRequirementArg::Input(bounds) = arg else {
                return None;
            };
            bounds
                .lower
                .as_ref()
                .map(|lower| materialize_core_type((**lower).clone(), substitutions))
        })
        .filter(|ty| !type_has_open_vars(ty))
        .collect()
}

fn associated_lower_target_var(bounds: &typed_ir::TypeBounds) -> Option<&typed_ir::TypeVar> {
    match bounds.lower.as_deref() {
        Some(typed_ir::Type::Var(var)) => Some(var),
        _ => None,
    }
}

fn type_has_open_vars(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Unknown | typed_ir::Type::Var(_) => true,
        typed_ir::Type::Never | typed_ir::Type::Any => false,
        typed_ir::Type::Named { args, .. } => args.iter().any(type_arg_has_open_vars),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            type_has_open_vars(param)
                || type_has_open_vars(param_effect)
                || type_has_open_vars(ret_effect)
                || type_has_open_vars(ret)
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => items.iter().any(type_has_open_vars),
        typed_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .any(|field| type_has_open_vars(&field.value))
                || record.spread.as_ref().is_some_and(|spread| match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        type_has_open_vars(ty)
                    }
                })
        }
        typed_ir::Type::Variant(variant) => {
            variant
                .cases
                .iter()
                .any(|case| case.payloads.iter().any(type_has_open_vars))
                || variant
                    .tail
                    .as_ref()
                    .is_some_and(|tail| type_has_open_vars(tail))
        }
        typed_ir::Type::Row { items, tail } => {
            items.iter().any(type_has_open_vars) || type_has_open_vars(tail)
        }
        typed_ir::Type::Recursive { body, .. } => type_has_open_vars(body),
    }
}

fn type_arg_has_open_vars(arg: &typed_ir::TypeArg) -> bool {
    match arg {
        typed_ir::TypeArg::Type(ty) => type_has_open_vars(ty),
        typed_ir::TypeArg::Bounds(bounds) => {
            bounds
                .lower
                .as_ref()
                .is_some_and(|ty| type_has_open_vars(ty))
                || bounds
                    .upper
                    .as_ref()
                    .is_some_and(|ty| type_has_open_vars(ty))
        }
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
    fn principal_graph_closes_curried_instance_from_argument_lowers() {
        let binding = pair_binding();
        let graph = PrincipalGraph::from_binding(&binding).unwrap();

        let solution = graph
            .solve_call_args_with_roles(
                vec![
                    RuntimeType::Core(int_type()),
                    RuntimeType::Core(bool_type()),
                ],
                None,
            )
            .unwrap();

        assert_eq!(
            solution.key,
            InstanceKey {
                original_binding: path(&["pair"]),
                closed_param_types: vec![
                    RuntimeType::Core(int_type()),
                    RuntimeType::Core(bool_type())
                ],
                closed_result_type: RuntimeType::Core(typed_ir::Type::Tuple(vec![
                    int_type(),
                    bool_type(),
                ])),
                closed_effect: typed_ir::Type::Never,
                captured_env_shape: None,
            }
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

    #[test]
    fn principal_graph_uses_role_associated_projection_to_close_result() {
        let binding = index_value_binding();
        let graph = PrincipalGraph::from_binding(&binding).unwrap();
        let roles = RoleContext::new([index_lines_impl()]);

        let solution = graph
            .solve_call_with_roles(
                RuntimeType::Core(lines_type(typed_ir::Type::Never)),
                Some(&roles),
            )
            .unwrap();

        assert_eq!(
            solution.key.closed_result_type,
            RuntimeType::Core(ref_str_type(typed_ir::Type::Never))
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

    fn pair_binding() -> Binding {
        Binding {
            name: path(&["pair"]),
            type_params: vec![typed_ir::TypeVar("a".into()), typed_ir::TypeVar("b".into())],
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: function_type(
                    typed_ir::Type::Var(typed_ir::TypeVar("a".into())),
                    function_type(
                        typed_ir::Type::Var(typed_ir::TypeVar("b".into())),
                        typed_ir::Type::Tuple(vec![
                            typed_ir::Type::Var(typed_ir::TypeVar("a".into())),
                            typed_ir::Type::Var(typed_ir::TypeVar("b".into())),
                        ]),
                    ),
                ),
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

    fn function_type(param: typed_ir::Type, ret: typed_ir::Type) -> typed_ir::Type {
        typed_ir::Type::Fun {
            param: Box::new(param),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(typed_ir::Type::Never),
            ret: Box::new(ret),
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
                body: typed_ir::Type::Fun {
                    param: Box::new(typed_ir::Type::Var(typed_ir::TypeVar("input".into()))),
                    param_effect: Box::new(typed_ir::Type::Never),
                    ret_effect: Box::new(typed_ir::Type::Never),
                    ret: Box::new(typed_ir::Type::Var(typed_ir::TypeVar("value".into()))),
                },
            },
            body: Expr::typed(ExprKind::Tuple(Vec::new()), RuntimeType::Unknown),
        }
    }

    fn index_lines_impl() -> typed_ir::RoleImplGraphNode {
        typed_ir::RoleImplGraphNode {
            role: path(&["std", "index", "Index"]),
            inputs: vec![typed_ir::TypeBounds::lower(lines_type(
                typed_ir::Type::Var(typed_ir::TypeVar("e".into())),
            ))],
            associated_types: vec![typed_ir::RecordField {
                name: typed_ir::Name("value".into()),
                value: typed_ir::TypeBounds::lower(ref_str_type(typed_ir::Type::Var(
                    typed_ir::TypeVar("e".into()),
                ))),
                optional: false,
            }],
            members: Vec::new(),
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

    fn ref_str_type(effect: typed_ir::Type) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path(&["std", "var", "Ref"]),
            args: vec![
                typed_ir::TypeArg::Type(effect),
                typed_ir::TypeArg::Type(typed_ir::Type::Named {
                    path: path(&["std", "string", "Str"]),
                    args: Vec::new(),
                }),
            ],
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
