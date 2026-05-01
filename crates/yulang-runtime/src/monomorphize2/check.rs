use std::collections::{HashMap, HashSet};

use super::*;
use crate::ir::{Binding, Expr, ExprKind, Module};

pub struct DemandChecker<'a> {
    bindings: HashMap<core_ir::Path, &'a Binding>,
    generic_bindings: HashSet<core_ir::Path>,
}

impl<'a> DemandChecker<'a> {
    pub fn from_module(module: &'a Module) -> Self {
        Self {
            bindings: module
                .bindings
                .iter()
                .map(|binding| (binding.name.clone(), binding))
                .collect(),
            generic_bindings: module
                .bindings
                .iter()
                .filter(|binding| !binding.type_params.is_empty())
                .map(|binding| binding.name.clone())
                .collect(),
        }
    }

    pub fn check_demand(&self, demand: &Demand) -> Result<CheckedDemand, DemandCheckError> {
        let binding = self
            .bindings
            .get(&demand.target)
            .copied()
            .ok_or_else(|| DemandCheckError::MissingBinding(demand.target.clone()))?;
        let mut checker = ExprChecker::new(&self.generic_bindings);
        let actual = checker.check_expr(&binding.body, &demand.key.signature)?;
        let (substitutions, child_demands) = checker.finish();
        Ok(CheckedDemand {
            target: demand.target.clone(),
            expected: demand.key.signature.clone(),
            actual,
            solved: substitutions.apply_signature(&demand.key.signature),
            substitutions,
            child_demands,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedDemand {
    pub target: core_ir::Path,
    pub expected: DemandSignature,
    pub actual: DemandSignature,
    pub solved: DemandSignature,
    pub substitutions: DemandSubstitution,
    pub child_demands: DemandQueue,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DemandCheckError {
    MissingBinding(core_ir::Path),
    Unify(DemandUnifyError),
}

impl From<DemandUnifyError> for DemandCheckError {
    fn from(error: DemandUnifyError) -> Self {
        Self::Unify(error)
    }
}

struct ExprChecker<'a> {
    generic_bindings: &'a HashSet<core_ir::Path>,
    locals: HashMap<core_ir::Path, DemandSignature>,
    unifier: DemandUnifier,
    child_demands: DemandQueue,
}

impl<'a> ExprChecker<'a> {
    fn new(generic_bindings: &'a HashSet<core_ir::Path>) -> Self {
        Self {
            generic_bindings,
            locals: HashMap::new(),
            unifier: DemandUnifier::new(),
            child_demands: DemandQueue::default(),
        }
    }

    fn check_expr(
        &mut self,
        expr: &Expr,
        expected: &DemandSignature,
    ) -> Result<DemandSignature, DemandCheckError> {
        let actual = self.synth_expr(expr, Some(expected))?;
        self.unifier.unify(expected, &actual)?;
        Ok(actual)
    }

    fn synth_expr(
        &mut self,
        expr: &Expr,
        expected: Option<&DemandSignature>,
    ) -> Result<DemandSignature, DemandCheckError> {
        match &expr.kind {
            ExprKind::Lambda { param, body, .. } => self.synth_lambda(expr, param, body, expected),
            ExprKind::Apply { callee, arg, .. } => {
                if let Some((target, args)) = applied_call(expr)
                    && self.generic_bindings.contains(target)
                {
                    let ret = expected
                        .cloned()
                        .unwrap_or_else(|| DemandSignature::from_runtime_type(&expr.ty));
                    let signature = curried_call_signature(&args, ret.clone());
                    self.child_demands.push_signature(
                        target.clone(),
                        curried_call_type(&args, expr.ty.clone()),
                        signature,
                    );
                    for arg in args {
                        self.synth_expr(arg, None)?;
                    }
                    return Ok(ret);
                }
                let callee = self.synth_expr(callee, None)?;
                let DemandSignature::Fun { param, ret } = callee else {
                    return Ok(DemandSignature::from_runtime_type(&expr.ty));
                };
                self.check_expr(arg, &param)?;
                Ok(*ret)
            }
            ExprKind::Var(path) => Ok(self
                .locals
                .get(path)
                .cloned()
                .unwrap_or_else(|| DemandSignature::from_runtime_type(&expr.ty))),
            ExprKind::Lit(_) => Ok(DemandSignature::from_runtime_type(&expr.ty)),
            _ => Ok(DemandSignature::from_runtime_type(&expr.ty)),
        }
    }

    fn synth_lambda(
        &mut self,
        expr: &Expr,
        param: &core_ir::Name,
        body: &Expr,
        expected: Option<&DemandSignature>,
    ) -> Result<DemandSignature, DemandCheckError> {
        let Some(
            expected @ DemandSignature::Fun {
                param: param_ty,
                ret,
            },
        ) = expected
        else {
            return Ok(DemandSignature::from_runtime_type(&expr.ty));
        };
        let local = core_ir::Path::from_name(param.clone());
        let previous = self.locals.insert(local.clone(), param_ty.as_ref().clone());
        self.check_expr(body, ret)?;
        restore_local(&mut self.locals, local, previous);
        Ok(expected.clone())
    }

    fn finish(self) -> (DemandSubstitution, DemandQueue) {
        (self.unifier.finish(), self.child_demands)
    }
}

fn curried_call_signature(args: &[&Expr], ret: DemandSignature) -> DemandSignature {
    args.iter()
        .rev()
        .fold(ret, |ret, arg| DemandSignature::Fun {
            param: Box::new(DemandSignature::from_runtime_type(&arg.ty)),
            ret: Box::new(ret),
        })
}

fn restore_local(
    locals: &mut HashMap<core_ir::Path, DemandSignature>,
    local: core_ir::Path,
    previous: Option<DemandSignature>,
) {
    match previous {
        Some(previous) => {
            locals.insert(local, previous);
        }
        None => {
            locals.remove(&local);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Expr, Root};

    #[test]
    fn checker_accepts_identity_at_concrete_demand() {
        let id = path("id");
        let module = module_with_binding(binding(
            id.clone(),
            vec![core_ir::TypeVar("a".to_string())],
            RuntimeType::fun(
                RuntimeType::core(core_ir::Type::Any),
                RuntimeType::core(core_ir::Type::Any),
            ),
            ExprKind::Lambda {
                param: core_ir::Name("x".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(Expr::typed(
                    ExprKind::Var(path("x")),
                    RuntimeType::core(core_ir::Type::Any),
                )),
            },
        ));
        let demand = Demand::new(
            id.clone(),
            RuntimeType::fun(
                RuntimeType::core(named("int")),
                RuntimeType::core(named("int")),
            ),
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked demand");

        assert_eq!(checked.target, id);
        assert_eq!(
            checked.solved,
            DemandSignature::from_runtime_type(&demand.expected)
        );
        assert!(checked.substitutions.values.is_empty());
    }

    #[test]
    fn checker_solves_return_hole_from_lambda_body() {
        let f = path("f");
        let module = module_with_binding(binding(
            f.clone(),
            vec![core_ir::TypeVar("a".to_string())],
            RuntimeType::fun(
                RuntimeType::core(core_ir::Type::Any),
                RuntimeType::core(core_ir::Type::Any),
            ),
            ExprKind::Lambda {
                param: core_ir::Name("x".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(Expr::typed(
                    ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                    RuntimeType::core(named("int")),
                )),
            },
        ));
        let demand = Demand::new(
            f,
            RuntimeType::fun(
                RuntimeType::core(named("unit")),
                RuntimeType::core(core_ir::Type::Any),
            ),
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked demand");

        assert_eq!(
            checked.solved,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Core(named_demand("unit"))),
                ret: Box::new(DemandSignature::Core(named_demand("int"))),
            }
        );
    }

    #[test]
    fn checker_checks_simple_application_inside_lambda() {
        let f = path("f");
        let module = module_with_binding(binding(
            f.clone(),
            vec![core_ir::TypeVar("a".to_string())],
            RuntimeType::fun(
                RuntimeType::core(named("int")),
                RuntimeType::core(named("int")),
            ),
            ExprKind::Lambda {
                param: core_ir::Name("x".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(Expr::typed(
                    ExprKind::Apply {
                        callee: Box::new(Expr::typed(
                            ExprKind::Lambda {
                                param: core_ir::Name("y".to_string()),
                                param_effect_annotation: None,
                                param_function_allowed_effects: None,
                                body: Box::new(Expr::typed(
                                    ExprKind::Var(path("y")),
                                    RuntimeType::core(named("int")),
                                )),
                            },
                            RuntimeType::fun(
                                RuntimeType::core(named("int")),
                                RuntimeType::core(named("int")),
                            ),
                        )),
                        arg: Box::new(Expr::typed(
                            ExprKind::Var(path("x")),
                            RuntimeType::core(named("int")),
                        )),
                        evidence: None,
                        instantiation: None,
                    },
                    RuntimeType::core(named("int")),
                )),
            },
        ));
        let demand = Demand::new(
            f,
            RuntimeType::fun(
                RuntimeType::core(named("int")),
                RuntimeType::core(named("int")),
            ),
        );

        DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked application");
    }

    #[test]
    fn checker_emits_child_demand_for_generic_call_in_body() {
        let id = path("id");
        let use_id = path("use_id");
        let module = Module {
            path: core_ir::Path::default(),
            bindings: vec![
                binding(
                    id.clone(),
                    vec![core_ir::TypeVar("a".to_string())],
                    RuntimeType::fun(
                        RuntimeType::core(core_ir::Type::Any),
                        RuntimeType::core(core_ir::Type::Any),
                    ),
                    ExprKind::Lambda {
                        param: core_ir::Name("x".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(Expr::typed(
                            ExprKind::Var(path("x")),
                            RuntimeType::core(core_ir::Type::Any),
                        )),
                    },
                ),
                binding(
                    use_id.clone(),
                    vec![core_ir::TypeVar("a".to_string())],
                    RuntimeType::fun(
                        RuntimeType::core(named("int")),
                        RuntimeType::core(named("int")),
                    ),
                    ExprKind::Lambda {
                        param: core_ir::Name("x".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(Expr::typed(
                            ExprKind::Apply {
                                callee: Box::new(Expr::typed(
                                    ExprKind::Var(id.clone()),
                                    RuntimeType::fun(
                                        RuntimeType::core(core_ir::Type::Any),
                                        RuntimeType::core(core_ir::Type::Any),
                                    ),
                                )),
                                arg: Box::new(Expr::typed(
                                    ExprKind::Var(path("x")),
                                    RuntimeType::core(named("int")),
                                )),
                                evidence: None,
                                instantiation: None,
                            },
                            RuntimeType::core(named("int")),
                        )),
                    },
                ),
            ],
            root_exprs: Vec::new(),
            roots: vec![Root::Binding(use_id.clone())],
        };
        let demand = Demand::new(
            use_id,
            RuntimeType::fun(
                RuntimeType::core(named("int")),
                RuntimeType::core(named("int")),
            ),
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked demand");
        let mut child_demands = checked.child_demands;
        let child = child_demands.pop_front().expect("child demand");

        assert_eq!(child.target, id);
        assert_eq!(
            child.key.signature,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Core(named_demand("int"))),
                ret: Box::new(DemandSignature::Core(named_demand("int"))),
            }
        );
        assert!(child_demands.is_empty());
    }

    fn module_with_binding(binding: Binding) -> Module {
        Module {
            path: core_ir::Path::default(),
            bindings: vec![binding],
            root_exprs: Vec::new(),
            roots: vec![Root::Binding(path("f"))],
        }
    }

    fn binding(
        name: core_ir::Path,
        type_params: Vec<core_ir::TypeVar>,
        ty: RuntimeType,
        kind: ExprKind,
    ) -> Binding {
        Binding {
            name,
            type_params,
            scheme: core_ir::Scheme {
                requirements: Vec::new(),
                body: core_ir::Type::Any,
            },
            body: Expr::typed(kind, ty),
        }
    }

    fn named(name: &str) -> core_ir::Type {
        core_ir::Type::Named {
            path: path(name),
            args: Vec::new(),
        }
    }

    fn named_demand(name: &str) -> DemandCoreType {
        DemandCoreType::Named {
            path: path(name),
            args: Vec::new(),
        }
    }

    fn path(name: &str) -> core_ir::Path {
        core_ir::Path::from_name(core_ir::Name(name.to_string()))
    }
}
