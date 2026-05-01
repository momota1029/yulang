use std::collections::{HashMap, HashSet};

use super::*;
use crate::ir::{Binding, Expr, ExprKind, Module, Pattern, Stmt, Type as RuntimeType};

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
    next_hole: u32,
    unifier: DemandUnifier,
    child_demands: DemandQueue,
}

impl<'a> ExprChecker<'a> {
    fn new(generic_bindings: &'a HashSet<core_ir::Path>) -> Self {
        Self {
            generic_bindings,
            locals: HashMap::new(),
            next_hole: 0,
            unifier: DemandUnifier::new(),
            child_demands: DemandQueue::default(),
        }
    }

    fn check_expr(
        &mut self,
        expr: &Expr,
        expected: &DemandSignature,
    ) -> Result<DemandSignature, DemandCheckError> {
        self.next_hole = self.next_hole.max(expected.next_hole_after());
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
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => self.synth_if(cond, then_branch, else_branch, expected),
            ExprKind::Tuple(items) => self.synth_tuple(items, expected),
            ExprKind::Block { stmts, tail } => self.synth_block(stmts, tail.as_deref(), expected),
            ExprKind::Apply { callee, arg, .. } => {
                if let Some((target, args)) = applied_call(expr)
                    && self.generic_bindings.contains(target)
                {
                    let ret = expected
                        .cloned()
                        .unwrap_or_else(|| self.signature_from_type(&expr.ty));
                    let arg_signatures = args
                        .iter()
                        .map(|arg| self.synth_expr(arg, None))
                        .collect::<Result<Vec<_>, _>>()?;
                    let signature = curried_signatures(&arg_signatures, ret.clone());
                    self.child_demands.push_signature(
                        target.clone(),
                        curried_call_type(&args, expr.ty.clone()),
                        signature,
                    );
                    return Ok(ret);
                }
                let callee = self.synth_expr(callee, None)?;
                let DemandSignature::Fun { param, ret } = callee else {
                    return Ok(self.signature_from_type(&expr.ty));
                };
                self.check_expr(arg, &param)?;
                Ok(*ret)
            }
            ExprKind::Var(path) => Ok(self
                .locals
                .get(path)
                .cloned()
                .unwrap_or_else(|| self.signature_from_type(&expr.ty))),
            ExprKind::Lit(_) => Ok(self.signature_from_type(&expr.ty)),
            _ => Ok(self.signature_from_type(&expr.ty)),
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
            return Ok(self.signature_from_type(&expr.ty));
        };
        let local = core_ir::Path::from_name(param.clone());
        let previous = self.locals.insert(local.clone(), param_ty.as_ref().clone());
        self.check_expr(body, ret)?;
        restore_local(&mut self.locals, local, previous);
        Ok(expected.clone())
    }

    fn synth_if(
        &mut self,
        cond: &Expr,
        then_branch: &Expr,
        else_branch: &Expr,
        expected: Option<&DemandSignature>,
    ) -> Result<DemandSignature, DemandCheckError> {
        self.synth_expr(cond, None)?;
        if let Some(expected) = expected {
            self.check_expr(then_branch, expected)?;
            self.check_expr(else_branch, expected)?;
            return Ok(expected.clone());
        }
        let then_ty = self.synth_expr(then_branch, None)?;
        let else_ty = self.synth_expr(else_branch, None)?;
        self.unifier.unify(&then_ty, &else_ty)?;
        Ok(then_ty)
    }

    fn synth_tuple(
        &mut self,
        items: &[Expr],
        expected: Option<&DemandSignature>,
    ) -> Result<DemandSignature, DemandCheckError> {
        if let Some(expected @ DemandSignature::Core(DemandCoreType::Tuple(expected_items))) =
            expected
            && expected_items.len() == items.len()
        {
            for (item, expected_item) in items.iter().zip(expected_items) {
                self.check_expr(item, &DemandSignature::Core(expected_item.clone()))?;
            }
            return Ok(expected.clone());
        }
        let items = items
            .iter()
            .map(|item| {
                self.synth_expr(item, None)
                    .map(|item| signature_core_value(&item))
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(DemandSignature::Core(DemandCoreType::Tuple(items)))
    }

    fn synth_block(
        &mut self,
        stmts: &[Stmt],
        tail: Option<&Expr>,
        expected: Option<&DemandSignature>,
    ) -> Result<DemandSignature, DemandCheckError> {
        let mut inserted = Vec::new();
        for stmt in stmts {
            if let Some(local) = self.synth_stmt(stmt)? {
                inserted.push(local);
            }
        }
        let result = match (tail, expected) {
            (Some(tail), Some(expected)) => {
                self.check_expr(tail, expected).map(|_| expected.clone())
            }
            (Some(tail), None) => self.synth_expr(tail, None),
            (None, Some(expected)) => {
                self.unifier
                    .unify(expected, &DemandSignature::Core(named_core("unit")))?;
                Ok(expected.clone())
            }
            (None, None) => Ok(DemandSignature::Core(named_core("unit"))),
        };
        for (local, previous) in inserted.into_iter().rev() {
            restore_local(&mut self.locals, local, previous);
        }
        result
    }

    fn synth_stmt(
        &mut self,
        stmt: &Stmt,
    ) -> Result<Option<(core_ir::Path, Option<DemandSignature>)>, DemandCheckError> {
        match stmt {
            Stmt::Let { pattern, value } => {
                let value = self.synth_expr(value, None)?;
                let Pattern::Bind { name, .. } = pattern else {
                    return Ok(None);
                };
                let local = core_ir::Path::from_name(name.clone());
                let previous = self.locals.insert(local.clone(), value);
                Ok(Some((local, previous)))
            }
            Stmt::Expr(expr) => {
                self.synth_expr(expr, None)?;
                Ok(None)
            }
            Stmt::Module { body, .. } => {
                self.synth_expr(body, None)?;
                Ok(None)
            }
        }
    }

    fn finish(self) -> (DemandSubstitution, DemandQueue) {
        (self.unifier.finish(), self.child_demands)
    }

    fn signature_from_type(&mut self, ty: &RuntimeType) -> DemandSignature {
        DemandSignature::from_runtime_type_with_holes(ty, &mut self.next_hole)
    }
}

fn signature_core_value(signature: &DemandSignature) -> DemandCoreType {
    match signature {
        DemandSignature::Hole(id) => DemandCoreType::Hole(*id),
        DemandSignature::Core(ty) => ty.clone(),
        DemandSignature::Fun { param, ret } => {
            let (param, param_effect) = signature_effected_core_value(param);
            let (ret, ret_effect) = signature_effected_core_value(ret);
            DemandCoreType::Fun {
                param: Box::new(param),
                param_effect: Box::new(param_effect),
                ret_effect: Box::new(ret_effect),
                ret: Box::new(ret),
            }
        }
        DemandSignature::Thunk { value, .. } => signature_core_value(value),
    }
}

fn signature_effected_core_value(signature: &DemandSignature) -> (DemandCoreType, DemandEffect) {
    match signature {
        DemandSignature::Thunk { effect, value } => (signature_core_value(value), effect.clone()),
        other => (signature_core_value(other), DemandEffect::Empty),
    }
}

fn named_core(name: &str) -> DemandCoreType {
    DemandCoreType::Named {
        path: core_ir::Path::from_name(core_ir::Name(name.to_string())),
        args: Vec::new(),
    }
}

pub(super) fn curried_signatures(
    args: &[DemandSignature],
    ret: DemandSignature,
) -> DemandSignature {
    args.iter()
        .rev()
        .fold(ret, |ret, arg| DemandSignature::Fun {
            param: Box::new(arg.clone()),
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
                                    RuntimeType::core(core_ir::Type::Any),
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

    #[test]
    fn checker_solves_block_tail_from_let_binding() {
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
                    ExprKind::Block {
                        stmts: vec![Stmt::Let {
                            pattern: Pattern::Bind {
                                name: core_ir::Name("y".to_string()),
                                ty: RuntimeType::core(core_ir::Type::Any),
                            },
                            value: Expr::typed(
                                ExprKind::Var(path("x")),
                                RuntimeType::core(core_ir::Type::Any),
                            ),
                        }],
                        tail: Some(Box::new(Expr::typed(
                            ExprKind::Var(path("y")),
                            RuntimeType::core(core_ir::Type::Any),
                        ))),
                    },
                    RuntimeType::core(core_ir::Type::Any),
                )),
            },
        ));
        let demand = Demand::new(
            f,
            RuntimeType::fun(
                RuntimeType::core(named("int")),
                RuntimeType::core(core_ir::Type::Any),
            ),
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked block");

        assert_eq!(
            checked.solved,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Core(named_demand("int"))),
                ret: Box::new(DemandSignature::Core(named_demand("int"))),
            }
        );
    }

    #[test]
    fn checker_solves_tuple_items_from_context() {
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
                    ExprKind::Tuple(vec![
                        Expr::typed(
                            ExprKind::Var(path("x")),
                            RuntimeType::core(core_ir::Type::Any),
                        ),
                        Expr::typed(
                            ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                            RuntimeType::core(named("int")),
                        ),
                    ]),
                    RuntimeType::core(core_ir::Type::Any),
                )),
            },
        ));
        let demand = Demand::new(
            f,
            RuntimeType::fun(
                RuntimeType::core(named("int")),
                RuntimeType::core(core_ir::Type::Any),
            ),
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked tuple");

        assert_eq!(
            checked.solved,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Core(named_demand("int"))),
                ret: Box::new(DemandSignature::Core(DemandCoreType::Tuple(vec![
                    named_demand("int"),
                    named_demand("int"),
                ]))),
            }
        );
    }

    #[test]
    fn checker_solves_if_branches_from_context() {
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
                    ExprKind::If {
                        cond: Box::new(Expr::typed(
                            ExprKind::Lit(core_ir::Lit::Bool(true)),
                            RuntimeType::core(named("bool")),
                        )),
                        then_branch: Box::new(Expr::typed(
                            ExprKind::Var(path("x")),
                            RuntimeType::core(core_ir::Type::Any),
                        )),
                        else_branch: Box::new(Expr::typed(
                            ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                            RuntimeType::core(named("int")),
                        )),
                        evidence: None,
                    },
                    RuntimeType::core(core_ir::Type::Any),
                )),
            },
        ));
        let demand = Demand::new(
            f,
            RuntimeType::fun(
                RuntimeType::core(named("int")),
                RuntimeType::core(core_ir::Type::Any),
            ),
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked if");

        assert_eq!(
            checked.solved,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Core(named_demand("int"))),
                ret: Box::new(DemandSignature::Core(named_demand("int"))),
            }
        );
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
