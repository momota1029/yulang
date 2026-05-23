use std::collections::{BTreeMap, HashMap, HashSet};

use yulang_runtime_ir::{
    Binding, Expr, ExprKind, RecordExprField, RecordSpreadExpr, Stmt, Type as RuntimeType,
};
use yulang_typed_ir as typed_ir;

use crate::diagnostic::{BodyIncompleteReason, FinalizeDiagnostic, FinalizeError, FinalizeResult};
use crate::effect::{
    close_handle_effect, expr_forced_effect, handler_output_type, materialize_handle_effect,
    project_runtime_effect, runtime_value_type, should_thunk_effect,
};
use crate::principal::{InstanceKey, PrincipalGraph, PrincipalSolution};
use crate::role::{RoleContext, RoleProjectionStatus, role_method_parts};
use crate::types::{
    LowerSubstitutions, materialize_core_type, materialize_expr_type, materialize_runtime_type,
    path_as_local_name, runtime_type_is_closed, runtime_types_match,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BodyGraph {
    binding: typed_ir::Path,
    param: typed_ir::Name,
    body: Expr,
    expected_result: RuntimeType,
    expected_effect: typed_ir::Type,
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
            expected_effect: key.closed_effect.clone(),
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
        let expected_body_type = self.expected_body_type();
        if !runtime_types_match(&self.expected_result, &solved_body.ty)
            && !runtime_types_match(&expected_body_type, &solved_body.ty)
        {
            return Err(FinalizeError::Diagnostic(
                FinalizeDiagnostic::BodyResultMismatch {
                    binding: self.binding.clone(),
                    expected: expected_body_type,
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
            result_type: solved_body.ty.clone(),
            body: solved_body,
            nested_instances: dedupe_nested_instances(nested_instances),
        })
    }

    fn expected_body_type(&self) -> RuntimeType {
        if should_thunk_effect(&self.expected_effect) {
            RuntimeType::Thunk {
                effect: self.expected_effect.clone(),
                value: Box::new(self.expected_result.clone()),
            }
        } else {
            self.expected_result.clone()
        }
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
            ExprKind::EffectOp(path) => {
                let ty = self.require_closed_expr_type(materialized_ty)?;
                Ok(Expr::typed(ExprKind::EffectOp(path), ty))
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
            ExprKind::Record { fields, spread } => {
                let solved_fields = fields
                    .into_iter()
                    .map(|field| {
                        let value = self.solve_expr(env, nested_instances, field.value)?;
                        Ok(RecordExprField {
                            name: field.name,
                            value,
                        })
                    })
                    .collect::<FinalizeResult<Vec<_>>>()?;
                let solved_spread = spread
                    .map(|spread| self.solve_record_spread(env, nested_instances, spread))
                    .transpose()?;
                let inferred = infer_record_type(&solved_fields, solved_spread.as_ref());
                let ty = self.choose_known_type(materialized_ty, inferred)?;
                Ok(Expr::typed(
                    ExprKind::Record {
                        fields: solved_fields,
                        spread: solved_spread,
                    },
                    ty,
                ))
            }
            ExprKind::Select { base, field } => {
                let solved_base = self.solve_expr(env, nested_instances, *base)?;
                let inferred = select_field_type(&solved_base.ty, &field);
                let ty = self.choose_known_type(materialized_ty, inferred)?;
                Ok(Expr::typed(
                    ExprKind::Select {
                        base: Box::new(solved_base),
                        field,
                    },
                    ty,
                ))
            }
            ExprKind::Variant { tag, value } => {
                let solved_value = value
                    .map(|value| self.solve_expr(env, nested_instances, *value))
                    .transpose()?;
                let inferred = infer_variant_type(&tag, solved_value.as_ref());
                let ty = self.choose_known_type(materialized_ty, inferred)?;
                Ok(Expr::typed(
                    ExprKind::Variant {
                        tag,
                        value: solved_value.map(Box::new),
                    },
                    ty,
                ))
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                evidence,
            } => {
                let solved_cond =
                    force_thunk_value(self.solve_expr(env, nested_instances, *cond)?);
                let solved_then =
                    force_thunk_value(self.solve_expr(env, nested_instances, *then_branch)?);
                let solved_else =
                    force_thunk_value(self.solve_expr(env, nested_instances, *else_branch)?);
                let evidence = evidence.map(|evidence| yulang_runtime_ir::JoinEvidence {
                    result: materialize_core_type(evidence.result, &self.substitutions),
                });
                let materialized_value_ty = runtime_value_type(&materialized_ty);
                let inferred = evidence
                    .as_ref()
                    .map(|evidence| RuntimeType::Core(evidence.result.clone()))
                    .or_else(|| {
                        runtime_types_match(&solved_then.ty, &solved_else.ty)
                            .then(|| solved_then.ty.clone())
                    });
                let value_ty = self.choose_known_type(materialized_value_ty, inferred)?;
                let solved_then = self.adapt_join_branch(&value_ty, solved_then)?;
                let solved_else = self.adapt_join_branch(&value_ty, solved_else)?;
                let expr = Expr::typed(
                    ExprKind::If {
                        cond: Box::new(solved_cond),
                        then_branch: Box::new(solved_then),
                        else_branch: Box::new(solved_else),
                        evidence,
                    },
                    value_ty,
                );
                let expr = attach_forced_effect(expr);
                let ty = self.choose_known_type(materialized_ty, Some(expr.ty.clone()))?;
                Ok(Expr::typed(expr.kind, ty))
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
                let solved_callee = self.solve_expr(env, nested_instances, *callee)?;
                if let Some((expected_arg, result)) = runtime_function_parts(&solved_callee.ty) {
                    let solved_arg_ty =
                        self.choose_known_type(solved_arg.ty.clone(), Some(expected_arg))?;
                    let solved_arg = if solved_arg_ty == solved_arg.ty {
                        solved_arg
                    } else {
                        Expr::typed(solved_arg.kind, solved_arg_ty)
                    };
                    let ty = self.choose_known_type(materialized_ty, Some(result))?;
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
                Err(FinalizeError::Diagnostic(
                    FinalizeDiagnostic::UnsupportedBodyShape {
                        binding: self.binding.clone(),
                        reason: BodyIncompleteReason::UnsupportedExpression,
                    },
                ))
            }
            ExprKind::Handle {
                body,
                arms,
                evidence,
                handler,
            } => self.solve_handle_expr(
                env,
                nested_instances,
                materialized_ty,
                *body,
                arms,
                evidence,
                handler,
            ),
            ExprKind::BindHere { expr } => {
                let solved_expr = self.solve_expr(env, nested_instances, *expr)?;
                let forced_ty = runtime_value_type(&solved_expr.ty);
                let ty = self.choose_known_type(materialized_ty, Some(forced_ty))?;
                Ok(Expr::typed(
                    ExprKind::BindHere {
                        expr: Box::new(solved_expr),
                    },
                    ty,
                ))
            }
            ExprKind::Thunk {
                effect,
                value,
                expr,
            } => {
                let closed_effect = materialize_core_type(effect, &self.substitutions);
                let closed_value = materialize_runtime_type(value, &self.substitutions);
                let solved_expr = self.solve_expr(env, nested_instances, *expr)?;
                self.choose_known_type(closed_value.clone(), Some(solved_expr.ty.clone()))?;
                let thunk_ty = RuntimeType::Thunk {
                    effect: closed_effect.clone(),
                    value: Box::new(closed_value.clone()),
                };
                let ty = self.choose_known_type(materialized_ty, Some(thunk_ty))?;
                Ok(Expr::typed(
                    ExprKind::Thunk {
                        effect: closed_effect,
                        value: closed_value,
                        expr: Box::new(solved_expr),
                    },
                    ty,
                ))
            }
            ExprKind::LocalPushId { id, body } => {
                let solved_body = self.solve_expr(env, nested_instances, *body)?;
                let ty = self.choose_known_type(materialized_ty, Some(solved_body.ty.clone()))?;
                Ok(Expr::typed(
                    ExprKind::LocalPushId {
                        id,
                        body: Box::new(solved_body),
                    },
                    ty,
                ))
            }
            ExprKind::AddId {
                id,
                allowed,
                active,
                thunk,
            } => {
                let solved_thunk = self.solve_expr(env, nested_instances, *thunk)?;
                let ty = self.choose_known_type(materialized_ty, Some(solved_thunk.ty.clone()))?;
                Ok(Expr::typed(
                    ExprKind::AddId {
                        id,
                        allowed: materialize_core_type(allowed, &self.substitutions),
                        active,
                        thunk: Box::new(solved_thunk),
                    },
                    ty,
                ))
            }
            ExprKind::Coerce { from, to, expr } => {
                let solved_expr = self.solve_expr(env, nested_instances, *expr)?;
                let closed_to = materialize_core_type(to, &self.substitutions);
                let ty = self.choose_known_type(
                    materialized_ty,
                    Some(RuntimeType::Core(closed_to.clone())),
                )?;
                Ok(Expr::typed(
                    ExprKind::Coerce {
                        from: materialize_core_type(from, &self.substitutions),
                        to: closed_to,
                        expr: Box::new(solved_expr),
                    },
                    ty,
                ))
            }
            ExprKind::Pack { var, expr } => {
                let solved_expr = self.solve_expr(env, nested_instances, *expr)?;
                let ty = self.choose_known_type(materialized_ty, Some(solved_expr.ty.clone()))?;
                Ok(Expr::typed(
                    ExprKind::Pack {
                        var,
                        expr: Box::new(solved_expr),
                    },
                    ty,
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

    fn solve_handle_expr(
        &self,
        env: &mut BTreeMap<typed_ir::Name, RuntimeType>,
        nested_instances: &mut Vec<NestedInstancePlan>,
        materialized_ty: RuntimeType,
        body: Expr,
        arms: Vec<yulang_runtime_ir::HandleArm>,
        evidence: yulang_runtime_ir::JoinEvidence,
        handler: yulang_runtime_ir::HandleEffect,
    ) -> FinalizeResult<Expr> {
        let solved_body = self.solve_expr(env, nested_instances, body)?;
        let handler = materialize_handle_effect(handler, &self.substitutions);
        let mut solved_arms = Vec::with_capacity(arms.len());
        let mut arm_effects = Vec::new();
        for arm in arms {
            let solved_arm = self.solve_handle_arm(env, nested_instances, arm)?;
            if let Some(guard) = &solved_arm.guard {
                if let Some(effect) = expr_forced_effect(guard) {
                    arm_effects.push(effect);
                }
            }
            if let Some(effect) = expr_forced_effect(&solved_arm.body) {
                arm_effects.push(effect);
            }
            solved_arms.push(solved_arm);
        }
        let residual_before = handler
            .residual_before
            .clone()
            .or_else(|| crate::effect::thunk_effect(&solved_body.ty))
            .unwrap_or(typed_ir::Type::Never);
        let handler = close_handle_effect(
            residual_before,
            &handler.consumes,
            arm_effects
                .into_iter()
                .reduce(crate::effect::merge_effect_rows),
        );
        let inferred = handler_output_type(&solved_body.ty, &handler);
        let ty = self.choose_known_type(materialized_ty, Some(inferred))?;
        Ok(Expr::typed(
            ExprKind::Handle {
                body: Box::new(solved_body),
                arms: solved_arms,
                evidence,
                handler,
            },
            ty,
        ))
    }

    fn solve_record_spread(
        &self,
        env: &mut BTreeMap<typed_ir::Name, RuntimeType>,
        nested_instances: &mut Vec<NestedInstancePlan>,
        spread: RecordSpreadExpr,
    ) -> FinalizeResult<RecordSpreadExpr> {
        match spread {
            RecordSpreadExpr::Head(expr) => Ok(RecordSpreadExpr::Head(Box::new(self.solve_expr(
                env,
                nested_instances,
                *expr,
            )?))),
            RecordSpreadExpr::Tail(expr) => Ok(RecordSpreadExpr::Tail(Box::new(self.solve_expr(
                env,
                nested_instances,
                *expr,
            )?))),
        }
    }

    fn solve_handle_arm(
        &self,
        env: &BTreeMap<typed_ir::Name, RuntimeType>,
        nested_instances: &mut Vec<NestedInstancePlan>,
        arm: yulang_runtime_ir::HandleArm,
    ) -> FinalizeResult<yulang_runtime_ir::HandleArm> {
        let mut arm_env = env.clone();
        let payload = self.solve_pattern(&mut arm_env, arm.payload)?;
        let resume = arm
            .resume
            .map(|resume| self.solve_resume_binding(&mut arm_env, resume))
            .transpose()?;
        let guard = arm
            .guard
            .map(|guard| self.solve_expr(&mut arm_env, nested_instances, guard))
            .transpose()?;
        let body = self.solve_expr(&mut arm_env, nested_instances, arm.body)?;
        Ok(yulang_runtime_ir::HandleArm {
            effect: arm.effect,
            payload,
            resume,
            guard,
            body,
        })
    }

    fn solve_resume_binding(
        &self,
        env: &mut BTreeMap<typed_ir::Name, RuntimeType>,
        resume: yulang_runtime_ir::ResumeBinding,
    ) -> FinalizeResult<yulang_runtime_ir::ResumeBinding> {
        let ty = materialize_expr_type(resume.ty, &self.substitutions);
        let ty = self.require_closed_expr_type(ty)?;
        env.insert(resume.name.clone(), ty.clone());
        Ok(yulang_runtime_ir::ResumeBinding {
            name: resume.name,
            ty,
        })
    }

    fn solve_pattern(
        &self,
        env: &mut BTreeMap<typed_ir::Name, RuntimeType>,
        pattern: yulang_runtime_ir::Pattern,
    ) -> FinalizeResult<yulang_runtime_ir::Pattern> {
        match pattern {
            yulang_runtime_ir::Pattern::Bind { name, ty } => {
                let ty = materialize_expr_type(ty, &self.substitutions);
                let ty = self.require_closed_expr_type(ty)?;
                env.insert(name.clone(), ty.clone());
                Ok(yulang_runtime_ir::Pattern::Bind { name, ty })
            }
            yulang_runtime_ir::Pattern::Wildcard { ty } => {
                let ty = materialize_expr_type(ty, &self.substitutions);
                let ty = self.require_closed_expr_type(ty)?;
                Ok(yulang_runtime_ir::Pattern::Wildcard { ty })
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

    fn adapt_join_branch(&self, expected: &RuntimeType, branch: Expr) -> FinalizeResult<Expr> {
        let actual = runtime_value_type(&branch.ty);
        if runtime_type_flows_to(expected, &actual) {
            return Ok(branch);
        }
        if let Some((from, to)) = runtime_coercion(&actual, expected) {
            return Ok(Expr::typed(
                ExprKind::Coerce {
                    from,
                    to,
                    expr: Box::new(branch),
                },
                expected.clone(),
            ));
        }
        Err(FinalizeError::Diagnostic(
            FinalizeDiagnostic::BodyResultMismatch {
                binding: self.binding.clone(),
                expected: expected.clone(),
                actual,
            },
        ))
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

fn force_thunk_value(expr: Expr) -> Expr {
    let RuntimeType::Thunk { value, .. } = expr.ty.clone() else {
        return expr;
    };
    Expr::typed(
        ExprKind::BindHere {
            expr: Box::new(expr),
        },
        *value,
    )
}

fn attach_forced_effect(expr: Expr) -> Expr {
    let Some(effect) = expr_forced_effect(&expr).map(|effect| project_runtime_effect(&effect))
    else {
        return expr;
    };
    if !should_thunk_effect(&effect) {
        return expr;
    }
    let value = expr.ty.clone();
    Expr::typed(
        ExprKind::Thunk {
            effect: effect.clone(),
            value: value.clone(),
            expr: Box::new(expr),
        },
        RuntimeType::Thunk {
            effect,
            value: Box::new(value),
        },
    )
}

fn runtime_type_flows_to(expected: &RuntimeType, actual: &RuntimeType) -> bool {
    let actual = runtime_value_type(actual);
    runtime_types_match(expected, &actual)
        || matches!(actual, RuntimeType::Core(typed_ir::Type::Never))
}

fn runtime_coercion(
    actual: &RuntimeType,
    expected: &RuntimeType,
) -> Option<(typed_ir::Type, typed_ir::Type)> {
    match (actual, expected) {
        (
            RuntimeType::Core(actual @ typed_ir::Type::Named { .. }),
            RuntimeType::Core(expected @ typed_ir::Type::Named { .. }),
        ) if can_widen_runtime_value(actual, expected) => Some((actual.clone(), expected.clone())),
        _ => None,
    }
}

fn can_widen_runtime_value(actual: &typed_ir::Type, expected: &typed_ir::Type) -> bool {
    match (actual, expected) {
        (
            typed_ir::Type::Named {
                path: actual_path,
                args: actual_args,
            },
            typed_ir::Type::Named {
                path: expected_path,
                args: expected_args,
            },
        ) if actual_args.is_empty() && expected_args.is_empty() => {
            actual_path != expected_path
                && typed_ir::can_widen_named_paths(actual_path, expected_path)
        }
        _ => false,
    }
}

fn runtime_core_type(ty: &RuntimeType) -> Option<typed_ir::Type> {
    match ty {
        RuntimeType::Core(ty) => Some(ty.clone()),
        RuntimeType::Unknown | RuntimeType::Fun { .. } | RuntimeType::Thunk { .. } => None,
    }
}

fn runtime_function_parts(ty: &RuntimeType) -> Option<(RuntimeType, RuntimeType)> {
    match ty {
        RuntimeType::Fun { param, ret } => Some((param.as_ref().clone(), ret.as_ref().clone())),
        RuntimeType::Core(typed_ir::Type::Fun {
            param,
            ret_effect,
            ret,
            ..
        }) => {
            let value = RuntimeType::Core(ret.as_ref().clone());
            let effect = crate::effect::project_runtime_effect(ret_effect);
            let ret = if crate::effect::should_thunk_effect(&effect) {
                RuntimeType::Thunk {
                    effect,
                    value: Box::new(value),
                }
            } else {
                value
            };
            Some((RuntimeType::Core(param.as_ref().clone()), ret))
        }
        RuntimeType::Unknown | RuntimeType::Core(_) | RuntimeType::Thunk { .. } => None,
    }
}

fn infer_record_type(
    fields: &[RecordExprField],
    spread: Option<&RecordSpreadExpr>,
) -> Option<RuntimeType> {
    if spread.is_some() {
        return None;
    }
    let fields = fields
        .iter()
        .map(|field| {
            let RuntimeType::Core(ty) = &field.value.ty else {
                return None;
            };
            Some(typed_ir::RecordField {
                name: field.name.clone(),
                value: ty.clone(),
                optional: false,
            })
        })
        .collect::<Option<Vec<_>>>()?;
    Some(RuntimeType::Core(typed_ir::Type::Record(
        typed_ir::RecordType {
            fields,
            spread: None,
        },
    )))
}

fn select_field_type(base: &RuntimeType, field: &typed_ir::Name) -> Option<RuntimeType> {
    let RuntimeType::Core(typed_ir::Type::Record(record)) = base else {
        return None;
    };
    record
        .fields
        .iter()
        .find(|record_field| &record_field.name == field)
        .map(|field| RuntimeType::Core(field.value.clone()))
}

fn infer_variant_type(tag: &typed_ir::Name, value: Option<&Expr>) -> Option<RuntimeType> {
    let payloads = match value {
        Some(value) => {
            let RuntimeType::Core(ty) = &value.ty else {
                return None;
            };
            vec![ty.clone()]
        }
        None => Vec::new(),
    };
    Some(RuntimeType::Core(typed_ir::Type::Variant(
        typed_ir::VariantType {
            cases: vec![typed_ir::VariantCase {
                name: tag.clone(),
                payloads,
            }],
            tail: None,
        },
    )))
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

    #[test]
    fn body_graph_forces_thunk_with_bind_here() {
        let principal = PrincipalSolution {
            key: InstanceKey {
                original_binding: path(&["force_io"]),
                closed_param_types: vec![RuntimeType::Thunk {
                    effect: effect_row(&["io"]),
                    value: Box::new(RuntimeType::Core(int_type())),
                }],
                closed_result_type: RuntimeType::Core(int_type()),
                closed_effect: effect_row(&["io"]),
                captured_env_shape: None,
            },
            substitutions: Vec::new(),
        };

        let graph = BodyGraph::from_binding_instance(&force_io_binding(), &principal).unwrap();
        let solution = graph.solve().unwrap();

        assert_eq!(solution.body.ty, RuntimeType::Core(int_type()));
    }

    #[test]
    fn body_graph_handler_subtracts_consumed_effects() {
        let principal = PrincipalSolution {
            key: InstanceKey {
                original_binding: path(&["handle_io"]),
                closed_param_types: vec![RuntimeType::Core(unit_type())],
                closed_result_type: RuntimeType::Core(int_type()),
                closed_effect: effect_row(&["log"]),
                captured_env_shape: None,
            },
            substitutions: Vec::new(),
        };

        let graph = BodyGraph::from_binding_instance(&handle_io_binding(), &principal).unwrap();
        let solution = graph.solve().unwrap();

        assert_eq!(
            solution.body.ty,
            RuntimeType::Thunk {
                effect: effect_row(&["log"]),
                value: Box::new(RuntimeType::Core(int_type())),
            }
        );
        let ExprKind::Handle { handler, .. } = &solution.body.kind else {
            panic!("expected handle");
        };
        assert_eq!(handler.residual_before, Some(effect_row(&["io", "log"])));
        assert_eq!(handler.residual_after, Some(effect_row(&["log"])));
    }

    #[test]
    fn body_graph_applies_closed_effect_operation_callee() {
        let principal = PrincipalSolution {
            key: InstanceKey {
                original_binding: path(&["perform_io"]),
                closed_param_types: vec![RuntimeType::Core(unit_type())],
                closed_result_type: RuntimeType::Core(int_type()),
                closed_effect: effect_row(&["io"]),
                captured_env_shape: None,
            },
            substitutions: Vec::new(),
        };

        let graph = BodyGraph::from_binding_instance(&perform_io_binding(), &principal).unwrap();
        let solution = graph.solve().unwrap();

        assert_eq!(
            solution.body.ty,
            RuntimeType::Thunk {
                effect: effect_row(&["io"]),
                value: Box::new(RuntimeType::Core(int_type())),
            }
        );
    }

    #[test]
    fn body_graph_solves_if_with_matching_branch_types() {
        let principal = PrincipalSolution {
            key: InstanceKey {
                original_binding: path(&["choose_int"]),
                closed_param_types: vec![RuntimeType::Core(bool_type())],
                closed_result_type: RuntimeType::Core(int_type()),
                closed_effect: typed_ir::Type::Never,
                captured_env_shape: None,
            },
            substitutions: Vec::new(),
        };

        let graph = BodyGraph::from_binding_instance(&choose_int_binding(), &principal).unwrap();
        let solution = graph.solve().unwrap();

        assert_eq!(solution.body.ty, RuntimeType::Core(int_type()));
    }

    #[test]
    fn body_graph_solves_record_and_select() {
        let principal = PrincipalSolution {
            key: InstanceKey {
                original_binding: path(&["select_answer"]),
                closed_param_types: vec![RuntimeType::Core(unit_type())],
                closed_result_type: RuntimeType::Core(int_type()),
                closed_effect: typed_ir::Type::Never,
                captured_env_shape: None,
            },
            substitutions: Vec::new(),
        };

        let graph = BodyGraph::from_binding_instance(&select_answer_binding(), &principal).unwrap();
        let solution = graph.solve().unwrap();

        assert_eq!(solution.body.ty, RuntimeType::Core(int_type()));
    }

    #[test]
    fn body_graph_solves_variant_construction() {
        let principal = PrincipalSolution {
            key: InstanceKey {
                original_binding: path(&["some_int"]),
                closed_param_types: vec![RuntimeType::Core(unit_type())],
                closed_result_type: RuntimeType::Core(some_int_type()),
                closed_effect: typed_ir::Type::Never,
                captured_env_shape: None,
            },
            substitutions: Vec::new(),
        };

        let graph = BodyGraph::from_binding_instance(&some_int_binding(), &principal).unwrap();
        let solution = graph.solve().unwrap();

        assert_eq!(solution.body.ty, RuntimeType::Core(some_int_type()));
    }

    #[test]
    fn body_graph_lifts_if_condition_effect_to_thunk_result() {
        let effect = effect_row(&["junction"]);
        let principal = PrincipalSolution {
            key: InstanceKey {
                original_binding: path(&["choose_with_effectful_cond"]),
                closed_param_types: vec![RuntimeType::Core(unit_type())],
                closed_result_type: RuntimeType::Core(int_type()),
                closed_effect: effect.clone(),
                captured_env_shape: None,
            },
            substitutions: Vec::new(),
        };

        let graph =
            BodyGraph::from_binding_instance(&choose_with_effectful_cond_binding(), &principal)
                .unwrap();
        let solution = graph.solve().unwrap();

        assert_eq!(
            solution.body.ty,
            RuntimeType::Thunk {
                effect: effect.clone(),
                value: Box::new(RuntimeType::Core(int_type())),
            }
        );
        let ExprKind::Thunk { expr, .. } = &solution.body.kind else {
            panic!("if should be lifted into an effect thunk");
        };
        let ExprKind::If { cond, .. } = &expr.kind else {
            panic!("thunk body should remain an if");
        };
        assert!(matches!(cond.kind, ExprKind::BindHere { .. }));
    }

    #[test]
    fn body_graph_coerces_if_branch_to_join_result_type() {
        let principal = PrincipalSolution {
            key: InstanceKey {
                original_binding: path(&["choose_float"]),
                closed_param_types: vec![RuntimeType::Core(bool_type())],
                closed_result_type: RuntimeType::Core(float_type()),
                closed_effect: typed_ir::Type::Never,
                captured_env_shape: None,
            },
            substitutions: Vec::new(),
        };

        let graph = BodyGraph::from_binding_instance(&choose_float_binding(), &principal).unwrap();
        let solution = graph.solve().unwrap();

        assert_eq!(solution.body.ty, RuntimeType::Core(float_type()));
        let ExprKind::If { then_branch, .. } = &solution.body.kind else {
            panic!("body should remain an if");
        };
        let ExprKind::Coerce { from, to, expr } = &then_branch.kind else {
            panic!("int branch should be coerced to float");
        };
        assert_eq!(*from, qualified_int_type());
        assert_eq!(*to, float_type());
        assert_eq!(expr.ty, RuntimeType::Core(qualified_int_type()));
    }

    #[test]
    fn body_graph_coerces_if_int_branch_to_frac_result_type() {
        let principal = PrincipalSolution {
            key: InstanceKey {
                original_binding: path(&["choose_frac"]),
                closed_param_types: vec![RuntimeType::Core(bool_type())],
                closed_result_type: RuntimeType::Core(frac_type()),
                closed_effect: typed_ir::Type::Never,
                captured_env_shape: None,
            },
            substitutions: Vec::new(),
        };

        let graph = BodyGraph::from_binding_instance(&choose_frac_binding(), &principal).unwrap();
        let solution = graph.solve().unwrap();

        assert_eq!(solution.body.ty, RuntimeType::Core(frac_type()));
        let ExprKind::If { then_branch, .. } = &solution.body.kind else {
            panic!("body should remain an if");
        };
        let ExprKind::Coerce { from, to, expr } = &then_branch.kind else {
            panic!("int branch should be coerced to frac");
        };
        assert_eq!(*from, simple_int_type());
        assert_eq!(*to, frac_type());
        assert_eq!(expr.ty, RuntimeType::Core(simple_int_type()));
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

    fn choose_int_binding() -> Binding {
        Binding {
            name: path(&["choose_int"]),
            type_params: Vec::new(),
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: function_type(bool_type(), int_type()),
            },
            body: Expr::typed(
                ExprKind::Lambda {
                    param: typed_ir::Name("flag".into()),
                    param_effect_annotation: None,
                    param_function_allowed_effects: None,
                    body: Box::new(Expr::typed(
                        ExprKind::If {
                            cond: Box::new(Expr::typed(
                                ExprKind::Var(path(&["flag"])),
                                RuntimeType::Core(bool_type()),
                            )),
                            then_branch: Box::new(Expr::typed(
                                ExprKind::Lit(typed_ir::Lit::Int("1".into())),
                                RuntimeType::Core(int_type()),
                            )),
                            else_branch: Box::new(Expr::typed(
                                ExprKind::Lit(typed_ir::Lit::Int("2".into())),
                                RuntimeType::Core(int_type()),
                            )),
                            evidence: Some(yulang_runtime_ir::JoinEvidence { result: int_type() }),
                        },
                        RuntimeType::Unknown,
                    )),
                },
                RuntimeType::Unknown,
            ),
        }
    }

    fn select_answer_binding() -> Binding {
        Binding {
            name: path(&["select_answer"]),
            type_params: Vec::new(),
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: function_type(unit_type(), int_type()),
            },
            body: Expr::typed(
                ExprKind::Lambda {
                    param: typed_ir::Name("_unit".into()),
                    param_effect_annotation: None,
                    param_function_allowed_effects: None,
                    body: Box::new(Expr::typed(
                        ExprKind::Select {
                            base: Box::new(Expr::typed(
                                ExprKind::Record {
                                    fields: vec![RecordExprField {
                                        name: typed_ir::Name("answer".into()),
                                        value: Expr::typed(
                                            ExprKind::Lit(typed_ir::Lit::Int("42".into())),
                                            RuntimeType::Core(int_type()),
                                        ),
                                    }],
                                    spread: None,
                                },
                                RuntimeType::Unknown,
                            )),
                            field: typed_ir::Name("answer".into()),
                        },
                        RuntimeType::Unknown,
                    )),
                },
                RuntimeType::Unknown,
            ),
        }
    }

    fn choose_with_effectful_cond_binding() -> Binding {
        let effect = effect_row(&["junction"]);
        Binding {
            name: path(&["choose_with_effectful_cond"]),
            type_params: Vec::new(),
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: typed_ir::Type::Fun {
                    param: Box::new(unit_type()),
                    param_effect: Box::new(typed_ir::Type::Never),
                    ret_effect: Box::new(effect.clone()),
                    ret: Box::new(int_type()),
                },
            },
            body: Expr::typed(
                ExprKind::Lambda {
                    param: typed_ir::Name("_unit".into()),
                    param_effect_annotation: None,
                    param_function_allowed_effects: None,
                    body: Box::new(Expr::typed(
                        ExprKind::If {
                            cond: Box::new(Expr::typed(
                                ExprKind::Apply {
                                    callee: Box::new(Expr::typed(
                                        ExprKind::Var(path(&["make_flag"])),
                                        RuntimeType::Fun {
                                            param: Box::new(RuntimeType::Core(unit_type())),
                                            ret: Box::new(RuntimeType::Thunk {
                                                effect: effect.clone(),
                                                value: Box::new(RuntimeType::Core(bool_type())),
                                            }),
                                        },
                                    )),
                                    arg: Box::new(Expr::typed(
                                        ExprKind::Var(path(&["_unit"])),
                                        RuntimeType::Core(unit_type()),
                                    )),
                                    evidence: None,
                                    instantiation: None,
                                },
                                RuntimeType::Unknown,
                            )),
                            then_branch: Box::new(Expr::typed(
                                ExprKind::Lit(typed_ir::Lit::Int("1".into())),
                                RuntimeType::Core(int_type()),
                            )),
                            else_branch: Box::new(Expr::typed(
                                ExprKind::Lit(typed_ir::Lit::Int("0".into())),
                                RuntimeType::Core(int_type()),
                            )),
                            evidence: Some(yulang_runtime_ir::JoinEvidence { result: int_type() }),
                        },
                        RuntimeType::Unknown,
                    )),
                },
                RuntimeType::Unknown,
            ),
        }
    }

    fn choose_float_binding() -> Binding {
        Binding {
            name: path(&["choose_float"]),
            type_params: Vec::new(),
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: function_type(bool_type(), float_type()),
            },
            body: Expr::typed(
                ExprKind::Lambda {
                    param: typed_ir::Name("flag".into()),
                    param_effect_annotation: None,
                    param_function_allowed_effects: None,
                    body: Box::new(Expr::typed(
                        ExprKind::If {
                            cond: Box::new(Expr::typed(
                                ExprKind::Var(path(&["flag"])),
                                RuntimeType::Core(bool_type()),
                            )),
                            then_branch: Box::new(Expr::typed(
                                ExprKind::Lit(typed_ir::Lit::Int("1".into())),
                                RuntimeType::Core(qualified_int_type()),
                            )),
                            else_branch: Box::new(Expr::typed(
                                ExprKind::Lit(typed_ir::Lit::Float("2.0".into())),
                                RuntimeType::Core(float_type()),
                            )),
                            evidence: Some(yulang_runtime_ir::JoinEvidence {
                                result: float_type(),
                            }),
                        },
                        RuntimeType::Unknown,
                    )),
                },
                RuntimeType::Unknown,
            ),
        }
    }

    fn choose_frac_binding() -> Binding {
        Binding {
            name: path(&["choose_frac"]),
            type_params: Vec::new(),
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: function_type(bool_type(), frac_type()),
            },
            body: Expr::typed(
                ExprKind::Lambda {
                    param: typed_ir::Name("flag".into()),
                    param_effect_annotation: None,
                    param_function_allowed_effects: None,
                    body: Box::new(Expr::typed(
                        ExprKind::If {
                            cond: Box::new(Expr::typed(
                                ExprKind::Var(path(&["flag"])),
                                RuntimeType::Core(bool_type()),
                            )),
                            then_branch: Box::new(Expr::typed(
                                ExprKind::Lit(typed_ir::Lit::Int("1".into())),
                                RuntimeType::Core(simple_int_type()),
                            )),
                            else_branch: Box::new(Expr::typed(
                                ExprKind::Var(path(&["existing_frac"])),
                                RuntimeType::Core(frac_type()),
                            )),
                            evidence: Some(yulang_runtime_ir::JoinEvidence {
                                result: frac_type(),
                            }),
                        },
                        RuntimeType::Unknown,
                    )),
                },
                RuntimeType::Unknown,
            ),
        }
    }

    fn some_int_binding() -> Binding {
        Binding {
            name: path(&["some_int"]),
            type_params: Vec::new(),
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: function_type(unit_type(), some_int_type()),
            },
            body: Expr::typed(
                ExprKind::Lambda {
                    param: typed_ir::Name("_unit".into()),
                    param_effect_annotation: None,
                    param_function_allowed_effects: None,
                    body: Box::new(Expr::typed(
                        ExprKind::Variant {
                            tag: typed_ir::Name("some".into()),
                            value: Some(Box::new(Expr::typed(
                                ExprKind::Lit(typed_ir::Lit::Int("1".into())),
                                RuntimeType::Core(int_type()),
                            ))),
                        },
                        RuntimeType::Unknown,
                    )),
                },
                RuntimeType::Unknown,
            ),
        }
    }

    fn force_io_binding() -> Binding {
        Binding {
            name: path(&["force_io"]),
            type_params: Vec::new(),
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: function_type(unit_type(), int_type()),
            },
            body: Expr::typed(
                ExprKind::Lambda {
                    param: typed_ir::Name("x".into()),
                    param_effect_annotation: None,
                    param_function_allowed_effects: None,
                    body: Box::new(Expr::typed(
                        ExprKind::BindHere {
                            expr: Box::new(Expr::typed(
                                ExprKind::Var(path(&["x"])),
                                RuntimeType::Thunk {
                                    effect: effect_row(&["io"]),
                                    value: Box::new(RuntimeType::Core(int_type())),
                                },
                            )),
                        },
                        RuntimeType::Unknown,
                    )),
                },
                RuntimeType::Unknown,
            ),
        }
    }

    fn handle_io_binding() -> Binding {
        Binding {
            name: path(&["handle_io"]),
            type_params: Vec::new(),
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: function_type(unit_type(), int_type()),
            },
            body: Expr::typed(
                ExprKind::Lambda {
                    param: typed_ir::Name("_unit".into()),
                    param_effect_annotation: None,
                    param_function_allowed_effects: None,
                    body: Box::new(Expr::typed(
                        ExprKind::Handle {
                            body: Box::new(Expr::typed(
                                ExprKind::Thunk {
                                    effect: effect_row(&["io", "log"]),
                                    value: RuntimeType::Core(int_type()),
                                    expr: Box::new(Expr::typed(
                                        ExprKind::Lit(typed_ir::Lit::Int("1".into())),
                                        RuntimeType::Core(int_type()),
                                    )),
                                },
                                RuntimeType::Unknown,
                            )),
                            arms: vec![yulang_runtime_ir::HandleArm {
                                effect: path(&["io"]),
                                payload: yulang_runtime_ir::Pattern::Wildcard {
                                    ty: RuntimeType::Core(unit_type()),
                                },
                                resume: None,
                                guard: None,
                                body: Expr::typed(
                                    ExprKind::Lit(typed_ir::Lit::Int("2".into())),
                                    RuntimeType::Core(int_type()),
                                ),
                            }],
                            evidence: yulang_runtime_ir::JoinEvidence { result: int_type() },
                            handler: yulang_runtime_ir::HandleEffect {
                                consumes: vec![path(&["io"])],
                                residual_before: None,
                                residual_after: None,
                            },
                        },
                        RuntimeType::Unknown,
                    )),
                },
                RuntimeType::Unknown,
            ),
        }
    }

    fn perform_io_binding() -> Binding {
        Binding {
            name: path(&["perform_io"]),
            type_params: Vec::new(),
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: function_type(unit_type(), int_type()),
            },
            body: Expr::typed(
                ExprKind::Lambda {
                    param: typed_ir::Name("x".into()),
                    param_effect_annotation: None,
                    param_function_allowed_effects: None,
                    body: Box::new(Expr::typed(
                        ExprKind::Apply {
                            callee: Box::new(Expr::typed(
                                ExprKind::EffectOp(path(&["io", "read"])),
                                RuntimeType::Fun {
                                    param: Box::new(RuntimeType::Core(unit_type())),
                                    ret: Box::new(RuntimeType::Thunk {
                                        effect: effect_row(&["io"]),
                                        value: Box::new(RuntimeType::Core(int_type())),
                                    }),
                                },
                            )),
                            arg: Box::new(Expr::typed(
                                ExprKind::Var(path(&["x"])),
                                RuntimeType::Core(unit_type()),
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

    fn bool_type() -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path(&["std", "bool", "Bool"]),
            args: Vec::new(),
        }
    }

    fn simple_int_type() -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path(&["int"]),
            args: Vec::new(),
        }
    }

    fn qualified_int_type() -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path(&["std", "int", "int"]),
            args: Vec::new(),
        }
    }

    fn float_type() -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path(&["std", "float", "float"]),
            args: Vec::new(),
        }
    }

    fn frac_type() -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path(&["std", "frac", "frac"]),
            args: Vec::new(),
        }
    }

    fn unit_type() -> typed_ir::Type {
        typed_ir::Type::Tuple(Vec::new())
    }

    fn some_int_type() -> typed_ir::Type {
        typed_ir::Type::Variant(typed_ir::VariantType {
            cases: vec![typed_ir::VariantCase {
                name: typed_ir::Name("some".into()),
                payloads: vec![int_type()],
            }],
            tail: None,
        })
    }

    fn effect_row(names: &[&str]) -> typed_ir::Type {
        crate::effect::effect_row_from_items(
            names
                .iter()
                .map(|name| typed_ir::Type::Named {
                    path: path(&[name]),
                    args: Vec::new(),
                })
                .collect(),
        )
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
