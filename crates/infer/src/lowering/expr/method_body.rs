//! Extracted expression lowering methods.

use super::super::*;
use super::*;

pub(in crate::lowering) struct ImplRequirementParameterPreparation {
    param_uppers: Vec<Option<NegId>>,
    body_cursor: Option<RequirementSpineCursor>,
    continuation: SignatureLoweringContinuation,
}

pub(in crate::lowering) struct LoweredImplMethodBody {
    pub(in crate::lowering) computation: Computation,
    pub(in crate::lowering) deferred_requirement: Option<DeferredRoleImplMethodRequirement>,
    #[cfg_attr(
        not(test),
        allow(
            dead_code,
            reason = "completed receiver descriptors remain inactive until Slice 4c"
        )
    )]
    pub(in crate::lowering) inactive_receiver_requirement:
        Option<DeferredRoleImplMethodRequirement>,
    #[cfg(test)]
    pub(in crate::lowering) receiver_parameter_context: Option<RequirementParameterContextStatus>,
    #[cfg_attr(
        not(test),
        allow(
            dead_code,
            reason = "receiver anchors are transported into the pending descriptor by Slice 4b"
        )
    )]
    pub(in crate::lowering) receiver_anchors: Option<ReceiverMethodLoweringAnchors>,
}

enum ReceiverRequirementPreparation {
    Immediate {
        plan: ImplRequirementMethodPlan,
        parameter_context: RequirementParameterContextStatus,
    },
    Inactive(DeferredRoleImplMethodRequirement),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::lowering) struct ReceiverMethodLoweringAnchors {
    pub(in crate::lowering) receiver: TypeVar,
    pub(in crate::lowering) tail_parameters: Vec<TypeVar>,
    pub(in crate::lowering) body_value: TypeVar,
    pub(in crate::lowering) body_effect: TypeVar,
    pub(in crate::lowering) method_value: TypeVar,
}

impl<'a> ExprLowerer<'a> {
    pub(in crate::lowering) fn lower_binding_body_with_args_with_self(
        &mut self,
        arg_patterns: &[Cst],
        body: &Cst,
        result_type_expr: Option<&Cst>,
        self_value: Option<TypeVar>,
    ) -> Result<Computation, LoweringError> {
        if arg_patterns.is_empty() {
            return self.lower_binding_body_expr(body);
        }
        let mut ann_builder = ann_type_builder_with_aliases(
            self.modules,
            self.module,
            self.site,
            self.self_alias.clone(),
            &self.type_var_aliases,
            &self.type_name_aliases,
        );
        let mut ann_solver_vars = FxHashMap::default();
        let mut ann_closed_effect_rows = FxHashMap::default();
        self.lower_lambda_params(
            arg_patterns,
            body,
            LambdaScope::Defined,
            &mut ann_builder,
            &mut ann_solver_vars,
            &mut ann_closed_effect_rows,
            result_type_expr,
            self_value,
        )
    }

    pub(in crate::lowering) fn lower_destructured_binding_component(
        &mut self,
        pattern: &Cst,
        hidden_def: DefId,
        name: Name,
    ) -> Result<Computation, LoweringError> {
        let pattern_value = self.fresh_type_var();
        let hidden = self.lower_resolved_value_ref("#destructure".to_string(), hidden_def);
        let pat = self.lower_match_pattern(pattern, pattern_value)?;
        self.subtype_var_to_var(hidden.value, pattern_value);
        self.subtype_var_to_var(pattern_value, hidden.value);
        let target = self.lower_name(name)?;
        Ok(self.prepend_block(
            LoweredLocalStmt {
                stmt: Stmt::Let(Vis::My, pat, hidden.expr),
                effect: hidden.effect,
            },
            target,
        ))
    }

    pub(in crate::lowering) fn lower_type_method_body_expr(
        &mut self,
        node: &Cst,
        arg_patterns: &[Cst],
        receiver: Name,
        receiver_kind: TypeMethodReceiver,
        owner: TypeDeclId,
        type_vars: &[String],
        result_type_expr: Option<Cst>,
        recursive_self_possible: bool,
    ) -> Result<Computation, LoweringError> {
        let mut ann_builder = ann_type_builder_with_aliases(
            self.modules,
            self.module,
            self.site,
            self.self_alias.clone(),
            &self.type_var_aliases,
            &self.type_name_aliases,
        );
        let self_ann = ann_builder.type_decl_application(owner, type_vars);
        let mut ann_solver_vars = FxHashMap::default();
        let mut ann_closed_effect_rows = FxHashMap::default();

        let receiver_value = self.fresh_type_var();
        self.connect_type_method_receiver(
            receiver_value,
            receiver_kind,
            &self_ann,
            &mut ann_solver_vars,
        )?;

        let before_locals = self.locals.len();
        let pat = self.bind_pattern_local(
            receiver,
            receiver_value,
            None,
            LocalCallReturnEffect::Annotated,
        );
        let arg_eff = self.never_neg();
        let has_tail_args = !arg_patterns.is_empty();
        let recursive_self = recursive_self_possible
            .then(|| self.receiver_recursive_self_skeleton(receiver_value, arg_eff, has_tail_args));
        self.function_frames
            .push(FunctionPredicateFrame::new(LambdaScope::Defined));
        let previous_recursive_self = if let Some(recursive_self) = recursive_self {
            self.recursive_self_value
                .replace(recursive_self.function_value)
        } else {
            self.recursive_self_value
        };
        let body_result = self.lower_defined_tail_after_receiver(
            arg_patterns,
            node,
            &mut ann_builder,
            &mut ann_solver_vars,
            &mut ann_closed_effect_rows,
            result_type_expr.as_ref(),
            recursive_self.map(|recursive_self| recursive_self.output_value),
            &[],
            None,
        );
        self.recursive_self_value = previous_recursive_self;
        let frame = self
            .function_frames
            .pop()
            .expect("method predicate frame should be balanced");
        self.locals.truncate(before_locals);
        let body = match recursive_self {
            Some(recursive_self) => self.attach_receiver_recursive_self_body(
                body_result?,
                recursive_self,
                has_tail_args,
            ),
            None => body_result?,
        };

        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let arg = self.alloc_neg(Neg::Var(receiver_value));
        let predicate_subtracts = self.lambda_predicate_subtracts(
            LambdaScope::Defined,
            PredicateOutputConstraints::default(),
            frame,
        );
        let (ret_eff, ret) = self.lambda_output_predicate(&body, &predicate_subtracts);
        self.constrain_lower(
            value,
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            },
        );

        let expr = self.session.poly.add_expr(Expr::Lambda(pat, body.expr));
        Ok(Computation::value(expr, value, effect))
    }

    pub(in crate::lowering) fn lower_act_method_body_expr(
        &mut self,
        node: &Cst,
        arg_patterns: &[Cst],
        receiver: Name,
        owner: TypeDeclId,
        result_type_expr: Option<Cst>,
        recursive_self_possible: bool,
    ) -> Result<Computation, LoweringError> {
        let mut ann_builder = ann_type_builder_with_aliases(
            self.modules,
            self.module,
            self.site,
            self.self_alias.clone(),
            &self.type_var_aliases,
            &self.type_name_aliases,
        );
        let mut ann_solver_vars = FxHashMap::default();
        let mut ann_closed_effect_rows = FxHashMap::default();

        let receiver_value = self.fresh_type_var();
        let receiver_effect = self.fresh_type_var();
        let receiver_subtract = self.connect_act_method_receiver_effect(receiver_effect, owner)?;
        let arg_eff = self.alloc_neg(Neg::Var(receiver_effect));
        let before_locals = self.locals.len();
        let pat = self.bind_pattern_local(
            receiver,
            receiver_value,
            Some(LocalEffect::Var(receiver_effect)),
            LocalCallReturnEffect::Annotated,
        );
        let has_tail_args = !arg_patterns.is_empty();
        let recursive_self = recursive_self_possible
            .then(|| self.receiver_recursive_self_skeleton(receiver_value, arg_eff, has_tail_args));
        self.function_frames
            .push(FunctionPredicateFrame::new(LambdaScope::Defined));
        let previous_recursive_self = if let Some(recursive_self) = recursive_self {
            self.recursive_self_value
                .replace(recursive_self.function_value)
        } else {
            self.recursive_self_value
        };
        let body_result = self.lower_defined_tail_after_receiver(
            arg_patterns,
            node,
            &mut ann_builder,
            &mut ann_solver_vars,
            &mut ann_closed_effect_rows,
            result_type_expr.as_ref(),
            recursive_self.map(|recursive_self| recursive_self.output_value),
            &[],
            None,
        );
        self.recursive_self_value = previous_recursive_self;
        let frame = self
            .function_frames
            .pop()
            .expect("method predicate frame should be balanced");
        self.locals.truncate(before_locals);
        let body = match recursive_self {
            Some(recursive_self) => self.attach_receiver_recursive_self_body(
                body_result?,
                recursive_self,
                has_tail_args,
            ),
            None => body_result?,
        };

        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let arg = self.alloc_neg(Neg::Var(receiver_value));
        let predicate_subtracts = self.lambda_predicate_subtracts(
            LambdaScope::Defined,
            PredicateOutputConstraints::from_subtracts(vec![StackWeight::pop(receiver_subtract)]),
            frame,
        );
        let (ret_eff, ret) = self.lambda_output_predicate(&body, &predicate_subtracts);
        self.constrain_lower(
            value,
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            },
        );

        let expr = self.session.poly.add_expr(Expr::Lambda(pat, body.expr));
        Ok(Computation::value(expr, value, effect))
    }

    pub(in crate::lowering) fn lower_role_method_body_expr(
        &mut self,
        node: &Cst,
        arg_patterns: &[Cst],
        receiver: Option<Name>,
        role_path: Vec<String>,
        role_inputs: &[String],
        role_associated: &[String],
        result_type_expr: Option<Cst>,
        recursive_self_possible: bool,
    ) -> Result<Computation, LoweringError> {
        let mut ann_builder = ann_type_builder_with_aliases(
            self.modules,
            self.module,
            self.site,
            self.self_alias.clone(),
            &self.type_var_aliases,
            &self.type_name_aliases,
        );
        for name in role_inputs.iter().chain(role_associated.iter()) {
            ann_builder.add_bare_type_var(name.clone());
        }
        if let Some(first) = role_inputs.first() {
            ann_builder.add_bare_type_var_alias("self", first.clone());
        }
        let role_arg_names = role_inputs
            .iter()
            .chain(role_associated.iter())
            .cloned()
            .collect::<Vec<_>>();
        let role_arg_anns = role_arg_names
            .iter()
            .map(|name| AnnType::Var(ann_builder.ann_type_var_for_role(name)))
            .collect::<Vec<_>>();

        let mut ann_solver_vars = FxHashMap::default();
        let mut ann_closed_effect_rows = FxHashMap::default();
        let receiver_value = self.fresh_type_var();
        self.connect_role_method_receiver_and_constraint(
            receiver.as_ref(),
            receiver_value,
            role_path,
            role_inputs,
            role_associated,
            &role_arg_anns,
            &mut ann_solver_vars,
        )?;

        let Some(receiver) = receiver else {
            return self.lower_lambda_params(
                arg_patterns,
                node,
                LambdaScope::Defined,
                &mut ann_builder,
                &mut ann_solver_vars,
                &mut ann_closed_effect_rows,
                result_type_expr.as_ref(),
                None,
            );
        };

        let before_locals = self.locals.len();
        let pat = self.bind_pattern_local(
            receiver,
            receiver_value,
            None,
            LocalCallReturnEffect::Annotated,
        );
        let arg_eff = self.never_neg();
        let has_tail_args = !arg_patterns.is_empty();
        let recursive_self = recursive_self_possible
            .then(|| self.receiver_recursive_self_skeleton(receiver_value, arg_eff, has_tail_args));
        self.function_frames
            .push(FunctionPredicateFrame::new(LambdaScope::Defined));
        let previous_recursive_self = if let Some(recursive_self) = recursive_self {
            self.recursive_self_value
                .replace(recursive_self.function_value)
        } else {
            self.recursive_self_value
        };
        let body_result = self.lower_defined_tail_after_receiver(
            arg_patterns,
            node,
            &mut ann_builder,
            &mut ann_solver_vars,
            &mut ann_closed_effect_rows,
            result_type_expr.as_ref(),
            recursive_self.map(|recursive_self| recursive_self.output_value),
            &[],
            None,
        );
        self.recursive_self_value = previous_recursive_self;
        let frame = self
            .function_frames
            .pop()
            .expect("role method predicate frame should be balanced");
        self.locals.truncate(before_locals);
        let body = match recursive_self {
            Some(recursive_self) => self.attach_receiver_recursive_self_body(
                body_result?,
                recursive_self,
                has_tail_args,
            ),
            None => body_result?,
        };

        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let arg = self.alloc_neg(Neg::Var(receiver_value));
        let predicate_subtracts = self.lambda_predicate_subtracts(
            LambdaScope::Defined,
            PredicateOutputConstraints::default(),
            frame,
        );
        let (ret_eff, ret) = self.lambda_output_predicate(&body, &predicate_subtracts);
        self.constrain_lower(
            value,
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            },
        );

        let expr = self.session.poly.add_expr(Expr::Lambda(pat, body.expr));
        Ok(Computation::value(expr, value, effect))
    }

    pub(in crate::lowering) fn lower_impl_method_body_expr(
        &mut self,
        node: &Cst,
        arg_patterns: &[Cst],
        receiver: Option<Name>,
        receiver_ann: &AnnType,
        result_type_expr: Option<Cst>,
        type_var_bindings: &[(String, AnnTypeVarId)],
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
        requirement: Option<&Arc<ResolvedRoleMethodRequirement>>,
        defer_receiverless_requirement: bool,
        prepare_inactive_receiver_requirement: bool,
        recursive_self_possible: bool,
    ) -> Result<LoweredImplMethodBody, LoweringError> {
        let mut ann_builder = ann_type_builder_with_aliases(
            self.modules,
            self.module,
            self.site,
            self.self_alias.clone(),
            &self.type_var_aliases,
            &self.type_name_aliases,
        );
        ann_builder.add_type_alias("self", receiver_ann.clone());
        ann_builder.seed_type_var_bindings(type_var_bindings);
        let mut ann_closed_effect_rows = FxHashMap::default();

        let Some(receiver) = receiver else {
            let body = self.lower_lambda_params(
                arg_patterns,
                node,
                LambdaScope::Defined,
                &mut ann_builder,
                ann_solver_vars,
                &mut ann_closed_effect_rows,
                result_type_expr.as_ref(),
                None,
            )?;
            let deferred_requirement = if let Some(requirement) = requirement {
                if defer_receiverless_requirement {
                    self.check_impl_method_requirement_shape(body.value, &requirement.signature)?;
                    self.check_impl_method_requirement_concrete_type(
                        body.value,
                        &requirement.signature,
                    )?;
                    Some(self.deferred_impl_method_requirement(
                        DeferredRequirementAnchor::Receiverless { value: body.value },
                        Arc::clone(requirement),
                        0,
                        false,
                        type_var_bindings,
                        ann_solver_vars,
                    )?)
                } else {
                    self.connect_impl_method_requirement(
                        body.value,
                        requirement,
                        type_var_bindings,
                        ann_solver_vars,
                        true,
                    )?;
                    None
                }
            } else {
                None
            };
            return Ok(LoweredImplMethodBody {
                computation: body,
                deferred_requirement,
                inactive_receiver_requirement: None,
                #[cfg(test)]
                receiver_parameter_context: None,
                receiver_anchors: None,
            });
        };

        let receiver_value = self.fresh_type_var();
        self.connect_type_method_value_annotation(receiver_value, receiver_ann, ann_solver_vars)?;
        let (requirement_plan, mut inactive_receiver_requirement, receiver_parameter_context) =
            match requirement {
                Some(requirement) if prepare_inactive_receiver_requirement => {
                    match self.prepare_receiver_requirement(
                        receiver_value,
                        Arc::clone(requirement),
                        arg_patterns.len(),
                        type_var_bindings,
                        ann_solver_vars,
                    )? {
                        ReceiverRequirementPreparation::Immediate {
                            plan,
                            parameter_context,
                        } => (plan, None, Some(parameter_context)),
                        ReceiverRequirementPreparation::Inactive(deferred) => {
                            let parameter_context = deferred.parameter_context.clone();
                            let plan = ImplRequirementMethodPlan {
                                param_uppers: deferred.parameter_uppers.clone(),
                                body: None,
                            };
                            (plan, Some(deferred), Some(parameter_context))
                        }
                    }
                }
                Some(requirement) => {
                    let parameters = self.prepare_impl_method_requirement_parameters(
                        &requirement.signature,
                        arg_patterns.len(),
                        true,
                        type_var_bindings,
                        ann_solver_vars,
                    )?;
                    (
                        self.resume_impl_method_requirement_body(
                            &requirement.signature,
                            parameters,
                        )?,
                        None,
                        None,
                    )
                }
                None => (
                    ImplRequirementMethodPlan {
                        param_uppers: Vec::new(),
                        body: None,
                    },
                    None,
                    None,
                ),
            };
        #[cfg(not(test))]
        let _ = &receiver_parameter_context;
        let before_locals = self.locals.len();
        let pat = self.bind_pattern_local(
            receiver,
            receiver_value,
            None,
            LocalCallReturnEffect::Annotated,
        );
        let arg_eff = self.never_neg();
        let has_tail_args = !arg_patterns.is_empty();
        let recursive_self = recursive_self_possible
            .then(|| self.receiver_recursive_self_skeleton(receiver_value, arg_eff, has_tail_args));
        self.function_frames
            .push(FunctionPredicateFrame::new(LambdaScope::Defined));
        let previous_recursive_self = if let Some(recursive_self) = recursive_self {
            self.recursive_self_value
                .replace(recursive_self.function_value)
        } else {
            self.recursive_self_value
        };
        let body_result = self.lower_defined_tail_after_receiver_with_anchors(
            arg_patterns,
            node,
            &mut ann_builder,
            ann_solver_vars,
            &mut ann_closed_effect_rows,
            result_type_expr.as_ref(),
            recursive_self.map(|recursive_self| recursive_self.output_value),
            &requirement_plan.param_uppers,
            requirement_plan.body,
        );
        self.recursive_self_value = previous_recursive_self;
        let frame = self
            .function_frames
            .pop()
            .expect("impl method predicate frame should be balanced");
        self.locals.truncate(before_locals);
        let lowered_tail = body_result?;
        let body = match recursive_self {
            Some(recursive_self) => self.attach_receiver_recursive_self_body(
                lowered_tail.computation,
                recursive_self,
                has_tail_args,
            ),
            None => lowered_tail.computation,
        };

        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let arg = self.alloc_neg(Neg::Var(receiver_value));
        let predicate_subtracts = self.lambda_predicate_subtracts(
            LambdaScope::Defined,
            PredicateOutputConstraints::default(),
            frame,
        );
        let (ret_eff, ret) = self.lambda_output_predicate(&body, &predicate_subtracts);
        self.constrain_lower(
            value,
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            },
        );
        let receiver_anchors = ReceiverMethodLoweringAnchors {
            receiver: receiver_value,
            tail_parameters: lowered_tail.parameter_values,
            body_value: lowered_tail.body.value,
            body_effect: lowered_tail.body.effect,
            method_value: value,
        };
        if let Some(deferred) = inactive_receiver_requirement.as_mut() {
            deferred.receiver_anchors = Some(receiver_anchors.clone());
            self.connect_inactive_receiver_requirement_immediately(deferred)?;
        } else if let Some(requirement) = requirement {
            self.connect_impl_method_requirement(
                value,
                requirement,
                type_var_bindings,
                ann_solver_vars,
                false,
            )?;
        }

        let expr = self.session.poly.add_expr(Expr::Lambda(pat, body.expr));
        Ok(LoweredImplMethodBody {
            computation: Computation::value(expr, value, effect),
            deferred_requirement: None,
            inactive_receiver_requirement,
            #[cfg(test)]
            receiver_parameter_context,
            receiver_anchors: Some(receiver_anchors),
        })
    }

    fn receiver_recursive_self_skeleton(
        &mut self,
        receiver_value: TypeVar,
        arg_eff: NegId,
        has_tail_args: bool,
    ) -> ReceiverRecursiveSelf {
        let function_value = self.fresh_type_var();
        let output_effect = if has_tail_args {
            self.fresh_exact_pure_effect()
        } else {
            self.fresh_type_var()
        };
        let output_value = self.fresh_type_var();
        let arg = self.alloc_neg(Neg::Var(receiver_value));
        let ret_eff = self.alloc_pos(Pos::Var(output_effect));
        let ret = self.alloc_pos(Pos::Var(output_value));
        self.constrain_lower(
            function_value,
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            },
        );
        ReceiverRecursiveSelf {
            function_value,
            output_effect,
            output_value,
        }
    }

    fn attach_receiver_recursive_self_body(
        &mut self,
        body: Computation,
        recursive_self: ReceiverRecursiveSelf,
        has_tail_args: bool,
    ) -> Computation {
        self.subtype_var_to_var(body.effect, recursive_self.output_effect);
        if has_tail_args {
            return body;
        }
        self.subtype_var_to_var(body.value, recursive_self.output_value);
        Computation::new(
            body.expr,
            recursive_self.output_value,
            recursive_self.output_effect,
            body.evaluation,
        )
    }

    /// Role requirement の関数 spine を一度だけ lower し、tail 引数の upper と
    /// 最終 body の upper を同じ signature 変数で作る。impl 値全体へ raw
    /// `value <: requirement` を張ると、body 内の stack evidence が receiver まで含む
    /// 関数境界を回って戻るので、requirement 由来の alias だけを body 近くで接続する。
    pub(in crate::lowering) fn deferred_impl_method_requirement(
        &mut self,
        anchor: DeferredRequirementAnchor,
        requirement: Arc<ResolvedRoleMethodRequirement>,
        param_count: usize,
        skip_receiver: bool,
        type_var_bindings: &[(String, AnnTypeVarId)],
        ann_solver_vars: &FxHashMap<AnnTypeVarId, TypeVar>,
    ) -> Result<DeferredRoleImplMethodRequirement, LoweringError> {
        let seed = signature_vars_from_ann_vars(type_var_bindings, ann_solver_vars);
        let level = self.session.infer.current_level();
        let final_metadata = DeferredRequirementMetadata {
            signature_vars: seed.clone(),
            new_var_level: level,
            connect_value_upper: matches!(anchor, DeferredRequirementAnchor::Receiverless { .. }),
        };
        let mut spine = &requirement.signature;
        let mut consumed_function_layers = 0usize;
        let mut parameter_signatures = Vec::with_capacity(param_count);
        let mut unavailable = None;

        if skip_receiver {
            if let Some(layer) = signature_function_layer(spine) {
                consumed_function_layers = consumed_function_layers.saturating_add(1);
                spine = layer.ret;
            } else {
                unavailable = Some(RequirementParameterContextUnavailable {
                    parameter_index: 0,
                    reason: RequirementParameterUnsupportedReason::MissingFunctionLayer,
                });
            }
        }

        for parameter_index in 0..param_count {
            let Some(layer) = signature_function_layer(spine) else {
                unavailable.get_or_insert(RequirementParameterContextUnavailable {
                    parameter_index,
                    reason: RequirementParameterUnsupportedReason::MissingFunctionLayer,
                });
                break;
            };
            parameter_signatures.push(layer.param);
            consumed_function_layers = consumed_function_layers.saturating_add(1);
            spine = layer.ret;
        }

        if unavailable.is_none() {
            unavailable =
                parameter_signatures
                    .iter()
                    .enumerate()
                    .find_map(|(parameter_index, signature)| {
                        unsupported_requirement_parameter(signature, self.modules).map(|reason| {
                            RequirementParameterContextUnavailable {
                                parameter_index,
                                reason,
                            }
                        })
                    });
        }

        let body_cursor = if skip_receiver || param_count > 0 {
            RequirementSpineCursor::FunctionResult {
                consumed_function_layers,
            }
        } else {
            RequirementSpineCursor::WholeValue
        };
        let (parameter_uppers, continuation, parameter_context) = if let Some(unavailable) =
            unavailable
        {
            let lowerer = SignatureLowerer::with_vars_at_level(
                &mut self.session.infer,
                self.modules,
                seed,
                level,
            );
            (
                vec![None; param_count],
                lowerer.into_continuation(),
                RequirementParameterContextStatus::Unsupported(unavailable),
            )
        } else {
            let before = self.requirement_bridge_audit_snapshot(type_var_bindings, ann_solver_vars);
            let mut lowerer = SignatureLowerer::with_vars_at_level(
                &mut self.session.infer,
                self.modules,
                seed,
                level,
            );
            let mut parameter_uppers = Vec::with_capacity(param_count);
            for signature in parameter_signatures {
                parameter_uppers.push(Some(
                    lowerer
                        .lower_neg(signature)
                        .map_err(|error| LoweringError::SignatureConstraint { error })?,
                ));
            }
            let continuation = lowerer.into_continuation();
            let parameter_context = self.requirement_parameter_context_since(
                NonMutatingRequirementClass::PlainValueParameters { count: param_count },
                before,
                type_var_bindings,
                ann_solver_vars,
            );
            (parameter_uppers, continuation, parameter_context)
        };

        Ok(DeferredRoleImplMethodRequirement {
            anchor,
            receiver_anchors: None,
            requirement,
            parameter_uppers,
            body_cursor,
            continuation,
            parameter_context,
            final_metadata,
        })
    }

    fn prepare_receiver_requirement(
        &mut self,
        receiver: TypeVar,
        requirement: Arc<ResolvedRoleMethodRequirement>,
        param_count: usize,
        type_var_bindings: &[(String, AnnTypeVarId)],
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
    ) -> Result<ReceiverRequirementPreparation, LoweringError> {
        let deferred = self.deferred_impl_method_requirement(
            DeferredRequirementAnchor::Receiver { receiver },
            requirement,
            param_count,
            true,
            type_var_bindings,
            ann_solver_vars,
        )?;
        self.finish_receiver_requirement_preparation(
            deferred,
            param_count,
            type_var_bindings,
            ann_solver_vars,
        )
    }

    fn finish_receiver_requirement_preparation(
        &mut self,
        deferred: DeferredRoleImplMethodRequirement,
        param_count: usize,
        type_var_bindings: &[(String, AnnTypeVarId)],
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
    ) -> Result<ReceiverRequirementPreparation, LoweringError> {
        match &deferred.parameter_context {
            RequirementParameterContextStatus::Clean(_) => {
                Ok(ReceiverRequirementPreparation::Inactive(deferred))
            }
            RequirementParameterContextStatus::MutatedBridge(_) => {
                let parameter_context = deferred.parameter_context.clone();
                let plan = self.resume_deferred_receiver_requirement(deferred)?;
                Ok(ReceiverRequirementPreparation::Immediate {
                    plan,
                    parameter_context,
                })
            }
            RequirementParameterContextStatus::Unsupported(_) => {
                let parameter_context = deferred.parameter_context.clone();
                let parameters = self.prepare_impl_method_requirement_parameters(
                    &deferred.requirement.signature,
                    param_count,
                    true,
                    type_var_bindings,
                    ann_solver_vars,
                )?;
                let plan = self.resume_impl_method_requirement_body(
                    &deferred.requirement.signature,
                    parameters,
                )?;
                Ok(ReceiverRequirementPreparation::Immediate {
                    plan,
                    parameter_context,
                })
            }
        }
    }

    #[cfg(test)]
    pub(in crate::lowering) fn force_mutated_receiver_requirement_fallback_for_slice4b(
        &mut self,
        mut deferred: DeferredRoleImplMethodRequirement,
        mutation: BridgeMutationAudit,
        param_count: usize,
        type_var_bindings: &[(String, AnnTypeVarId)],
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
    ) -> Result<ImplRequirementMethodPlan, LoweringError> {
        deferred.parameter_context = RequirementParameterContextStatus::MutatedBridge(mutation);
        match self.finish_receiver_requirement_preparation(
            deferred,
            param_count,
            type_var_bindings,
            ann_solver_vars,
        )? {
            ReceiverRequirementPreparation::Immediate { plan, .. } => Ok(plan),
            ReceiverRequirementPreparation::Inactive(_) => {
                unreachable!("forced MutatedBridge must take the immediate fallback")
            }
        }
    }

    fn resume_deferred_receiver_requirement(
        &mut self,
        deferred: DeferredRoleImplMethodRequirement,
    ) -> Result<ImplRequirementMethodPlan, LoweringError> {
        self.resume_impl_method_requirement_body(
            &deferred.requirement.signature,
            ImplRequirementParameterPreparation {
                param_uppers: deferred.parameter_uppers,
                body_cursor: Some(deferred.body_cursor),
                continuation: deferred.continuation,
            },
        )
    }

    fn connect_inactive_receiver_requirement_immediately(
        &mut self,
        deferred: &DeferredRoleImplMethodRequirement,
    ) -> Result<(), LoweringError> {
        // Slice 4b keeps the completed pre-body continuation inactive for inspection while this
        // clone restores the legacy edges exactly once. Slice 4c must consume the stored
        // continuation instead and remove this compatibility application; running both would
        // lower the deferred expected layer twice.
        debug_assert!(matches!(
            deferred.parameter_context,
            RequirementParameterContextStatus::Clean(_)
        ));
        let anchors = deferred
            .receiver_anchors
            .as_ref()
            .expect("completed receiver descriptor must retain every lowering anchor");
        let body = self.resume_impl_method_requirement_body(
            &deferred.requirement.signature,
            ImplRequirementParameterPreparation {
                param_uppers: deferred.parameter_uppers.clone(),
                body_cursor: Some(deferred.body_cursor),
                continuation: deferred.continuation.clone(),
            },
        )?;
        let Some(body) = body.body else {
            return Err(LoweringError::SignatureShapeMismatch {
                expected: SignatureShape::of(&deferred.requirement.signature),
            });
        };
        self.connect_impl_method_body_requirement_anchors(
            anchors.body_value,
            anchors.body_effect,
            body,
        );

        self.check_impl_method_requirement_shape(
            anchors.method_value,
            &deferred.requirement.signature,
        )?;
        self.check_impl_method_requirement_concrete_type(
            anchors.method_value,
            &deferred.requirement.signature,
        )?;
        self.connect_impl_method_requirement_from_continuation(
            anchors.method_value,
            &deferred.requirement,
            SignatureLoweringContinuation::with_vars_at_level(
                deferred.final_metadata.signature_vars.clone(),
                deferred.final_metadata.new_var_level,
            ),
            deferred.final_metadata.connect_value_upper,
        )
    }

    pub(in crate::lowering) fn requirement_bridge_audit_snapshot(
        &self,
        type_var_bindings: &[(String, AnnTypeVarId)],
        ann_solver_vars: &FxHashMap<AnnTypeVarId, TypeVar>,
    ) -> RequirementBridgeAuditSnapshot {
        let constraints = self.session.infer.constraints();
        let mut mapped = type_var_bindings
            .iter()
            .filter_map(|(_, annotation_var)| {
                ann_solver_vars
                    .get(annotation_var)
                    .copied()
                    .map(|solver_var| (*annotation_var, solver_var))
            })
            .collect::<Vec<_>>();
        mapped.sort_by_key(|(annotation_var, solver_var)| (annotation_var.0, solver_var.0));
        mapped.dedup();
        let entries = mapped
            .into_iter()
            .map(|(annotation_var, solver_var)| RequirementBridgeAuditEntry {
                annotation_var,
                solver_var,
                bounds: constraints.bounds().of(solver_var).cloned(),
                subtract_facts: constraints.subtracts().facts(solver_var).to_vec(),
            })
            .collect();
        RequirementBridgeAuditSnapshot {
            epoch: constraints.epoch(),
            entries,
        }
    }

    pub(in crate::lowering) fn requirement_parameter_context_since(
        &self,
        class: NonMutatingRequirementClass,
        before: RequirementBridgeAuditSnapshot,
        type_var_bindings: &[(String, AnnTypeVarId)],
        ann_solver_vars: &FxHashMap<AnnTypeVarId, TypeVar>,
    ) -> RequirementParameterContextStatus {
        let after = self.requirement_bridge_audit_snapshot(type_var_bindings, ann_solver_vars);
        requirement_parameter_context_after_clean_lowering(class, before, after)
    }

    #[cfg(test)]
    pub(in crate::lowering) fn impl_method_requirement_plan(
        &mut self,
        requirement: &SignatureType,
        param_count: usize,
        skip_receiver: bool,
        type_var_bindings: &[(String, AnnTypeVarId)],
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
    ) -> Result<ImplRequirementMethodPlan, LoweringError> {
        let parameters = self.prepare_impl_method_requirement_parameters(
            requirement,
            param_count,
            skip_receiver,
            type_var_bindings,
            ann_solver_vars,
        )?;
        self.resume_impl_method_requirement_body(requirement, parameters)
    }

    pub(in crate::lowering) fn prepare_impl_method_requirement_parameters(
        &mut self,
        requirement: &SignatureType,
        param_count: usize,
        skip_receiver: bool,
        type_var_bindings: &[(String, AnnTypeVarId)],
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
    ) -> Result<ImplRequirementParameterPreparation, LoweringError> {
        let seed = signature_vars_from_ann_vars(type_var_bindings, ann_solver_vars);
        // 足場の区間変数（`Bounds(int|v, v&int)` の v）が root level で生まれると
        // simplify の level 保護で永久に残るので、def の現在 level で lower する。
        let level = self.session.infer.current_level();
        let mut lowerer = SignatureLowerer::with_vars_at_level(
            &mut self.session.infer,
            self.modules,
            seed,
            level,
        );
        let mut spine = requirement;
        let mut consumed_function_layers = 0usize;
        let mut missing_layer = false;

        if skip_receiver {
            match signature_function_layer(spine) {
                Some(layer) => {
                    consumed_function_layers = consumed_function_layers.saturating_add(1);
                    spine = layer.ret;
                }
                None => {
                    missing_layer = true;
                }
            }
        }

        let mut uppers = Vec::with_capacity(param_count);
        for _ in 0..param_count {
            let Some(layer) = signature_function_layer(spine) else {
                uppers.push(None);
                missing_layer = true;
                continue;
            };
            uppers.push(Some(
                lowerer
                    .lower_neg(layer.param)
                    .map_err(|error| LoweringError::SignatureConstraint { error })?,
            ));
            consumed_function_layers = consumed_function_layers.saturating_add(1);
            spine = layer.ret;
        }

        let body_cursor = if missing_layer {
            None
        } else if skip_receiver || param_count > 0 {
            Some(RequirementSpineCursor::FunctionResult {
                consumed_function_layers,
            })
        } else {
            Some(RequirementSpineCursor::WholeValue)
        };

        Ok(ImplRequirementParameterPreparation {
            param_uppers: uppers,
            body_cursor,
            continuation: lowerer.into_continuation(),
        })
    }

    pub(in crate::lowering) fn resume_impl_method_requirement_body(
        &mut self,
        requirement: &SignatureType,
        parameters: ImplRequirementParameterPreparation,
    ) -> Result<ImplRequirementMethodPlan, LoweringError> {
        let ImplRequirementParameterPreparation {
            param_uppers,
            body_cursor,
            continuation,
        } = parameters;
        let body = match body_cursor {
            None => None,
            Some(RequirementSpineCursor::WholeValue) => {
                let mut lowerer = SignatureLowerer::from_continuation(
                    &mut self.session.infer,
                    self.modules,
                    continuation,
                );
                Some(lower_impl_requirement_value_connection(
                    &mut lowerer,
                    requirement,
                )?)
            }
            Some(RequirementSpineCursor::FunctionResult {
                consumed_function_layers,
            }) => {
                let Some((ret_eff, ret)) =
                    signature_function_result(requirement, consumed_function_layers)
                else {
                    return Ok(ImplRequirementMethodPlan {
                        param_uppers,
                        body: None,
                    });
                };
                let mut lowerer = SignatureLowerer::from_continuation(
                    &mut self.session.infer,
                    self.modules,
                    continuation,
                );
                Some(lower_impl_requirement_body_connection(
                    &mut lowerer,
                    ret_eff,
                    ret,
                )?)
            }
        };
        Ok(ImplRequirementMethodPlan { param_uppers, body })
    }

    #[cfg(test)]
    pub(in crate::lowering) fn uninterrupted_impl_method_requirement_plan_for_slice4a(
        &mut self,
        requirement: &SignatureType,
        param_count: usize,
        skip_receiver: bool,
        type_var_bindings: &[(String, AnnTypeVarId)],
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
    ) -> Result<ImplRequirementMethodPlan, LoweringError> {
        // Frozen pre-Slice-4a oracle: unlike production, this keeps one uninterrupted driver
        // across parameter and body expected-signature lowering. Raw node ids, bridge state, and
        // epochs are compared against the split production path by the lifecycle witness.
        let seed = signature_vars_from_ann_vars(type_var_bindings, ann_solver_vars);
        let level = self.session.infer.current_level();
        let mut lowerer = SignatureLowerer::with_vars_at_level(
            &mut self.session.infer,
            self.modules,
            seed,
            level,
        );
        let mut spine = requirement;
        let mut body_result = None;
        let mut missing_layer = false;

        if skip_receiver {
            match signature_function_layer(spine) {
                Some(layer) => {
                    body_result = Some((layer.ret_eff, layer.ret));
                    spine = layer.ret;
                }
                None => missing_layer = true,
            }
        }

        let mut param_uppers = Vec::with_capacity(param_count);
        for _ in 0..param_count {
            let Some(layer) = signature_function_layer(spine) else {
                param_uppers.push(None);
                missing_layer = true;
                continue;
            };
            param_uppers.push(Some(
                lowerer
                    .lower_neg(layer.param)
                    .map_err(|error| LoweringError::SignatureConstraint { error })?,
            ));
            body_result = Some((layer.ret_eff, layer.ret));
            spine = layer.ret;
        }

        let body = if missing_layer {
            None
        } else if let Some((ret_eff, ret)) = body_result {
            Some(lower_impl_requirement_body_connection(
                &mut lowerer,
                ret_eff,
                ret,
            )?)
        } else if !skip_receiver && param_count == 0 {
            Some(lower_impl_requirement_value_connection(
                &mut lowerer,
                requirement,
            )?)
        } else {
            None
        };
        Ok(ImplRequirementMethodPlan { param_uppers, body })
    }

    pub(in crate::lowering) fn connect_impl_method_body_requirement(
        &mut self,
        body: Computation,
        requirement: ImplRequirementBodyConnection,
    ) {
        self.connect_impl_method_body_requirement_anchors(body.value, body.effect, requirement);
    }

    fn connect_impl_method_body_requirement_anchors(
        &mut self,
        body_value: TypeVar,
        body_effect: TypeVar,
        requirement: ImplRequirementBodyConnection,
    ) {
        let effect_lower = self.alloc_pos(Pos::Var(body_effect));
        self.session
            .infer
            .subtype(effect_lower, requirement.effect_upper);
        let value_lower = self.alloc_pos(Pos::Var(body_value));
        self.session
            .infer
            .subtype(value_lower, requirement.value_upper);
    }

    pub(in crate::lowering) fn connect_impl_method_requirement(
        &mut self,
        value: TypeVar,
        requirement: &ResolvedRoleMethodRequirement,
        type_var_bindings: &[(String, AnnTypeVarId)],
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
        connect_value_upper: bool,
    ) -> Result<(), LoweringError> {
        let signature = &requirement.signature;
        self.check_impl_method_requirement_shape(value, signature)?;
        self.check_impl_method_requirement_concrete_type(value, signature)?;
        let seed = signature_vars_from_ann_vars(type_var_bindings, ann_solver_vars);
        let level = self.session.infer.current_level();
        self.connect_impl_method_requirement_from_continuation(
            value,
            requirement,
            SignatureLoweringContinuation::with_vars_at_level(seed, level),
            connect_value_upper,
        )
    }

    pub(in crate::lowering) fn connect_impl_method_requirement_from_continuation(
        &mut self,
        value: TypeVar,
        requirement: &ResolvedRoleMethodRequirement,
        continuation: SignatureLoweringContinuation,
        connect_value_upper: bool,
    ) -> Result<(), LoweringError> {
        let signature = &requirement.signature;
        let (upper, summary_lower, summary_root, summary_role) = {
            let mut lowerer = SignatureLowerer::from_continuation(
                &mut self.session.infer,
                self.modules,
                continuation,
            );
            let upper = if connect_value_upper {
                Some(
                    lowerer
                        .lower_neg(signature)
                        .map_err(|error| LoweringError::SignatureConstraint { error })?,
                )
            } else {
                None
            };
            let summary_root = lowerer.fresh_type_var();
            let summary_lower = lowerer
                .lower_pos(signature)
                .map_err(|error| LoweringError::SignatureConstraint { error })?;
            let summary_upper = lowerer.alloc_neg(Neg::Var(summary_root));
            lowerer.infer.subtype(summary_lower, summary_upper);
            let summary_role = lower_impl_requirement_role_constraint(&mut lowerer, requirement)?;
            (upper, summary_lower, summary_root, summary_role)
        };
        if let Some(upper) = upper {
            let lower = self.session.infer.alloc_pos(Pos::Var(value));
            self.session.infer.subtype(lower, upper);
        }
        let projection = CompactRoot {
            root: compact_pos_surface(self.session.infer.constraints().types(), summary_lower),
            rec_vars: Vec::new(),
        };
        self.session
            .register_role_impl_member_projection(self.parent, projection);
        self.register_impl_requirement_simplification(summary_root, summary_role);
        Ok(())
    }

    pub(in crate::lowering) fn register_impl_requirement_simplification(
        &mut self,
        root: TypeVar,
        role: RoleConstraint,
    ) {
        let compact = compact_type_var(self.session.infer.constraints(), root);
        let role_predicate = compact_role_constraint(self.session.infer.constraints(), &role);
        let generalized = generalize_prepared_compact_root_with_roles(
            self.session.infer.constraints(),
            TypeLevel::root(),
            compact,
            vec![role_predicate],
            &FxHashSet::default(),
        );
        self.session.register_role_impl_member_simplification(
            self.parent,
            CompactSimplification {
                substitutions: generalized.substitutions,
                sandwiches: generalized.sandwiches,
            },
        );
    }

    pub(in crate::lowering) fn check_impl_method_requirement_concrete_type(
        &self,
        value: TypeVar,
        requirement: &SignatureType,
    ) -> Result<(), LoweringError> {
        let compact = compact_type_var(self.session.infer.constraints(), value);
        if compact_type_matches_signature(&compact.root, requirement, self.modules) {
            return Ok(());
        }
        Err(LoweringError::SignatureTypeMismatch {
            expected: SignatureShape::of(requirement),
        })
    }

    pub(in crate::lowering) fn check_impl_method_requirement_shape(
        &self,
        value: TypeVar,
        requirement: &SignatureType,
    ) -> Result<(), LoweringError> {
        let mut visited = Vec::new();
        if self.var_has_signature_shape(value, requirement, &mut visited) {
            return Ok(());
        }
        Err(LoweringError::SignatureShapeMismatch {
            expected: SignatureShape::of(requirement),
        })
    }

    pub(in crate::lowering) fn var_has_signature_shape(
        &self,
        var: TypeVar,
        requirement: &SignatureType,
        visited: &mut Vec<TypeVar>,
    ) -> bool {
        if visited.contains(&var) {
            return true;
        }
        visited.push(var);
        let Some(bounds) = self.session.infer.constraints().bounds().of(var) else {
            return true;
        };
        let lowers = bounds.lowers();
        lowers.is_empty()
            || lowers
                .iter()
                .any(|bound| self.pos_has_signature_shape(bound.pos, requirement, visited))
    }

    pub(in crate::lowering) fn pos_has_signature_shape(
        &self,
        pos: PosId,
        requirement: &SignatureType,
        visited: &mut Vec<TypeVar>,
    ) -> bool {
        let required_shape = SignatureShape::of(requirement);
        match self.session.infer.constraints().types().pos(pos) {
            Pos::Bot => true,
            Pos::Var(var) => self.var_has_signature_shape(*var, requirement, visited),
            Pos::Con(_, _) => required_shape != SignatureShape::Function,
            Pos::Fun { ret, .. } => match requirement {
                SignatureType::Function { ret: expected, .. }
                    if SignatureShape::of(expected) == SignatureShape::Function =>
                {
                    self.pos_has_signature_shape(*ret, expected, visited)
                }
                SignatureType::Function { .. } | SignatureType::Var(_) => true,
                _ => false,
            },
            Pos::Record(_) => true,
            Pos::RecordTailSpread { .. } | Pos::RecordHeadSpread { .. } => true,
            Pos::PolyVariant(_) => required_shape != SignatureShape::Function,
            Pos::Tuple(items) => match requirement {
                SignatureType::Var(_) => true,
                _ => items.is_empty() && required_shape != SignatureShape::Function,
            },
            Pos::Row(_) => matches!(
                required_shape,
                SignatureShape::Any | SignatureShape::EffectRow
            ),
            Pos::NonSubtract(inner, _) => {
                self.pos_has_signature_shape(*inner, requirement, visited)
            }
            Pos::Stack { inner, .. } => self.pos_has_signature_shape(*inner, requirement, visited),
            Pos::Union(left, right) => {
                self.pos_has_signature_shape(*left, requirement, visited)
                    || self.pos_has_signature_shape(*right, requirement, visited)
            }
        }
    }

    pub(in crate::lowering) fn connect_role_method_receiver_and_constraint(
        &mut self,
        receiver: Option<&Name>,
        receiver_value: TypeVar,
        role_path: Vec<String>,
        role_inputs: &[String],
        role_associated: &[String],
        role_arg_anns: &[AnnType],
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
    ) -> Result<(), LoweringError> {
        let receiver_ann = receiver.and_then(|_| role_arg_anns.first());
        let vars = std::mem::take(ann_solver_vars);
        let mut lowerer =
            AnnConstraintLowerer::with_vars(&mut self.session.infer, self.modules, vars);
        if let Some(receiver_ann) = receiver_ann.as_ref() {
            lowerer
                .connect_value(receiver_value, receiver_ann)
                .map_err(|error| LoweringError::AnnotationConstraint { error })?;
        }
        let mut role_args = Vec::with_capacity(role_arg_anns.len());
        for ann in role_arg_anns {
            role_args.push(
                lowerer
                    .lower_role_arg(ann)
                    .map_err(|error| LoweringError::AnnotationConstraint { error })?,
            );
        }
        *ann_solver_vars = lowerer.into_vars();

        let inputs = role_args[..role_inputs.len()].to_vec();
        let associated = role_associated
            .iter()
            .cloned()
            .zip(role_args[role_inputs.len()..].iter().copied())
            .map(|(name, value)| RoleAssociatedConstraint { name, value })
            .collect();
        self.session.roles.insert(
            self.parent,
            RoleConstraint {
                role: role_path,
                inputs,
                associated,
            },
        );
        Ok(())
    }

    pub(in crate::lowering) fn connect_act_method_receiver_effect(
        &mut self,
        effect: TypeVar,
        owner: TypeDeclId,
    ) -> Result<SubtractId, LoweringError> {
        let owner =
            self.modules
                .type_decl_by_id(owner)
                .ok_or(LoweringError::AnnotationConstraint {
                    error: AnnConstraintError::MissingTypeDecl { id: owner },
                })?;
        let path = self
            .modules
            .type_decl_path(&owner)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect::<Vec<_>>();
        let subtract = self.session.infer.fresh_subtract_id();
        let inner = self.fresh_type_var();
        let subtractability = Subtractability::Set(path, Vec::new());
        self.session
            .infer
            .declared_subtract_fact(inner, subtract, subtractability.clone());
        let inner_pos = self.alloc_pos(Pos::Var(inner));
        let stacked = self.alloc_pos(Pos::Stack {
            inner: inner_pos,
            weight: StackWeight::push(subtract, subtractability),
        });
        let effect_upper = self.alloc_neg(Neg::Var(effect));
        self.session.infer.subtype(stacked, effect_upper);
        Ok(subtract)
    }

    pub(in crate::lowering) fn connect_type_method_receiver(
        &mut self,
        receiver_value: TypeVar,
        receiver_kind: TypeMethodReceiver,
        self_ann: &AnnType,
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
    ) -> Result<(), LoweringError> {
        match receiver_kind {
            TypeMethodReceiver::Value => {
                self.connect_type_method_value_annotation(receiver_value, self_ann, ann_solver_vars)
            }
            TypeMethodReceiver::Ref => {
                let payload = self.fresh_type_var();
                self.connect_type_method_value_annotation(payload, self_ann, ann_solver_vars)?;
                let effect = self.fresh_type_var();
                let effect_arg = self.invariant_var_arg(effect);
                let payload_arg = self.invariant_var_arg(payload);
                self.constrain_lower(
                    receiver_value,
                    Pos::Con(
                        crate::std_paths::control_var_ref_type(),
                        vec![effect_arg, payload_arg],
                    ),
                );
                self.constrain_upper(
                    receiver_value,
                    Neg::Con(
                        crate::std_paths::control_var_ref_type(),
                        vec![effect_arg, payload_arg],
                    ),
                );
                Ok(())
            }
        }
    }

    pub(in crate::lowering) fn connect_type_method_value_annotation(
        &mut self,
        value: TypeVar,
        ann: &AnnType,
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
    ) -> Result<(), LoweringError> {
        let vars = std::mem::take(ann_solver_vars);
        let mut lowerer =
            AnnConstraintLowerer::with_vars(&mut self.session.infer, self.modules, vars);
        let result = lowerer
            .connect_value(value, ann)
            .map(|_| ())
            .map_err(|error| LoweringError::AnnotationConstraint { error });
        *ann_solver_vars = lowerer.into_vars();
        result
    }

    pub(in crate::lowering) fn connect_type_method_result_annotation(
        &mut self,
        body: Computation,
        type_expr: &Cst,
        ann_builder: &mut AnnTypeBuilder,
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
        ann_closed_effect_rows: &mut FxHashMap<AnnClosedEffectRowKey, TypeVar>,
    ) -> Result<Computation, LoweringError> {
        let ann = ann_builder
            .build_type_expr(type_expr)
            .map_err(|error| LoweringError::annotation_build(error, type_expr))?;
        self.check_result_annotation_type(body.value, &ann)?;
        let body = self.apply_effect_annotation_upcasts(body, &ann);
        let vars = std::mem::take(ann_solver_vars);
        let closed_effect_rows = std::mem::take(ann_closed_effect_rows);
        let mut lowerer = AnnConstraintLowerer::with_vars_and_closed_effect_rows(
            &mut self.session.infer,
            self.modules,
            vars,
            closed_effect_rows,
        );
        let result = lowerer
            .connect_computation_detailed(
                AnnComputationTarget {
                    value: body.value,
                    effect: body.effect,
                },
                &ann,
            )
            .map_err(|error| LoweringError::AnnotationConstraint { error });
        let (vars, closed_effect_rows) = lowerer.into_vars_and_closed_effect_rows();
        *ann_solver_vars = vars;
        *ann_closed_effect_rows = closed_effect_rows;
        let connection = result?;
        self.constrain_effect_filters(body.effect, &connection.subtracts);
        self.extend_current_predicate_connection(connection);
        Ok(body)
    }

    pub(in crate::lowering) fn apply_effect_annotation_upcasts(
        &mut self,
        mut body: Computation,
        ann: &AnnType,
    ) -> Computation {
        let target_paths = self.annotation_effect_paths(ann);
        if target_paths.is_empty() {
            return body;
        }
        let mut applied = FxHashSet::default();
        let mut up_defs = Vec::new();
        for target in target_paths {
            for def in self.session.casts.effect_up_defs_for_target(&target) {
                if applied.insert(def) {
                    up_defs.push(def);
                }
            }
        }
        for def in up_defs {
            let public_value = body.value;
            let up = self.lower_resolved_value_ref("#effect-up".to_string(), def);
            let wrapped = self.make_app(up, body);
            self.subtype_var_to_var(public_value, wrapped.value);
            self.subtype_var_to_var(wrapped.value, public_value);
            body = Computation::new(
                wrapped.expr,
                public_value,
                wrapped.effect,
                wrapped.evaluation,
            );
        }
        body
    }

    fn annotation_effect_paths(&self, ann: &AnnType) -> Vec<Vec<String>> {
        let AnnType::Effectful { eff, .. } = ann else {
            return Vec::new();
        };
        let mut paths = eff
            .items
            .iter()
            .filter_map(|atom| self.annotation_effect_atom_path(atom))
            .collect::<Vec<_>>();
        paths.sort();
        paths.dedup();
        paths
    }

    fn annotation_effect_atom_path(&self, atom: &AnnEffectAtom) -> Option<Vec<String>> {
        match atom {
            AnnEffectAtom::Type(AnnType::Var(_) | AnnType::Wildcard(_))
            | AnnEffectAtom::Wildcard => None,
            AnnEffectAtom::Type(ty) => self.annotation_constructor_path(ty),
        }
    }

    fn annotation_constructor_path(&self, ann: &AnnType) -> Option<Vec<String>> {
        match ann {
            AnnType::Builtin(builtin) => Some(vec![builtin.surface_name().to_string()]),
            AnnType::Named(id) => self.modules.type_decl_by_id(*id).map(|decl| {
                self.modules
                    .type_decl_path(&decl)
                    .segments
                    .into_iter()
                    .map(|name| name.0)
                    .collect()
            }),
            AnnType::Apply { callee, .. } => self.annotation_constructor_path(callee),
            _ => None,
        }
    }

    fn check_result_annotation_type(
        &self,
        value: TypeVar,
        ann: &AnnType,
    ) -> Result<(), LoweringError> {
        let expected = signature_from_ann_type(ann);
        let actual = compact_type_var(self.session.infer.constraints(), value);
        if compact_type_matches_signature_shape(&actual.root, &expected, self.modules) {
            return Ok(());
        }
        Err(LoweringError::SignatureTypeMismatch {
            expected: SignatureShape::of(&expected),
        })
    }

    fn constrain_effect_filters(&mut self, effect: TypeVar, weights: &[StackWeight]) {
        for weight in weights {
            self.session
                .infer
                .constraints_mut()
                .constrain_type_var_lowers_by_filter(effect, weight.filter_set().clone());
        }
    }

    pub(in crate::lowering) fn invariant_var_arg(&mut self, var: TypeVar) -> poly::types::NeuId {
        let lower = self.alloc_pos(Pos::Var(var));
        let upper = self.alloc_neg(Neg::Var(var));
        self.session.infer.alloc_neu(Neu::Bounds(lower, upper))
    }

    pub(in crate::lowering) fn act_effect_type_var_names(&self, id: TypeDeclId) -> Vec<String> {
        if let Some(error) = self.modules.error_decl(id) {
            return error.type_vars.clone();
        }
        if let Some(type_vars) = self.modules.act_type_vars(id).map(|vars| vars.to_vec())
            && !type_vars.is_empty()
        {
            return type_vars;
        }
        let Some(copy) = self.modules.resolved_act_copy(id) else {
            return Vec::new();
        };
        let aliases = copy
            .type_var_aliases
            .iter()
            .cloned()
            .collect::<FxHashMap<_, _>>();
        self.modules
            .act_type_vars(copy.source)
            .map(|vars| vars.to_vec())
            .unwrap_or_default()
            .into_iter()
            .map(|source| aliases.get(&source).cloned().unwrap_or(source))
            .collect()
    }
}

#[derive(Clone, Copy)]
struct ReceiverRecursiveSelf {
    function_value: TypeVar,
    output_effect: TypeVar,
    output_value: TypeVar,
}

struct SignatureFunctionLayer<'a> {
    param: &'a SignatureType,
    ret_eff: Option<&'a SignatureEffectRow>,
    ret: &'a SignatureType,
}

fn signature_function_layer(signature: &SignatureType) -> Option<SignatureFunctionLayer<'_>> {
    match signature {
        SignatureType::Effectful { ret, .. } => signature_function_layer(ret),
        SignatureType::Function {
            param,
            ret_eff,
            ret,
            ..
        } => Some(SignatureFunctionLayer {
            param,
            ret_eff: ret_eff.as_ref(),
            ret,
        }),
        _ => None,
    }
}

fn signature_function_result(
    signature: &SignatureType,
    consumed_function_layers: usize,
) -> Option<(Option<&SignatureEffectRow>, &SignatureType)> {
    let mut spine = signature;
    let mut result = None;
    for _ in 0..consumed_function_layers {
        let layer = signature_function_layer(spine)?;
        result = Some((layer.ret_eff, layer.ret));
        spine = layer.ret;
    }
    result
}

fn lower_impl_requirement_body_connection(
    lowerer: &mut SignatureLowerer<'_>,
    ret_eff: Option<&SignatureEffectRow>,
    ret: &SignatureType,
) -> Result<ImplRequirementBodyConnection, LoweringError> {
    let (ret_eff, ret) = signature_result_effect(ret_eff, ret);
    Ok(ImplRequirementBodyConnection {
        effect_upper: lowerer
            .lower_ret_effect_neg(ret_eff)
            .map_err(|error| LoweringError::SignatureConstraint { error })?,
        value_upper: lowerer
            .lower_neg(ret)
            .map_err(|error| LoweringError::SignatureConstraint { error })?,
    })
}

fn lower_impl_requirement_value_connection(
    lowerer: &mut SignatureLowerer<'_>,
    signature: &SignatureType,
) -> Result<ImplRequirementBodyConnection, LoweringError> {
    lower_impl_requirement_body_connection(lowerer, None, signature)
}

fn signature_result_effect<'a>(
    ret_eff: Option<&'a SignatureEffectRow>,
    ret: &'a SignatureType,
) -> (Option<&'a SignatureEffectRow>, &'a SignatureType) {
    match (ret_eff, ret) {
        (None, SignatureType::Effectful { eff, ret }) => (Some(eff), ret),
        _ => (ret_eff, ret),
    }
}

fn unsupported_requirement_parameter(
    signature: &SignatureType,
    modules: &ModuleTable,
) -> Option<RequirementParameterUnsupportedReason> {
    match signature {
        SignatureType::Builtin(_) | SignatureType::Var(_) => None,
        SignatureType::Named(declaration) => modules
            .type_decl_by_id(*declaration)
            .filter(|decl| matches!(decl.kind, ModuleTypeKind::Act | ModuleTypeKind::Error))
            .map(|_| RequirementParameterUnsupportedReason::EffectFamily {
                declaration: *declaration,
            }),
        SignatureType::EffectRow(_) => Some(RequirementParameterUnsupportedReason::EffectRow),
        SignatureType::Effectful { .. } => {
            Some(RequirementParameterUnsupportedReason::EffectfulLayer)
        }
        SignatureType::Tuple(items) => items
            .iter()
            .find_map(|item| unsupported_requirement_parameter(item, modules)),
        SignatureType::Apply { callee, args } => unsupported_requirement_parameter(callee, modules)
            .or_else(|| {
                args.iter()
                    .find_map(|arg| unsupported_requirement_parameter(arg, modules))
            }),
        SignatureType::Function {
            param,
            arg_eff,
            ret_eff,
            ret,
        } => {
            if arg_eff.is_some() || ret_eff.is_some() {
                return Some(RequirementParameterUnsupportedReason::EffectRow);
            }
            unsupported_requirement_parameter(param, modules)
                .or_else(|| unsupported_requirement_parameter(ret, modules))
        }
    }
}

fn requirement_parameter_context_after_clean_lowering(
    class: NonMutatingRequirementClass,
    before: RequirementBridgeAuditSnapshot,
    after: RequirementBridgeAuditSnapshot,
) -> RequirementParameterContextStatus {
    let mut affected = Vec::new();
    for entry in &before.entries {
        let found = after.entries.iter().find(|candidate| {
            candidate.annotation_var == entry.annotation_var
                && candidate.solver_var == entry.solver_var
        });
        let (bounds_changed, subtract_facts_changed) = match found {
            Some(found) => (
                found.bounds != entry.bounds,
                found.subtract_facts != entry.subtract_facts,
            ),
            None => (true, true),
        };
        if bounds_changed || subtract_facts_changed {
            affected.push(ConformanceBinderMutation {
                annotation_var: entry.annotation_var,
                solver_var: entry.solver_var,
                bounds_changed,
                subtract_facts_changed,
            });
        }
    }
    for entry in &after.entries {
        let existed = before.entries.iter().any(|candidate| {
            candidate.annotation_var == entry.annotation_var
                && candidate.solver_var == entry.solver_var
        });
        if !existed {
            affected.push(ConformanceBinderMutation {
                annotation_var: entry.annotation_var,
                solver_var: entry.solver_var,
                bounds_changed: true,
                subtract_facts_changed: true,
            });
        }
    }
    affected.sort_by_key(|mutation| (mutation.annotation_var.0, mutation.solver_var.0));
    let unexplained_epoch_advance = before.epoch != after.epoch && affected.is_empty();
    if affected.is_empty() && !unexplained_epoch_advance {
        RequirementParameterContextStatus::Clean(class)
    } else {
        RequirementParameterContextStatus::MutatedBridge(BridgeMutationAudit {
            epoch_before: before.epoch,
            epoch_after: after.epoch,
            affected,
            unexplained_epoch_advance,
        })
    }
}
