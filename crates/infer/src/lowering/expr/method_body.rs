//! Extracted expression lowering methods.

use super::super::*;
use super::*;

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
        self.lower_lambda_params(
            arg_patterns,
            body,
            LambdaScope::Defined,
            &mut ann_builder,
            &mut ann_solver_vars,
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
        self.function_frames
            .push(FunctionPredicateFrame::new(LambdaScope::Defined));
        let body_result = self.lower_defined_tail_after_receiver(
            arg_patterns,
            node,
            &mut ann_builder,
            &mut ann_solver_vars,
            result_type_expr.as_ref(),
            &[],
        );
        let frame = self
            .function_frames
            .pop()
            .expect("method predicate frame should be balanced");
        self.locals.truncate(before_locals);
        let body = body_result?;

        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let arg = self.alloc_neg(Neg::Var(receiver_value));
        let arg_eff = self.never_neg();
        let predicate_subtracts =
            self.lambda_predicate_subtracts(LambdaScope::Defined, Vec::new(), frame);
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

        let receiver_value = self.fresh_type_var();
        let receiver_effect = self.fresh_type_var();
        let receiver_subtract = self.connect_act_method_receiver_effect(receiver_effect, owner)?;
        let before_locals = self.locals.len();
        let pat = self.bind_pattern_local(
            receiver,
            receiver_value,
            Some(LocalEffect::Var(receiver_effect)),
            LocalCallReturnEffect::Annotated,
        );
        self.function_frames
            .push(FunctionPredicateFrame::new(LambdaScope::Defined));
        let body_result = self.lower_defined_tail_after_receiver(
            arg_patterns,
            node,
            &mut ann_builder,
            &mut ann_solver_vars,
            result_type_expr.as_ref(),
            &[],
        );
        let frame = self
            .function_frames
            .pop()
            .expect("method predicate frame should be balanced");
        self.locals.truncate(before_locals);
        let body = body_result?;

        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let arg = self.alloc_neg(Neg::Var(receiver_value));
        let arg_eff = self.alloc_neg(Neg::Var(receiver_effect));
        let predicate_subtracts = self.lambda_predicate_subtracts(
            LambdaScope::Defined,
            vec![StackWeight::pop(receiver_subtract)],
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
        self.function_frames
            .push(FunctionPredicateFrame::new(LambdaScope::Defined));
        let body_result = self.lower_defined_tail_after_receiver(
            arg_patterns,
            node,
            &mut ann_builder,
            &mut ann_solver_vars,
            result_type_expr.as_ref(),
            &[],
        );
        let frame = self
            .function_frames
            .pop()
            .expect("role method predicate frame should be balanced");
        self.locals.truncate(before_locals);
        let body = body_result?;

        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let arg = self.alloc_neg(Neg::Var(receiver_value));
        let arg_eff = self.never_neg();
        let predicate_subtracts =
            self.lambda_predicate_subtracts(LambdaScope::Defined, Vec::new(), frame);
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
        requirement: Option<&ResolvedRoleMethodRequirement>,
    ) -> Result<Computation, LoweringError> {
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

        let Some(receiver) = receiver else {
            let body = self.lower_lambda_params(
                arg_patterns,
                node,
                LambdaScope::Defined,
                &mut ann_builder,
                ann_solver_vars,
                result_type_expr.as_ref(),
                None,
            )?;
            if let Some(requirement) = requirement {
                self.connect_impl_method_requirement(
                    body.value,
                    requirement,
                    type_var_bindings,
                    ann_solver_vars,
                )?;
            }
            return Ok(body);
        };

        let receiver_value = self.fresh_type_var();
        self.connect_type_method_value_annotation(receiver_value, receiver_ann, ann_solver_vars)?;
        let param_uppers = match requirement {
            Some(requirement) => self.impl_method_param_uppers(
                &requirement.signature,
                arg_patterns.len(),
                type_var_bindings,
                ann_solver_vars,
            )?,
            None => Vec::new(),
        };
        let before_locals = self.locals.len();
        let pat = self.bind_pattern_local(
            receiver,
            receiver_value,
            None,
            LocalCallReturnEffect::Annotated,
        );
        self.function_frames
            .push(FunctionPredicateFrame::new(LambdaScope::Defined));
        let body_result = self.lower_defined_tail_after_receiver(
            arg_patterns,
            node,
            &mut ann_builder,
            ann_solver_vars,
            result_type_expr.as_ref(),
            &param_uppers,
        );
        let frame = self
            .function_frames
            .pop()
            .expect("impl method predicate frame should be balanced");
        self.locals.truncate(before_locals);
        let body = body_result?;

        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let arg = self.alloc_neg(Neg::Var(receiver_value));
        let arg_eff = self.never_neg();
        let predicate_subtracts =
            self.lambda_predicate_subtracts(LambdaScope::Defined, Vec::new(), frame);
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
        if let Some(requirement) = requirement {
            self.connect_impl_method_requirement(
                value,
                requirement,
                type_var_bindings,
                ann_solver_vars,
            )?;
        }

        let expr = self.session.poly.add_expr(Expr::Lambda(pat, body.expr));
        Ok(Computation::value(expr, value, effect))
    }

    /// requirement（impl 入力を代入済みの role method シグネチャ）の引数列を、
    /// member の各 param の上界として引き上げる。`value <: requirement` だけだと
    /// 引数側には下界しか流れず、subject の釘付け（discharge / 共起併合の前提）が
    /// 引数経由の demand に届かない。先頭の Function は receiver なので飛ばす。
    pub(in crate::lowering) fn impl_method_param_uppers(
        &mut self,
        requirement: &SignatureType,
        param_count: usize,
        type_var_bindings: &[(String, AnnTypeVarId)],
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
    ) -> Result<Vec<Option<NegId>>, LoweringError> {
        let mut spine = signature_function_step(requirement).map(|(_, ret)| ret);
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
        let mut uppers = Vec::with_capacity(param_count);
        for _ in 0..param_count {
            let Some((param, ret)) = spine.and_then(signature_function_step) else {
                uppers.push(None);
                continue;
            };
            uppers.push(Some(
                lowerer
                    .lower_neg(param)
                    .map_err(|error| LoweringError::SignatureConstraint { error })?,
            ));
            spine = Some(ret);
        }
        Ok(uppers)
    }

    pub(in crate::lowering) fn connect_impl_method_requirement(
        &mut self,
        value: TypeVar,
        requirement: &ResolvedRoleMethodRequirement,
        type_var_bindings: &[(String, AnnTypeVarId)],
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
    ) -> Result<(), LoweringError> {
        let signature = &requirement.signature;
        self.check_impl_method_requirement_shape(value, signature)?;
        self.check_impl_method_requirement_concrete_type(value, signature)?;
        let seed = signature_vars_from_ann_vars(type_var_bindings, ann_solver_vars);
        let level = self.session.infer.current_level();
        let (upper, summary_lower, summary_root, summary_role) = {
            let mut lowerer = SignatureLowerer::with_vars_at_level(
                &mut self.session.infer,
                self.modules,
                seed,
                level,
            );
            let upper = lowerer
                .lower_neg(signature)
                .map_err(|error| LoweringError::SignatureConstraint { error })?;
            let summary_root = lowerer.fresh_type_var();
            let summary_lower = lowerer
                .lower_pos(signature)
                .map_err(|error| LoweringError::SignatureConstraint { error })?;
            let summary_upper = lowerer.alloc_neg(Neg::Var(summary_root));
            lowerer.infer.subtype(summary_lower, summary_upper);
            let summary_role = lower_impl_requirement_role_constraint(&mut lowerer, requirement)?;
            (upper, summary_lower, summary_root, summary_role)
        };
        let lower = self.session.infer.alloc_pos(Pos::Var(value));
        self.session.infer.subtype(lower, upper);
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
    ) -> Result<(), LoweringError> {
        let ann = ann_builder
            .build_type_expr(type_expr)
            .map_err(|error| LoweringError::AnnotationBuild { error })?;
        self.check_result_annotation_type(body.value, &ann)?;
        let vars = std::mem::take(ann_solver_vars);
        let result_effect = self
            .self_alias
            .is_some()
            .then(|| self.materialize_effect_var(body.effect));
        let mut lowerer =
            AnnConstraintLowerer::with_vars(&mut self.session.infer, self.modules, vars);
        let target = AnnComputationTarget {
            value: body.value,
            effect: body.effect,
        };
        let result = if self.self_alias.is_some() {
            lowerer.connect_result_computation_detailed(
                AnnComputationTarget {
                    value: body.value,
                    effect: result_effect.expect("method result effect should be materialized"),
                },
                &ann,
            )
        } else {
            lowerer.connect_computation_detailed(target, &ann)
        }
        .map_err(|error| LoweringError::AnnotationConstraint { error });
        *ann_solver_vars = lowerer.into_vars();
        let connection = result?;
        self.constrain_effect_filters(body.effect, &connection.subtracts);
        self.extend_current_predicate_subtracts(connection.subtracts);
        Ok(())
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
        if let Some(type_vars) = self.modules.act_template(id).map(crate::act_type_var_names)
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
            .act_template(copy.source)
            .map(crate::act_type_var_names)
            .unwrap_or_default()
            .into_iter()
            .map(|source| aliases.get(&source).cloned().unwrap_or(source))
            .collect()
    }
}
