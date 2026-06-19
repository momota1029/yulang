//! Extracted expression lowering methods.

use super::super::*;
use super::*;

impl<'a> ExprLowerer<'a> {
    pub(in crate::lowering) fn lower_lambda(
        &mut self,
        node: &Cst,
        lambda_scope: LambdaScope,
    ) -> Result<Computation, LoweringError> {
        let patterns = node
            .children()
            .filter(|child| child.kind() == SyntaxKind::Pattern)
            .collect::<Vec<_>>();
        let Some(body) = node
            .children()
            .filter(|child| {
                matches!(
                    child.kind(),
                    SyntaxKind::Expr | SyntaxKind::IndentBlock | SyntaxKind::BraceGroup
                )
            })
            .last()
        else {
            return Err(LoweringError::MissingLambdaBody);
        };
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
            patterns.as_slice(),
            &body,
            lambda_scope,
            &mut ann_builder,
            &mut ann_solver_vars,
            None,
            None,
        )
    }

    pub(in crate::lowering) fn lower_sub_lambda(
        &mut self,
        node: &Cst,
        lambda_scope: LambdaScope,
    ) -> Result<Computation, LoweringError> {
        let Some(parts) = crate::sub_lambda_syntax_parts(node) else {
            return Err(LoweringError::MissingLambdaBody);
        };
        let mut ann_builder = ann_type_builder_with_aliases(
            self.modules,
            self.module,
            self.site,
            self.self_alias.clone(),
            &self.type_var_aliases,
            &self.type_name_aliases,
        );
        let mut ann_solver_vars = FxHashMap::default();
        self.lower_lambda_params_with_body_mode(
            parts.patterns.as_slice(),
            &parts.body,
            lambda_scope,
            &mut ann_builder,
            &mut ann_solver_vars,
            None,
            None,
            &LambdaBodyMode::Sub { label: parts.label },
        )
    }

    pub(in crate::lowering) fn lower_recursive_lambda(
        &mut self,
        node: &Cst,
        lambda_scope: LambdaScope,
    ) -> Result<Computation, LoweringError> {
        let Some(label) = recursive_lambda_label_name(node) else {
            return self.lower_lambda(node, lambda_scope);
        };

        let boundary = self.local_generalize_boundary;
        let previous_level = self.session.infer.enter_child_level();
        let before_locals = self.locals.len();
        let result = (|| {
            let value = self.fresh_type_var();
            let (pat, def) = self.bind_let_local_with_def(
                label.clone(),
                value,
                LocalCallReturnEffect::Annotated,
                None,
            );
            let body = self.lower_lambda(node, lambda_scope)?;
            self.subtype_var_to_var(body.value, value);
            self.subtype_var_to_var(value, body.value);
            self.set_local_let_body(def, body.expr);
            self.generalize_local_binding(
                def,
                value,
                boundary,
                BindingFetch::from_evaluation(body.evaluation),
            );
            let tail = self.lower_name(label)?;
            Ok(self.prepend_block(
                LoweredLocalStmt {
                    stmt: Stmt::Let(Vis::My, pat, body.expr),
                    effect: body.effect,
                },
                tail,
            ))
        })();
        self.locals.truncate(before_locals);
        self.session.infer.restore_level(previous_level);
        result
    }

    pub(in crate::lowering) fn lower_method_lambda(
        &mut self,
        node: &Cst,
        lambda_scope: LambdaScope,
    ) -> Result<Computation, LoweringError> {
        let receiver_name = Name("#method-receiver".to_string());
        let receiver_value = self.fresh_type_var();
        let before_locals = self.locals.len();
        let pat = self.bind_pattern_local(
            receiver_name.clone(),
            receiver_value,
            None,
            LocalCallReturnEffect::Annotated,
        );
        let receiver = self
            .locals
            .last()
            .cloned()
            .expect("method lambda receiver should be the last local");

        self.function_frames
            .push(FunctionPredicateFrame::new(lambda_scope));
        let previous_level = self.session.infer.enter_child_level();
        let body_result = self.lower_method_lambda_body(node, receiver);
        self.session.infer.restore_level(previous_level);
        let frame = self
            .function_frames
            .pop()
            .expect("method lambda predicate frame should be balanced");
        self.locals.truncate(before_locals);
        let body = body_result?;

        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let arg = self.alloc_neg(Neg::Var(receiver_value));
        let arg_eff = self.never_neg();
        let predicate_subtracts = self.lambda_predicate_subtracts(lambda_scope, Vec::new(), frame);
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

    pub(in crate::lowering) fn lower_method_lambda_body(
        &mut self,
        node: &Cst,
        receiver: LocalBinding,
    ) -> Result<Computation, LoweringError> {
        let mut acc = self.lower_local_name(receiver.name.clone(), receiver, None);
        for child in node.children() {
            acc = self.lower_tail_node(acc, &child)?;
        }
        Ok(acc)
    }

    pub(in crate::lowering) fn lower_lambda_params(
        &mut self,
        patterns: &[Cst],
        body: &Cst,
        lambda_scope: LambdaScope,
        ann_builder: &mut AnnTypeBuilder,
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
        body_type_expr: Option<&Cst>,
        self_value: Option<TypeVar>,
    ) -> Result<Computation, LoweringError> {
        self.lower_lambda_params_with_body_mode(
            patterns,
            body,
            lambda_scope,
            ann_builder,
            ann_solver_vars,
            body_type_expr,
            self_value,
            &LambdaBodyMode::Expr,
        )
    }

    pub(in crate::lowering) fn lower_lambda_params_with_body_mode(
        &mut self,
        patterns: &[Cst],
        body: &Cst,
        lambda_scope: LambdaScope,
        ann_builder: &mut AnnTypeBuilder,
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
        body_type_expr: Option<&Cst>,
        self_value: Option<TypeVar>,
        body_mode: &LambdaBodyMode,
    ) -> Result<Computation, LoweringError> {
        if lambda_scope == LambdaScope::Defined && !patterns.is_empty() {
            return self.lower_defined_lambda_params(
                patterns,
                body,
                ann_builder,
                ann_solver_vars,
                body_type_expr,
                self_value,
                &[],
                body_mode,
            );
        }

        let Some((pattern, rest)) = patterns.split_first() else {
            let body = self.lower_lambda_body(body, body_mode)?;
            if let Some(type_expr) = body_type_expr {
                self.connect_type_method_result_annotation(
                    body,
                    type_expr,
                    ann_builder,
                    ann_solver_vars,
                )?;
            }
            return Ok(body);
        };

        let param_value = self.fresh_type_var();
        let annotation = self.connect_lambda_pattern_annotation(
            pattern,
            param_value,
            ann_builder,
            ann_solver_vars,
        )?;
        let var_bindings = self.prepare_var_pattern_bindings(pattern)?;
        let before_locals = self.locals.len();
        let pat = self.lower_lambda_pattern_with_var_bindings(
            pattern,
            param_value,
            annotation.local_effect.clone(),
            annotation.call_return_effect,
            &var_bindings,
        )?;
        self.mark_lambda_param_as_input(pat);
        let active_var_bindings = self.install_var_pattern_bindings(&var_bindings)?;
        self.function_frames
            .push(FunctionPredicateFrame::new(lambda_scope));
        let previous_level = self.session.infer.enter_child_level();
        let previous_local_generalize_boundary = self.local_generalize_boundary;
        self.local_generalize_boundary = previous_level;
        let body_result = self.lower_lambda_params_with_body_mode(
            rest,
            body,
            lambda_scope,
            ann_builder,
            ann_solver_vars,
            body_type_expr,
            None,
            body_mode,
        );
        self.local_generalize_boundary = previous_local_generalize_boundary;
        self.session.infer.restore_level(previous_level);
        let frame = self
            .function_frames
            .pop()
            .expect("lambda predicate frame should be balanced");
        let mut body = match body_result {
            Ok(body) => body,
            Err(error) => {
                self.locals.truncate(before_locals);
                return Err(error);
            }
        };
        body = match self.wrap_var_pattern_bindings(active_var_bindings, body) {
            Ok(body) => body,
            Err(error) => {
                self.locals.truncate(before_locals);
                return Err(error);
            }
        };
        self.locals.truncate(before_locals);

        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let arg = self.alloc_neg(Neg::Var(param_value));
        let arg_eff = annotation.arg_eff;
        let predicate_subtracts =
            self.lambda_predicate_subtracts(lambda_scope, annotation.subtracts, frame);
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

    pub(in crate::lowering) fn lower_defined_tail_after_receiver(
        &mut self,
        patterns: &[Cst],
        body: &Cst,
        ann_builder: &mut AnnTypeBuilder,
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
        body_type_expr: Option<&Cst>,
        param_uppers: &[Option<NegId>],
    ) -> Result<Computation, LoweringError> {
        if !patterns.is_empty() {
            return self.lower_defined_lambda_params(
                patterns,
                body,
                ann_builder,
                ann_solver_vars,
                body_type_expr,
                None,
                param_uppers,
                &LambdaBodyMode::Expr,
            );
        }

        let previous_level = self.session.infer.enter_child_level();
        let previous_local_generalize_boundary = self.local_generalize_boundary;
        self.local_generalize_boundary = previous_level;
        let body_result = (|| {
            let body = self.lower_lambda_body(body, &LambdaBodyMode::Expr)?;
            if let Some(type_expr) = body_type_expr {
                self.connect_type_method_result_annotation(
                    body,
                    type_expr,
                    ann_builder,
                    ann_solver_vars,
                )?;
            }
            Ok(body)
        })();
        self.local_generalize_boundary = previous_local_generalize_boundary;
        self.session.infer.restore_level(previous_level);
        body_result
    }

    pub(in crate::lowering) fn lower_defined_lambda_params(
        &mut self,
        patterns: &[Cst],
        body: &Cst,
        ann_builder: &mut AnnTypeBuilder,
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
        body_type_expr: Option<&Cst>,
        self_value: Option<TypeVar>,
        param_uppers: &[Option<NegId>],
        body_mode: &LambdaBodyMode,
    ) -> Result<Computation, LoweringError> {
        let before_locals = self.locals.len();
        let before_frames = self.function_frames.len();
        let before_active_skeletons = self.active_defined_skeletons.len();
        let mut params = Vec::with_capacity(patterns.len());
        let mut var_bindings = Vec::new();

        for (param_index, pattern) in patterns.iter().enumerate() {
            let param_value = self.fresh_type_var();
            if let Some(Some(upper)) = param_uppers.get(param_index) {
                let lower = self.alloc_pos(Pos::Var(param_value));
                self.session.infer.subtype(lower, *upper);
            }
            let annotation = match self.connect_lambda_pattern_annotation(
                pattern,
                param_value,
                ann_builder,
                ann_solver_vars,
            ) {
                Ok(annotation) => annotation,
                Err(error) => {
                    self.locals.truncate(before_locals);
                    self.function_frames.truncate(before_frames);
                    self.active_defined_skeletons
                        .truncate(before_active_skeletons);
                    return Err(error);
                }
            };
            let prepared_var_bindings = match self.prepare_var_pattern_bindings(pattern) {
                Ok(bindings) => bindings,
                Err(error) => {
                    self.locals.truncate(before_locals);
                    self.function_frames.truncate(before_frames);
                    self.active_defined_skeletons
                        .truncate(before_active_skeletons);
                    return Err(error);
                }
            };
            let param_local_start = self.locals.len();
            let pat = match self.lower_lambda_pattern_with_var_bindings(
                pattern,
                param_value,
                annotation.local_effect.clone(),
                annotation.call_return_effect,
                &prepared_var_bindings,
            ) {
                Ok(pat) => pat,
                Err(error) => {
                    self.locals.truncate(before_locals);
                    self.function_frames.truncate(before_frames);
                    self.active_defined_skeletons
                        .truncate(before_active_skeletons);
                    return Err(error);
                }
            };
            self.mark_lambda_param_as_input(pat);
            let frame_index = self.function_frames.len();
            self.function_frames
                .push(FunctionPredicateFrame::new(LambdaScope::Defined));
            self.mark_defined_unannotated_arg_call_frame(param_local_start, frame_index);
            params.push(LoweredLambdaParam {
                pat,
                value: param_value,
                annotation,
            });
            var_bindings.push(prepared_var_bindings);
        }

        let skeleton_slots = if self_value.is_some() {
            Some(self.fresh_defined_lambda_skeleton(params.len()))
        } else {
            None
        };
        if let (Some(target), Some(skeleton)) = (self_value, skeleton_slots.as_ref()) {
            let initial_frames = params
                .iter()
                .map(|_| FunctionPredicateFrame::new(LambdaScope::Defined))
                .collect::<Vec<_>>();
            self.constrain_defined_lambda_skeleton_shape(&params, target, skeleton);
            self.connect_defined_lambda_skeleton_predicates(
                &params,
                &initial_frames,
                skeleton,
                SkeletonPredicateMode::KnownBeforeBody,
            );
            self.active_defined_skeletons
                .push(ActiveDefinedLambdaSkeleton {
                    before_frames,
                    params: params.clone(),
                    skeleton: skeleton.clone(),
                });
        }

        let previous_level = self.session.infer.enter_child_level();
        let previous_local_generalize_boundary = self.local_generalize_boundary;
        self.local_generalize_boundary = previous_level;
        let body_result = (|| {
            let active_var_bindings = var_bindings
                .iter()
                .map(|bindings| self.install_var_pattern_bindings(bindings))
                .collect::<Result<Vec<_>, _>>()?;
            let mut body = self.lower_lambda_body(body, body_mode)?;
            for active in active_var_bindings.into_iter().rev() {
                body = self.wrap_var_pattern_bindings(active, body)?;
            }
            if let (Some(_target), Some(skeleton)) = (self_value, skeleton_slots.as_ref()) {
                // body lowering 中に見つかった unannotated callee subtract は、発見時点で
                // active skeleton の output slot へ反映する。shape は stable な slot を返す
                // だけなので、最終段では body と skeleton slot の接続だけを張る。
                let skeleton_frames = self.function_frames[before_frames..].to_vec();
                self.connect_defined_lambda_skeleton_predicates(
                    &params,
                    &skeleton_frames,
                    skeleton,
                    SkeletonPredicateMode::All,
                );
                self.subtype_var_to_var(body.effect, skeleton.body_effect);
                self.subtype_var_to_var(body.value, skeleton.body_value);
                body = Computation::new(
                    body.expr,
                    skeleton.body_value,
                    skeleton.body_effect,
                    body.evaluation,
                );
            }
            if let Some(type_expr) = body_type_expr {
                self.connect_type_method_result_annotation(
                    body,
                    type_expr,
                    ann_builder,
                    ann_solver_vars,
                )?;
            }
            Ok(body)
        })();
        self.local_generalize_boundary = previous_local_generalize_boundary;
        self.session.infer.restore_level(previous_level);
        self.active_defined_skeletons
            .truncate(before_active_skeletons);

        let mut body = match body_result {
            Ok(body) => body,
            Err(error) => {
                self.locals.truncate(before_locals);
                self.function_frames.truncate(before_frames);
                self.active_defined_skeletons
                    .truncate(before_active_skeletons);
                return Err(error);
            }
        };

        for param in params.into_iter().rev() {
            let frame = self
                .function_frames
                .pop()
                .expect("lambda predicate frame should be balanced");
            body = self.wrap_lambda_param(LambdaScope::Defined, param, frame, body);
        }
        self.locals.truncate(before_locals);
        Ok(body)
    }

    pub(in crate::lowering) fn lower_lambda_body(
        &mut self,
        body: &Cst,
        mode: &LambdaBodyMode,
    ) -> Result<Computation, LoweringError> {
        match mode {
            LambdaBodyMode::Expr => self.lower_expr(body),
            LambdaBodyMode::Sub { label } => match label {
                Some(label) => self.lower_labeled_sub_syntax(label.clone(), body.clone()),
                None => self.lower_unlabeled_sub_syntax(body.clone()),
            },
        }
    }

    fn mark_lambda_param_as_input(&mut self, pat: PatId) {
        let def = match self.session.poly.pat(pat) {
            Pat::Var(def) | Pat::As(_, def) => Some(*def),
            _ => None,
        };
        if let Some(def) = def
            && let Some(use_site) = self.session.local_defs.get_mut(def)
        {
            use_site.role = LocalDefRole::Input;
        }
    }

    pub(in crate::lowering) fn wrap_lambda_param(
        &mut self,
        lambda_scope: LambdaScope,
        param: LoweredLambdaParam,
        frame: FunctionPredicateFrame,
        body: Computation,
    ) -> Computation {
        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let arg = self.alloc_neg(Neg::Var(param.value));
        let predicate_subtracts =
            self.lambda_predicate_subtracts(lambda_scope, param.annotation.subtracts, frame);
        let (ret_eff, ret) = self.lambda_output_predicate(&body, &predicate_subtracts);
        self.constrain_lower(
            value,
            Pos::Fun {
                arg,
                arg_eff: param.annotation.arg_eff,
                ret_eff,
                ret,
            },
        );

        let expr = self
            .session
            .poly
            .add_expr(Expr::Lambda(param.pat, body.expr));
        Computation::value(expr, value, effect)
    }

    pub(in crate::lowering) fn fresh_defined_lambda_skeleton(
        &mut self,
        params_len: usize,
    ) -> DefinedLambdaSkeleton {
        let layers = (0..params_len)
            .map(|_| DefinedLambdaSkeletonLayer {
                function_effect: self.fresh_exact_pure_effect(),
                function_value: self.fresh_type_var(),
                output_effect: self.fresh_type_var(),
                output_value: self.fresh_type_var(),
            })
            .collect();
        DefinedLambdaSkeleton {
            body_effect: self.fresh_type_var(),
            body_value: self.fresh_type_var(),
            layers,
        }
    }

    pub(in crate::lowering) fn constrain_defined_lambda_skeleton_shape(
        &mut self,
        params: &[LoweredLambdaParam],
        target: TypeVar,
        skeleton: &DefinedLambdaSkeleton,
    ) {
        debug_assert_eq!(params.len(), skeleton.layers.len());
        let mut current_value = None;

        for (param, layer) in params.iter().zip(skeleton.layers.iter()).rev() {
            let arg = self.alloc_neg(Neg::Var(param.value));
            let ret_eff = self.alloc_pos(Pos::Var(layer.output_effect));
            let ret = self.alloc_pos(Pos::Var(layer.output_value));
            self.constrain_lower(
                layer.function_value,
                Pos::Fun {
                    arg,
                    arg_eff: param.annotation.skeleton_arg_eff,
                    ret_eff,
                    ret,
                },
            );
            current_value = Some(layer.function_value);
        }

        if let Some(value) = current_value {
            self.subtype_var_to_var(value, target);
        }
    }

    pub(in crate::lowering) fn connect_defined_lambda_skeleton_predicates(
        &mut self,
        params: &[LoweredLambdaParam],
        frames: &[FunctionPredicateFrame],
        skeleton: &DefinedLambdaSkeleton,
        mode: SkeletonPredicateMode,
    ) {
        debug_assert_eq!(params.len(), frames.len());
        debug_assert_eq!(params.len(), skeleton.layers.len());
        let mut current_effect = skeleton.body_effect;
        let mut current_value = skeleton.body_value;

        for ((param, frame), layer) in params
            .iter()
            .zip(frames.iter())
            .zip(skeleton.layers.iter())
            .rev()
        {
            let predicate_subtracts = self.lambda_predicate_subtracts(
                LambdaScope::Defined,
                param.annotation.subtracts.clone(),
                frame.clone(),
            );
            let key = DefinedSkeletonPredicateKey {
                output_effect: layer.output_effect,
                output_value: layer.output_value,
                current_effect,
                current_value,
                subtracts: predicate_subtracts.clone(),
            };
            if predicate_subtracts.is_empty() {
                if mode.connects_empty_predicate(param) {
                    if !self.connected_defined_skeleton_predicates.insert(key) {
                        current_effect = layer.function_effect;
                        current_value = layer.function_value;
                        continue;
                    }
                    self.subtype_var_to_var(current_effect, layer.output_effect);
                    self.subtype_var_to_var(current_value, layer.output_value);
                    self.subtype_var_to_var(layer.output_value, current_value);
                }
            } else {
                if !self.connected_defined_skeleton_predicates.insert(key) {
                    current_effect = layer.function_effect;
                    current_value = layer.function_value;
                    continue;
                }
                let ret_eff = self.alloc_pos(Pos::Var(current_effect));
                let ret = self.alloc_pos(Pos::Var(current_value));
                let ret_eff = self.wrap_pos_with_subtracts(ret_eff, &predicate_subtracts);
                let ret = self.wrap_pos_with_subtracts(ret, &predicate_subtracts);
                self.subtype_pos_to_var(ret_eff, layer.output_effect);
                self.subtype_pos_to_var(ret, layer.output_value);
            }
            current_effect = layer.function_effect;
            current_value = layer.function_value;
        }
    }

    pub(in crate::lowering) fn connect_lambda_pattern_annotation(
        &mut self,
        pattern: &Cst,
        value: TypeVar,
        ann_builder: &mut AnnTypeBuilder,
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
    ) -> Result<LambdaPatternAnnotation, LoweringError> {
        let Some(type_expr) = pattern_type_expr(pattern) else {
            return Ok(LambdaPatternAnnotation {
                arg_eff: self.never_neg(),
                skeleton_arg_eff: self.never_neg(),
                local_effect: None,
                subtracts: Vec::new(),
                call_return_effect: LocalCallReturnEffect::Unannotated,
            });
        };
        let ann = ann_builder
            .build_type_expr(&type_expr)
            .map_err(|error| LoweringError::AnnotationBuild { error })?;
        let (effect, arg_eff) = self.lambda_param_effect_slot(&ann);
        let vars = std::mem::take(ann_solver_vars);
        let mut lowerer =
            AnnConstraintLowerer::with_vars(&mut self.session.infer, self.modules, vars);
        let connection = lowerer
            .connect_parameter_computation_detailed(AnnComputationTarget { value, effect }, &ann)
            .map_err(|error| LoweringError::AnnotationConstraint { error });
        *ann_solver_vars = lowerer.into_vars();
        let connection = connection?;
        let arg_eff = match connection.effect_stack {
            Some(ref effect_stack) => effect_stack.arg_eff,
            None => arg_eff,
        };
        let skeleton_arg_eff = match connection.effect_stack {
            Some(ref effect_stack) => effect_stack.arg_eff,
            None => arg_eff,
        };
        let local_effect = connection
            .effect_stack
            .clone()
            .map(|effect_stack| LocalEffect::Stack {
                effect,
                inner: effect_stack.inner,
                weight: effect_stack.weight,
            })
            .or_else(|| {
                matches!(ann, AnnType::Effectful { .. }).then_some(LocalEffect::Var(effect))
            });
        let subtracts = if matches!(&ann, AnnType::Effectful { eff, .. } if effect_row_has_wildcard(eff))
        {
            connection.subtracts
        } else {
            Vec::new()
        };
        Ok(LambdaPatternAnnotation {
            arg_eff,
            skeleton_arg_eff,
            local_effect,
            subtracts,
            call_return_effect: LocalCallReturnEffect::Annotated,
        })
    }

    pub(in crate::lowering) fn lambda_param_effect_slot(
        &mut self,
        ann: &AnnType,
    ) -> (TypeVar, NegId) {
        if matches!(ann, AnnType::Effectful { .. }) {
            let effect = self.fresh_type_var();
            return (effect, self.alloc_neg(Neg::Var(effect)));
        }

        (self.fresh_exact_pure_effect(), self.never_neg())
    }
}
