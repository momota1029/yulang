//! Extracted expression lowering methods.

use super::super::*;
use super::*;
use crate::annotation::{AnnEffectAtom, AnnEffectRow};

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
        let mut ann_closed_effect_rows = FxHashMap::default();
        self.lower_lambda_params(
            patterns.as_slice(),
            &body,
            lambda_scope,
            &mut ann_builder,
            &mut ann_solver_vars,
            &mut ann_closed_effect_rows,
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
        let mut ann_closed_effect_rows = FxHashMap::default();
        self.lower_lambda_params_with_body_mode(
            parts.patterns.as_slice(),
            &parts.body,
            lambda_scope,
            &mut ann_builder,
            &mut ann_solver_vars,
            &mut ann_closed_effect_rows,
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
        let predicate_subtracts = self.lambda_predicate_subtracts(
            lambda_scope,
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
        ann_closed_effect_rows: &mut FxHashMap<AnnClosedEffectRowKey, TypeVar>,
        body_type_expr: Option<&Cst>,
        self_value: Option<TypeVar>,
    ) -> Result<Computation, LoweringError> {
        self.lower_lambda_params_with_body_mode(
            patterns,
            body,
            lambda_scope,
            ann_builder,
            ann_solver_vars,
            ann_closed_effect_rows,
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
        ann_closed_effect_rows: &mut FxHashMap<AnnClosedEffectRowKey, TypeVar>,
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
                ann_closed_effect_rows,
                body_type_expr,
                self_value,
                &[],
                None,
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
                    ann_closed_effect_rows,
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
            ann_closed_effect_rows,
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
        self.mark_lambda_param_call_predicate(before_locals, &annotation);
        self.mark_lambda_param_as_input(pat);
        self.mark_lambda_param_effect_contract(pat, &annotation);
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
            ann_closed_effect_rows,
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
            self.lambda_predicate_subtracts(lambda_scope, annotation.predicate, frame);
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
        ann_closed_effect_rows: &mut FxHashMap<AnnClosedEffectRowKey, TypeVar>,
        body_type_expr: Option<&Cst>,
        self_value: Option<TypeVar>,
        param_uppers: &[Option<NegId>],
        requirement_body: Option<ImplRequirementBodyConnection>,
    ) -> Result<Computation, LoweringError> {
        if !patterns.is_empty() {
            return self.lower_defined_lambda_params(
                patterns,
                body,
                ann_builder,
                ann_solver_vars,
                ann_closed_effect_rows,
                body_type_expr,
                self_value,
                param_uppers,
                requirement_body,
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
                    ann_closed_effect_rows,
                )?;
            }
            if let Some(requirement_body) = requirement_body {
                self.connect_impl_method_body_requirement(body, requirement_body);
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
        ann_closed_effect_rows: &mut FxHashMap<AnnClosedEffectRowKey, TypeVar>,
        body_type_expr: Option<&Cst>,
        self_value: Option<TypeVar>,
        param_uppers: &[Option<NegId>],
        requirement_body: Option<ImplRequirementBodyConnection>,
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
            let mut annotation = match self.connect_lambda_pattern_annotation(
                pattern,
                param_value,
                ann_builder,
                ann_solver_vars,
                ann_closed_effect_rows,
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
            if param_uppers
                .get(param_index)
                .and_then(|upper| *upper)
                .is_some()
            {
                annotation.call_return_effect = LocalCallReturnEffect::Annotated;
            }
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
            self.mark_lambda_param_effect_contract(pat, &annotation);
            self.mark_lambda_param_call_predicate(param_local_start, &annotation);
            let frame_index = self.function_frames.len();
            self.function_frames
                .push(FunctionPredicateFrame::new(LambdaScope::Defined));
            self.mark_lambda_param_call_predicate_frame(param_local_start, frame_index);
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
                // Recursive self calls use the internal skeleton shape. Output predicates are
                // attached by the final wrapper below, so feeding them back into the skeleton would
                // reapply the same boundary on every recursive self edge.
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
                    ann_closed_effect_rows,
                )?;
            }
            if let Some(requirement_body) = requirement_body {
                self.connect_impl_method_body_requirement(body, requirement_body);
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
            body = self.wrap_lambda_param(
                LambdaScope::Defined,
                param,
                frame,
                body,
                body_type_expr.is_some(),
            );
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
        let def = self.lambda_param_def(pat);
        if let Some(def) = def
            && let Some(use_site) = self.session.local_defs.get_mut(def)
        {
            use_site.role = LocalDefRole::Input;
        }
    }

    fn mark_lambda_param_effect_contract(
        &mut self,
        pat: PatId,
        annotation: &LambdaPatternAnnotation,
    ) {
        let Some(contract) = annotation.argument_effect_contract.as_ref() else {
            return;
        };
        if let Some(def) = self.lambda_param_def(pat) {
            self.session
                .poly
                .arg_effect_contracts
                .insert(def, contract.clone());
        }
    }

    fn lambda_param_def(&self, pat: PatId) -> Option<DefId> {
        match self.session.poly.pat(pat) {
            Pat::Var(def) | Pat::As(_, def) => Some(*def),
            _ => None,
        }
    }

    fn mark_lambda_param_call_predicate(
        &mut self,
        local_start: usize,
        annotation: &LambdaPatternAnnotation,
    ) {
        let predicate = &annotation.call_predicate;
        if predicate.is_empty() {
            return;
        }
        for local in &mut self.locals[local_start..] {
            local
                .call_predicate_subtracts
                .extend(predicate.subtracts.iter().cloned());
            local.call_public_upper = annotation.call_public_upper;
            local.call_erased_upper = annotation.call_erased_upper;
            local.call_projection_enabled = annotation.call_projection_enabled;
        }
    }

    fn mark_lambda_param_call_predicate_frame(&mut self, local_start: usize, frame_index: usize) {
        for local in &mut self.locals[local_start..] {
            if !local.call_predicate_subtracts.is_empty() {
                local.call_predicate_frame = Some(frame_index);
            }
        }
    }

    pub(in crate::lowering) fn wrap_lambda_param(
        &mut self,
        lambda_scope: LambdaScope,
        param: LoweredLambdaParam,
        frame: FunctionPredicateFrame,
        body: Computation,
        project_called_params_to_body_effect: bool,
    ) -> Computation {
        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let arg =
            self.lambda_param_public_arg(&param, body.effect, project_called_params_to_body_effect);
        let predicate_subtracts =
            self.lambda_predicate_subtracts(lambda_scope, param.annotation.predicate, frame);
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

    fn lambda_param_public_arg(
        &mut self,
        param: &LoweredLambdaParam,
        body_effect: TypeVar,
        project_to_body_effect: bool,
    ) -> NegId {
        let def = match self.session.poly.pat(param.pat) {
            Pat::Var(def) | Pat::As(_, def) => Some(*def),
            _ => None,
        };
        let local_call = def
            .and_then(|def| self.local_binding_by_def(def))
            .filter(|local| local.call_erased_used)
            .map(|local| {
                (
                    local.call_projection_enabled,
                    local.call_nested,
                    local.call_uppers.clone(),
                    local.call_public_upper,
                    local.call_erased_upper,
                )
            });
        if let Some((
            call_projection_enabled,
            call_nested,
            call_uppers,
            call_public_upper,
            call_erased_upper,
        )) = local_call
        {
            if let Some(public_upper) = call_public_upper {
                return self.callable_upper_with_observed_wildcards(
                    public_upper,
                    &call_uppers,
                    true,
                );
            }
            if project_to_body_effect && call_projection_enabled && call_nested {
                if !call_uppers.is_empty() {
                    let projected = self.fresh_type_var();
                    for upper in call_uppers {
                        let upper = self.call_upper_with_body_effect(upper, body_effect);
                        let lower = self.alloc_pos(Pos::Var(projected));
                        self.session.infer.subtype(lower, upper);
                    }
                    return self.alloc_neg(Neg::Var(projected));
                }
            }
            if let Some(erased_upper) = call_erased_upper {
                return self.callable_upper_with_observed_wildcards(
                    erased_upper,
                    &call_uppers,
                    true,
                );
            }
        }
        self.alloc_neg(Neg::Var(param.value))
    }

    fn callable_upper_with_observed_wildcards(
        &mut self,
        upper: NegId,
        call_uppers: &[NegId],
        replace_wildcard_ret: bool,
    ) -> NegId {
        let (mut arg, arg_eff, ret_eff, mut ret) =
            match self.session.infer.constraints().types().neg(upper) {
                Neg::Fun {
                    arg,
                    arg_eff,
                    ret_eff,
                    ret,
                } => (*arg, *arg_eff, *ret_eff, *ret),
                _ => return upper,
            };

        if matches!(self.session.infer.constraints().types().pos(arg), Pos::Bot) {
            let observed_arg = self.fresh_type_var();
            let mut found_observed_arg = false;
            for upper in call_uppers {
                let call_arg = match self.session.infer.constraints().types().neg(*upper) {
                    Neg::Fun { arg, .. } => *arg,
                    _ => continue,
                };
                self.subtype_pos_to_var(call_arg, observed_arg);
                found_observed_arg = true;
            }
            if found_observed_arg {
                arg = self.alloc_pos(Pos::Var(observed_arg));
            }
        }

        if replace_wildcard_ret
            && matches!(self.session.infer.constraints().types().neg(ret), Neg::Top)
        {
            let observed_ret = self.fresh_type_var();
            let mut found_observed_ret = false;
            for upper in call_uppers {
                let call_ret = match self.session.infer.constraints().types().neg(*upper) {
                    Neg::Fun { ret, .. } => *ret,
                    _ => continue,
                };
                let call_ret_var = match self.session.infer.constraints().types().neg(call_ret) {
                    Neg::Var(var) => Some(*var),
                    _ => None,
                };
                self.subtype(Pos::Var(observed_ret), call_ret);
                if let Some(call_ret_var) = call_ret_var {
                    self.subtype_var_to_var(call_ret_var, observed_ret);
                }
                found_observed_ret = true;
            }
            if found_observed_ret {
                ret = self.alloc_neg(Neg::Var(observed_ret));
            }
        }

        self.alloc_neg(Neg::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        })
    }

    fn call_upper_with_body_effect(&mut self, upper: NegId, body_effect: TypeVar) -> NegId {
        let (arg, arg_eff, ret) = match self.session.infer.constraints().types().neg(upper) {
            Neg::Fun {
                arg, arg_eff, ret, ..
            } => (*arg, *arg_eff, *ret),
            _ => return upper,
        };
        let ret_eff = self.alloc_neg(Neg::Var(body_effect));
        self.alloc_neg(Neg::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        })
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
                param.annotation.predicate.clone(),
                frame.clone(),
            );
            let key = DefinedSkeletonPredicateKey {
                output_effect: layer.output_effect,
                output_value: layer.output_value,
                current_effect,
                current_value,
                subtracts: predicate_subtracts.subtracts.clone(),
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
                let ret_eff = self.wrap_pos_with_subtracts(ret_eff, &predicate_subtracts.subtracts);
                let ret = self.wrap_pos_with_subtracts(ret, &predicate_subtracts.subtracts);
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
        ann_closed_effect_rows: &mut FxHashMap<AnnClosedEffectRowKey, TypeVar>,
    ) -> Result<LambdaPatternAnnotation, LoweringError> {
        let Some(type_expr) = pattern_type_expr(pattern) else {
            return Ok(LambdaPatternAnnotation {
                arg_eff: self.never_neg(),
                skeleton_arg_eff: self.never_neg(),
                local_effect: None,
                argument_effect_contract: None,
                predicate: PredicateOutputConstraints::default(),
                call_predicate: PredicateOutputConstraints::default(),
                call_public_upper: None,
                call_erased_upper: None,
                call_projection_enabled: false,
                call_return_effect: LocalCallReturnEffect::Unannotated,
            });
        };
        let ann = ann_builder
            .build_type_expr(&type_expr)
            .map_err(|error| LoweringError::annotation_build(error, &type_expr))?;
        let (effect, arg_eff) = self.lambda_param_effect_slot(&ann);
        let vars = std::mem::take(ann_solver_vars);
        let closed_effect_rows = std::mem::take(ann_closed_effect_rows);
        let mut lowerer = AnnConstraintLowerer::with_vars_and_closed_effect_rows(
            &mut self.session.infer,
            self.modules,
            vars,
            closed_effect_rows,
        );
        let connection = lowerer
            .connect_parameter_computation_detailed(AnnComputationTarget { value, effect }, &ann)
            .map_err(|error| LoweringError::AnnotationConstraint { error });
        let connection = connection?;
        let call_predicate = lambda_annotation_predicate_constraints(&ann, connection.clone());
        let predicate = lambda_parameter_output_predicate_constraints(&ann, call_predicate.clone());
        let call_public_upper =
            if call_predicate.is_empty() || !callable_annotation_has_closed_effect_head(&ann) {
                None
            } else {
                Some(
                    lowerer
                        .lower_public_callable_upper_with_evidence(&ann)
                        .map_err(|error| LoweringError::AnnotationConstraint { error })?,
                )
            };
        let call_erased_upper =
            if call_predicate.is_empty() || !callable_annotation_has_effect_head(&ann) {
                None
            } else {
                let erased = erase_callable_annotation_effect_heads(&ann);
                Some(
                    lowerer
                        .lower_value_upper(&erased)
                        .map_err(|error| LoweringError::AnnotationConstraint { error })?,
                )
            };
        let (vars, closed_effect_rows) = lowerer.into_vars_and_closed_effect_rows();
        *ann_solver_vars = vars;
        *ann_closed_effect_rows = closed_effect_rows;
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
        Ok(LambdaPatternAnnotation {
            arg_eff,
            skeleton_arg_eff,
            local_effect,
            argument_effect_contract: lambda_annotation_argument_effect_contract(
                self.modules,
                &ann,
            ),
            predicate,
            call_predicate,
            call_public_upper,
            call_erased_upper,
            call_projection_enabled: !callable_annotation_has_effect_wildcard(&ann),
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

fn lambda_annotation_argument_effect_contract(
    modules: &ModuleTable,
    ann: &AnnType,
) -> Option<poly::expr::ArgEffectContract> {
    if !matches!(ann, AnnType::Function { .. }) {
        return None;
    }
    let mut markers = Vec::new();
    collect_argument_contract_markers(modules, ann, 0, &mut markers);
    (!markers.is_empty()).then_some(poly::expr::ArgEffectContract { markers })
}

fn collect_argument_contract_markers(
    modules: &ModuleTable,
    ann: &AnnType,
    depth: u32,
    markers: &mut Vec<poly::expr::ArgEffectContractMarker>,
) {
    match ann {
        AnnType::Effectful { eff, ret } => {
            collect_effect_row_contract_markers(modules, eff, depth, markers);
            collect_argument_contract_markers(modules, ret, depth, markers);
        }
        AnnType::Function {
            param,
            arg_eff,
            ret_eff,
            ret,
        } => {
            let nested_depth = depth.saturating_add(1);
            if let Some(row) = arg_eff {
                collect_effect_row_contract_markers(modules, row, nested_depth, markers);
            }
            if let Some(row) = ret_eff {
                collect_effect_row_contract_markers(modules, row, nested_depth, markers);
            }
            collect_argument_contract_markers(modules, param, nested_depth, markers);
            collect_argument_contract_markers(modules, ret, nested_depth, markers);
        }
        AnnType::Tuple(items) => {
            for item in items {
                collect_argument_contract_markers(modules, item, depth, markers);
            }
        }
        AnnType::Apply { args, .. } => {
            for arg in args {
                collect_argument_contract_markers(modules, arg, depth, markers);
            }
        }
        AnnType::EffectRow(row) => {
            collect_effect_row_contract_markers(modules, row, depth, markers)
        }
        AnnType::Builtin(_) | AnnType::Named(_) | AnnType::Var(_) | AnnType::Wildcard(_) => {}
    }
}

fn collect_effect_row_contract_markers(
    modules: &ModuleTable,
    row: &AnnEffectRow,
    depth: u32,
    markers: &mut Vec<poly::expr::ArgEffectContractMarker>,
) {
    for item in &row.items {
        let AnnEffectAtom::Type(ann) = item else {
            continue;
        };
        let Some(path) = effect_contract_path(modules, ann) else {
            continue;
        };
        let marker = poly::expr::ArgEffectContractMarker {
            path,
            depth,
            resume: poly::expr::ContractResumePolicy::PreserveMatchingPath,
        };
        if !markers.contains(&marker) {
            markers.push(marker);
        }
    }
}

fn effect_contract_path(modules: &ModuleTable, ann: &AnnType) -> Option<Vec<String>> {
    match ann {
        AnnType::Builtin(builtin) => Some(vec![builtin.surface_name().to_string()]),
        AnnType::Named(id) => modules.type_decl_by_id(*id).map(|decl| {
            modules
                .type_decl_path(&decl)
                .segments
                .into_iter()
                .map(|name| name.0)
                .collect()
        }),
        AnnType::Apply { callee, .. } => effect_contract_path(modules, callee),
        AnnType::Var(_)
        | AnnType::Wildcard(_)
        | AnnType::EffectRow(_)
        | AnnType::Effectful { .. }
        | AnnType::Tuple(_)
        | AnnType::Function { .. } => None,
    }
}

fn callable_annotation_has_effect_head(ann: &AnnType) -> bool {
    match ann {
        AnnType::Effectful { eff, ret } => {
            !eff.items.is_empty() || callable_annotation_has_effect_head(ret)
        }
        AnnType::Function {
            param,
            arg_eff,
            ret_eff,
            ret,
        } => {
            callable_annotation_has_effect_head(param)
                || arg_eff.as_ref().is_some_and(|row| !row.items.is_empty())
                || ret_eff.as_ref().is_some_and(|row| !row.items.is_empty())
                || callable_annotation_has_effect_head(ret)
        }
        AnnType::Tuple(items) => items.iter().any(callable_annotation_has_effect_head),
        _ => false,
    }
}

fn callable_annotation_has_closed_effect_head(ann: &AnnType) -> bool {
    match ann {
        AnnType::Effectful { eff, ret } => {
            effect_row_is_closed_head(eff) || callable_annotation_has_closed_effect_head(ret)
        }
        AnnType::Function {
            param,
            arg_eff,
            ret_eff,
            ret,
        } => {
            callable_annotation_has_closed_effect_head(param)
                || arg_eff.as_ref().is_some_and(effect_row_is_closed_head)
                || ret_eff.as_ref().is_some_and(effect_row_is_closed_head)
                || callable_annotation_has_closed_effect_head(ret)
        }
        AnnType::Tuple(items) => items.iter().any(callable_annotation_has_closed_effect_head),
        _ => false,
    }
}

fn effect_row_is_closed_head(row: &AnnEffectRow) -> bool {
    row.tail.is_none()
        && !row.items.is_empty()
        && !row
            .items
            .iter()
            .any(|item| matches!(item, AnnEffectAtom::Wildcard))
}

fn callable_annotation_has_effect_wildcard(ann: &AnnType) -> bool {
    match ann {
        AnnType::Effectful { eff, ret } => {
            effect_row_has_wildcard(eff) || callable_annotation_has_effect_wildcard(ret)
        }
        AnnType::Function {
            param,
            arg_eff,
            ret_eff,
            ret,
        } => {
            callable_annotation_has_effect_wildcard(param)
                || arg_eff.as_ref().is_some_and(effect_row_has_wildcard)
                || ret_eff.as_ref().is_some_and(effect_row_has_wildcard)
                || callable_annotation_has_effect_wildcard(ret)
        }
        AnnType::Tuple(items) => items.iter().any(callable_annotation_has_effect_wildcard),
        _ => false,
    }
}

fn erase_callable_annotation_effect_heads(ann: &AnnType) -> AnnType {
    match ann {
        AnnType::Effectful { eff, ret } => AnnType::Effectful {
            eff: erase_effect_row_heads(eff),
            ret: Box::new(erase_callable_annotation_effect_heads(ret)),
        },
        AnnType::Function {
            param,
            arg_eff,
            ret_eff,
            ret,
        } => AnnType::Function {
            param: param.clone(),
            arg_eff: arg_eff.clone(),
            ret_eff: ret_eff.as_ref().map(erase_effect_row_heads),
            ret: Box::new(erase_callable_annotation_effect_heads(ret)),
        },
        AnnType::Tuple(items) => AnnType::Tuple(
            items
                .iter()
                .map(erase_callable_annotation_effect_heads)
                .collect(),
        ),
        other => other.clone(),
    }
}

fn erase_effect_row_heads(row: &AnnEffectRow) -> AnnEffectRow {
    if row
        .items
        .iter()
        .any(|item| matches!(item, AnnEffectAtom::Wildcard))
    {
        return row.clone();
    }
    AnnEffectRow {
        items: Vec::new(),
        tail: row.tail.clone(),
    }
}

fn lambda_parameter_output_predicate_constraints(
    ann: &AnnType,
    call_predicate: PredicateOutputConstraints,
) -> PredicateOutputConstraints {
    match ann {
        AnnType::Function { .. } => PredicateOutputConstraints::default(),
        _ => call_predicate,
    }
}

fn lambda_annotation_predicate_constraints(
    ann: &AnnType,
    connection: AnnComputationConnection,
) -> PredicateOutputConstraints {
    if matches!(ann, AnnType::Function { .. }) && callable_annotation_has_effect_wildcard(ann) {
        return PredicateOutputConstraints::default();
    }
    let AnnType::Effectful { eff, .. } = ann else {
        return PredicateOutputConstraints {
            subtracts: connection.subtracts,
        };
    };
    if effect_row_has_wildcard(eff) {
        return PredicateOutputConstraints {
            subtracts: connection.subtracts,
        };
    }

    let Some(effect_stack) = connection.effect_stack else {
        return PredicateOutputConstraints {
            subtracts: connection.subtracts,
        };
    };
    if effect_stack.subtracts.is_empty() {
        return PredicateOutputConstraints {
            subtracts: connection.subtracts,
        };
    }

    let effect_stack_ids = effect_stack
        .subtracts
        .into_iter()
        .collect::<FxHashSet<SubtractId>>();
    let subtracts = connection
        .subtracts
        .into_iter()
        .filter(|weight| {
            let mut has_effect_stack_id = false;
            let all_effect_stack_ids = weight.subtract_ids().all(|id| {
                has_effect_stack_id = true;
                effect_stack_ids.contains(&id)
            });
            !has_effect_stack_id || !all_effect_stack_ids
        })
        .collect();
    PredicateOutputConstraints { subtracts }
}
