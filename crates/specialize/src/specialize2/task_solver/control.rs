use super::*;

impl<'a> TaskSolver<'a> {
    pub(super) fn case_type(
        &mut self,
        expr: poly_expr::ExprId,
        scrutinee: poly_expr::ExprId,
        arms: &[poly_expr::CaseArm],
    ) -> Result<Type, SpecializeError> {
        let scrutinee_ty = self.expr(scrutinee)?;
        let (scrutinee_value, scrutinee_effect) = split_runtime_computation_shape(scrutinee_ty);
        let result = self.graph.fresh_value();
        let mut effects = vec![scrutinee_effect];
        for arm in arms {
            self.bind_pat(arm.pat, scrutinee_value.clone())?;
            if let Some(guard) = arm.guard {
                effects.push(self.consume_expr_value(guard, bool_type())?.1);
            }
            let (_, body_effect) = self.consume_expr_value(arm.body, result.clone())?;
            effects.push(body_effect);
        }
        let effect = self.join_effects(effects)?;
        let result = self.runtime_shape(effect, result)?;
        if matches!(result, Type::Thunk { .. }) {
            self.mark_raw_thunk_computation(expr);
        }
        Ok(result)
    }

    pub(super) fn catch_type(
        &mut self,
        body: poly_expr::ExprId,
        arms: &[poly_expr::CatchArm],
    ) -> Result<Type, SpecializeError> {
        let body_ty = self.expr(body)?;
        let (body_value, body_effect) = self.catch_scrutinee_shape(body, body_ty)?;
        let result = self.graph.fresh_value();
        let has_value_arm = arms.iter().any(|arm| arm.operation.is_none());
        if !has_value_arm {
            self.graph
                .constrain_subtype(body_value.clone(), result.clone())?;
        }
        let mut effects = Vec::new();
        let mut handled_effects = Vec::new();
        for arm in arms {
            if let Some(operation) = &arm.operation {
                let op = self.catch_operation_types(operation.def, body_effect.clone())?;
                handled_effects.push(op.effect.clone());
                self.bind_pat(arm.pat, op.payload)?;
                self.bind_pat(
                    arm.continuation.ok_or(SpecializeError::MissingExprType {
                        expr: body.0,
                        role: ExprTypeRole::Actual,
                    })?,
                    Type::Fun {
                        arg: Box::new(op.continuation_input),
                        arg_effect: Box::new(Type::pure_effect()),
                        ret_effect: Box::new(op.residual_effect),
                        ret: Box::new(body_value.clone()),
                    },
                )?;
            } else {
                self.bind_pat(arm.pat, body_value.clone())?;
            }
            if let Some(guard) = arm.guard {
                effects.push(self.consume_expr_value(guard, bool_type())?.1);
            }
            let (_, arm_effect) = self.consume_expr_value(arm.body, result.clone())?;
            effects.push(arm_effect);
        }
        effects.push(self.residual_effect_after_handling(body_effect, &handled_effects)?);
        let effect = self.join_effects(effects)?;
        self.runtime_shape(effect, result)
    }

    pub(super) fn catch_scrutinee_shape(
        &mut self,
        expr: poly_expr::ExprId,
        ty: Type,
    ) -> Result<(Type, Type), SpecializeError> {
        if let Type::OpenVar(_) = ty {
            let value = self.graph.fresh_value();
            let effect = self.graph.fresh_effect();
            self.consume_expr_computation(expr, effect.clone(), value.clone())?;
            return Ok((value, effect));
        }
        Ok(split_runtime_computation_shape(ty))
    }

    pub(super) fn catch_operation_types(
        &mut self,
        def: Option<poly_expr::DefId>,
        scrutinee_effect: Type,
    ) -> Result<CatchOperationTypes, SpecializeError> {
        let Some(def) = def else {
            let payload = self.graph.fresh_value();
            return Ok(CatchOperationTypes {
                payload: payload.clone(),
                continuation_input: payload,
                effect: Type::pure_effect(),
                residual_effect: scrutinee_effect,
            });
        };
        let operation_ty = self.instantiate_def_scheme(def)?;
        let Some(parts) = function_computation_parts(&operation_ty) else {
            let payload = self.graph.fresh_value();
            return Ok(CatchOperationTypes {
                payload: payload.clone(),
                continuation_input: payload,
                effect: Type::pure_effect(),
                residual_effect: scrutinee_effect,
            });
        };
        let payload = parts.arg;
        let ret = parts.ret;
        let (continuation_input, ret_runtime_effect) = split_runtime_computation_shape(ret);
        let operation_effect = self.join_effects([parts.ret_effect, ret_runtime_effect])?;
        let handled_effect = self.constrain_operation_effect_to_scrutinee(
            operation_effect.clone(),
            scrutinee_effect.clone(),
        )?;
        let payload =
            refine_operation_type_from_handled_effect(payload, &operation_effect, &handled_effect);
        let continuation_input = refine_operation_type_from_handled_effect(
            continuation_input,
            &operation_effect,
            &handled_effect,
        );
        let residual_effect = self.residual_effect_after_handling(
            scrutinee_effect,
            std::slice::from_ref(&handled_effect),
        )?;
        Ok(CatchOperationTypes {
            payload,
            continuation_input,
            effect: handled_effect.clone(),
            residual_effect,
        })
    }

    pub(super) fn residual_effect_after_handling(
        &mut self,
        scrutinee_effect: Type,
        handled_effects: &[Type],
    ) -> Result<Type, SpecializeError> {
        if handled_effects.is_empty() || scrutinee_effect.is_pure_effect() {
            return Ok(scrutinee_effect);
        }
        let residual = self.graph.fresh_effect();
        let mut upper_items = handled_effects
            .iter()
            .flat_map(effect_row_items)
            .cloned()
            .collect::<Vec<_>>();
        upper_items.push(residual.clone());
        self.graph
            .constrain_subtype(scrutinee_effect, Type::EffectRow(upper_items))?;
        Ok(residual)
    }

    pub(super) fn constrain_operation_effect_to_scrutinee(
        &mut self,
        operation_effect: Type,
        scrutinee_effect: Type,
    ) -> Result<Type, SpecializeError> {
        if let (Type::EffectRow(operation_items), Type::EffectRow(scrutinee_items)) =
            (&operation_effect, &scrutinee_effect)
        {
            let mut handled_items = Vec::new();
            for operation_item in operation_items {
                let Some(scrutinee_item) =
                    matching_effect_row_item(operation_item, scrutinee_items)
                else {
                    continue;
                };
                self.graph
                    .constrain_subtype(operation_item.clone(), scrutinee_item.clone())?;
                self.graph
                    .constrain_subtype(scrutinee_item.clone(), operation_item.clone())?;
                handled_items.push(scrutinee_item);
            }
            if !handled_items.is_empty() {
                return Ok(Type::EffectRow(handled_items));
            }
        }
        self.graph
            .constrain_subtype(operation_effect.clone(), scrutinee_effect.clone())?;
        Ok(operation_effect)
    }

    pub(super) fn block_type(
        &mut self,
        expr: poly_expr::ExprId,
        stmts: &[poly_expr::Stmt],
        tail: Option<poly_expr::ExprId>,
    ) -> Result<Type, SpecializeError> {
        let mut effects = Vec::new();
        for stmt in stmts {
            match stmt {
                poly_expr::Stmt::Let(_, pat, value) => {
                    let binding = self.local_let_binding_type(*pat, *value)?;
                    self.bind_pat(*pat, binding.ty.clone())?;
                    let value_ty = if binding.use_as_lambda_signature {
                        self.lambda_expr_with_signature(*value, binding.ty.clone())?
                    } else {
                        self.expr(*value)?
                    };
                    let (value_value, value_effect) = split_runtime_computation_shape(value_ty);
                    if binding.use_as_lambda_signature {
                        self.graph
                            .constrain_subtype(value_value.clone(), binding.ty.clone())?;
                    } else {
                        self.consume_expr_value(*value, binding.ty.clone())?;
                    }
                    if binding.exact_value {
                        self.graph.constrain_exact(value_value, binding.ty)?;
                    }
                    effects.push(value_effect);
                }
                poly_expr::Stmt::Expr(expr) => {
                    self.discarded_exprs.insert(*expr);
                    let expr_ty = self.expr(*expr)?;
                    if !discarded_catch_has_open_result(self.arena.expr(*expr), &expr_ty) {
                        self.consume_discarded_expr(*expr, &expr_ty)?;
                    }
                    effects.push(split_runtime_computation_shape(expr_ty).1);
                }
                poly_expr::Stmt::Module(_, body) => {
                    let body_ty = self.block_type(expr, body, None)?;
                    effects.push(split_runtime_computation_shape(body_ty).1);
                }
            }
        }
        let tail_ty = match tail {
            Some(tail) => self.expr(tail)?,
            None => Type::unit(),
        };
        let (tail_value, tail_effect) = split_runtime_computation_shape(tail_ty);
        effects.push(tail_effect);
        let effect = self.join_effects(effects)?;
        let result = self.runtime_shape(effect, tail_value)?;
        if matches!(result, Type::Thunk { .. }) {
            self.mark_raw_thunk_computation(expr);
        }
        Ok(result)
    }

    pub(super) fn lambda_expr_with_signature(
        &mut self,
        expr: poly_expr::ExprId,
        signature: Type,
    ) -> Result<Type, SpecializeError> {
        let poly_expr::Expr::Lambda(param, body) = self.arena.expr(expr) else {
            return self.expr(expr);
        };
        if let Some(ty) = self.exprs.get(&expr) {
            return Ok(ty.actual.clone());
        }
        let ty = self.lambda_type_with_signature(*param, *body, signature)?;
        self.exprs.entry(expr).or_insert_with(|| ExprType {
            actual: ty.clone(),
            consumer: None,
        });
        Ok(ty)
    }

    pub(super) fn lambda_type_with_signature(
        &mut self,
        param: poly_expr::PatId,
        body: poly_expr::ExprId,
        signature: Type,
    ) -> Result<Type, SpecializeError> {
        let Some(parts) = function_computation_parts(&signature) else {
            return self.lambda_type(param, body);
        };
        self.bind_pat(
            param,
            types::runtime_shape(parts.arg_effect.clone(), parts.arg.clone()),
        )?;
        let body_ty = self.expr(body)?;
        let (ret, ret_effect) = split_runtime_computation_shape(body_ty);
        self.graph.constrain_subtype(
            types::runtime_shape(ret_effect.clone(), ret.clone()),
            types::runtime_shape(parts.ret_effect.clone(), parts.ret.clone()),
        )?;
        Ok(Type::Fun {
            arg: Box::new(parts.arg),
            arg_effect: Box::new(parts.arg_effect),
            ret_effect: Box::new(ret_effect),
            ret: Box::new(ret),
        })
    }

    pub(super) fn local_let_binding_type(
        &mut self,
        pat: poly_expr::PatId,
        value: poly_expr::ExprId,
    ) -> Result<LocalLetBindingType, SpecializeError> {
        if !matches!(self.arena.expr(value), poly_expr::Expr::Lambda(_, _)) {
            return Ok(LocalLetBindingType::fresh(&mut self.graph));
        }
        let Some(def) = self.single_binding_pat_def(pat) else {
            return Ok(LocalLetBindingType::fresh(&mut self.graph));
        };
        let Some(poly_expr::Def::Let {
            scheme: Some(scheme),
            ..
        }) = self.arena.defs.get(def)
        else {
            return Ok(LocalLetBindingType::fresh(&mut self.graph));
        };
        Ok(LocalLetBindingType {
            ty: self.instantiate_scheme(def, scheme)?,
            exact_value: false,
            use_as_lambda_signature: true,
        })
    }

    pub(super) fn single_binding_pat_def(&self, pat: poly_expr::PatId) -> Option<poly_expr::DefId> {
        match self.arena.pat(pat) {
            poly_expr::Pat::Var(def) => Some(*def),
            poly_expr::Pat::As(_, def) => Some(*def),
            _ => None,
        }
    }

    pub(super) fn mark_raw_thunk_computation(&mut self, expr: poly_expr::ExprId) {
        self.raw_thunk_computations.insert(expr);
    }

    pub(super) fn bind_pat(
        &mut self,
        pat: poly_expr::PatId,
        ty: Type,
    ) -> Result<(), SpecializeError> {
        use poly_expr::Pat as PolyPat;
        match self.arena.pat(pat) {
            PolyPat::Wild => {}
            PolyPat::Lit(lit) => self.graph.constrain_exact(ty, lit_type(lit))?,
            PolyPat::Var(def) => {
                self.locals.insert(*def, ty);
            }
            PolyPat::As(inner, def) => {
                self.locals.insert(*def, ty.clone());
                self.bind_pat(*inner, ty)?;
            }
            PolyPat::Tuple(items) => {
                let item_types = items
                    .iter()
                    .map(|_| self.graph.fresh_value())
                    .collect::<Vec<_>>();
                self.graph
                    .constrain_exact(ty, Type::Tuple(item_types.clone()))?;
                for (item, item_ty) in items.iter().zip(item_types) {
                    self.bind_pat(*item, item_ty)?;
                }
            }
            PolyPat::List {
                prefix,
                spread,
                suffix,
            } => {
                let item = self.graph.fresh_value();
                let list = list_type(item.clone());
                self.graph.constrain_exact(ty.clone(), list.clone())?;
                for pat in prefix.iter().chain(suffix) {
                    self.bind_pat(*pat, item.clone())?;
                }
                if let Some(spread) = spread {
                    self.bind_pat(*spread, list)?;
                }
            }
            PolyPat::Record { fields, spread } => {
                let field_types = fields
                    .iter()
                    .map(|field| TypeField {
                        name: field.name.clone(),
                        value: self.graph.fresh_value(),
                        optional: false,
                    })
                    .collect::<Vec<_>>();
                self.graph
                    .constrain_subtype(ty.clone(), Type::Record(field_types.clone()))?;
                for (field, field_ty) in fields.iter().zip(field_types) {
                    if let Some(default) = field.default {
                        self.consume_expr_value(default, field_ty.value.clone())?;
                    }
                    self.bind_pat(field.pat, field_ty.value)?;
                }
                if let Some(def) = record_spread_def(spread) {
                    self.locals.insert(def, self.graph.fresh_value());
                }
            }
            PolyPat::Con(ref_id, payloads) => self.bind_constructor_pat(*ref_id, payloads, ty)?,
            PolyPat::PolyVariant(tag, payloads) => {
                let payload_types = payloads
                    .iter()
                    .map(|_| self.graph.fresh_value())
                    .collect::<Vec<_>>();
                self.graph.constrain_subtype(
                    Type::PolyVariant(vec![TypeVariant {
                        name: tag.clone(),
                        payloads: payload_types.clone(),
                    }]),
                    ty,
                )?;
                for (payload, payload_ty) in payloads.iter().zip(payload_types) {
                    self.bind_pat(*payload, payload_ty)?;
                }
            }
            PolyPat::Or(left, right) => {
                self.bind_pat(*left, ty.clone())?;
                self.bind_pat(*right, ty)?;
            }
            PolyPat::Ref(ref_id) => self.bind_ref_pat(pat, *ref_id, ty)?,
        }
        Ok(())
    }

    pub(super) fn bind_constructor_pat(
        &mut self,
        ref_id: poly_expr::RefId,
        payloads: &[poly_expr::PatId],
        scrutinee: Type,
    ) -> Result<(), SpecializeError> {
        let Some(def) = self.arena.ref_target(ref_id) else {
            return Err(SpecializeError::UnresolvedRef { ref_id: ref_id.0 });
        };
        let constructor = self.instantiate_def_scheme(def)?;
        let Some((payload_tys, owner_ty)) = split_function_spine(constructor, payloads.len())
        else {
            return Ok(());
        };
        self.graph.constrain_exact(scrutinee, owner_ty)?;
        for (payload, payload_ty) in payloads.iter().zip(payload_tys) {
            self.bind_pat(*payload, payload_ty)?;
        }
        Ok(())
    }

    pub(super) fn bind_ref_pat(
        &mut self,
        pat: poly_expr::PatId,
        ref_id: poly_expr::RefId,
        scrutinee: Type,
    ) -> Result<(), SpecializeError> {
        let Some(def) = self.arena.ref_target(ref_id) else {
            return Err(SpecializeError::UnresolvedRef { ref_id: ref_id.0 });
        };
        let ty = self.instantiate_def_scheme(def)?;
        self.graph.constrain_exact(scrutinee, ty.clone())?;
        self.pat_ref_uses.push(PatRefUse { pat, ty });
        Ok(())
    }
}
