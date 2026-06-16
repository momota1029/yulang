use super::*;

impl<'a> ExprTypeSolver<'a> {
    pub(super) fn primitive_spine_callee_expected(
        &self,
        callee: poly_expr::ExprId,
        ret: Type,
    ) -> Option<Type> {
        let (op, applied) = self.primitive_spine(callee)?;
        let ret = runtime_value_shape(&ret).clone();
        let arg = primitive_spine_arg_type(op, applied, &ret)?;
        Some(types::pure_function_type(arg, ret))
    }

    pub(super) fn primitive_spine(
        &self,
        expr: poly_expr::ExprId,
    ) -> Option<(poly_expr::PrimitiveOp, usize)> {
        match self.arena.expr(expr) {
            poly_expr::Expr::PrimitiveOp(op) => Some((*op, 0)),
            poly_expr::Expr::App(callee, _) => {
                let (op, applied) = self.primitive_spine(*callee)?;
                Some((op, applied + 1))
            }
            _ => None,
        }
    }

    pub(super) fn catch_type(
        &mut self,
        body: poly_expr::ExprId,
        arms: &[poly_expr::CatchArm],
        expected: Option<Type>,
    ) -> Result<Type, SpecializeError> {
        let expected_result = expected.unwrap_or_else(|| self.fresh_value_slot());
        let (result, _) = split_runtime_computation_shape(expected_result);
        let body_actual = self.expr(body, None)?;
        let (scrutinee_value, scrutinee_effect) = split_runtime_computation_shape(body_actual);
        self.expr(body, Some(scrutinee_value.clone()))?;
        let mut handled_effects = Vec::new();
        let mut effects = Vec::new();
        for arm in arms {
            if let Some(handled) =
                self.bind_catch_arm(arm, scrutinee_value.clone(), scrutinee_effect.clone())?
            {
                handled_effects.push(handled);
            }
            if let Some(guard) = arm.guard {
                let guard_actual = self.expr(guard, Some(bool_type()))?;
                effects.push(split_runtime_computation_shape(guard_actual).1);
            }
            let arm_actual = self.expr(arm.body, Some(result.clone()))?;
            effects.push(split_runtime_computation_shape(arm_actual).1);
        }
        effects.push(catch_residual_effect(scrutinee_effect, &handled_effects));
        let effect = self.join_call_effects(effects)?;
        let result = types::runtime_shape(effect, result);
        if matches!(result, Type::Thunk { .. }) {
            self.plan.mark_raw_thunk_computation(body);
        }
        Ok(result)
    }

    pub(super) fn bind_catch_arm(
        &mut self,
        arm: &poly_expr::CatchArm,
        scrutinee_value: Type,
        scrutinee_effect: Type,
    ) -> Result<Option<Type>, SpecializeError> {
        let Some(continuation) = arm.continuation else {
            self.bind_pat(arm.pat, scrutinee_value)?;
            return Ok(None);
        };

        let operation =
            self.catch_operation_types(arm.operation.as_ref(), scrutinee_effect.clone())?;
        self.bind_pat(arm.pat, operation.payload)?;
        let continuation_ret = types::runtime_shape(operation.residual_effect, scrutinee_value);
        self.bind_pat(
            continuation,
            types::pure_function_type(operation.continuation_input, continuation_ret),
        )?;
        Ok(Some(operation.effect))
    }

    pub(super) fn catch_operation_types(
        &mut self,
        operation: Option<&poly_expr::CatchOperation>,
        scrutinee_effect: Type,
    ) -> Result<CatchOperationTypes, SpecializeError> {
        let Some(operation) = operation else {
            let payload = self.fresh_value_slot();
            return Ok(CatchOperationTypes {
                payload: payload.clone(),
                continuation_input: payload,
                effect: Type::pure_effect(),
                residual_effect: scrutinee_effect,
            });
        };
        let Some(def) = operation.def else {
            let payload = self.fresh_value_slot();
            return Ok(CatchOperationTypes {
                payload: payload.clone(),
                continuation_input: payload,
                effect: Type::pure_effect(),
                residual_effect: scrutinee_effect,
            });
        };
        let Some(poly_expr::Def::Let {
            scheme: Some(scheme),
            ..
        }) = self.arena.defs.get(def)
        else {
            let payload = self.fresh_value_slot();
            return Ok(CatchOperationTypes {
                payload: payload.clone(),
                continuation_input: payload,
                effect: Type::pure_effect(),
                residual_effect: scrutinee_effect,
            });
        };
        let operation_ty = self.instantiate_scheme(def, scheme)?;
        let Some((payload, ret)) = function_runtime_parts(&operation_ty) else {
            let payload = self.fresh_value_slot();
            return Ok(CatchOperationTypes {
                payload: payload.clone(),
                continuation_input: payload,
                effect: Type::pure_effect(),
                residual_effect: scrutinee_effect,
            });
        };
        let (continuation_input, operation_effect) = split_runtime_computation_shape(ret);
        let handled_effect = self
            .constrain_operation_effect_to_scrutinee(operation_effect, scrutinee_effect.clone())?;
        let residual_effect =
            catch_residual_effect(scrutinee_effect, std::slice::from_ref(&handled_effect));
        Ok(CatchOperationTypes {
            payload,
            continuation_input,
            effect: handled_effect,
            residual_effect,
        })
    }

    pub(super) fn constrain_operation_effect_to_scrutinee(
        &mut self,
        operation_effect: Type,
        scrutinee_effect: Type,
    ) -> Result<Type, SpecializeError> {
        if let (Type::EffectRow(operation_items), Type::EffectRow(scrutinee_items)) =
            (&operation_effect, &scrutinee_effect)
        {
            let mut constrained = false;
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
                constrained = true;
                handled_items.push(scrutinee_item);
            }
            if constrained {
                return Ok(Type::EffectRow(handled_items));
            }
        }
        self.graph
            .constrain_subtype(operation_effect.clone(), scrutinee_effect.clone())?;
        self.graph
            .constrain_subtype(scrutinee_effect, operation_effect.clone())?;
        Ok(operation_effect)
    }

    pub(super) fn lambda_type(
        &mut self,
        param: poly_expr::PatId,
        body: poly_expr::ExprId,
        expected: Option<Type>,
    ) -> Result<Type, SpecializeError> {
        let function = match expected {
            Some(Type::Fun { .. }) => expected.expect("checked as function"),
            Some(other) => {
                self.expr(body, None)?;
                return Ok(other);
            }
            None => types::pure_function_type(self.fresh_value_slot(), self.fresh_value_slot()),
        };
        let Type::Fun { arg, ret, .. } = &function else {
            unreachable!("function shape checked above");
        };
        self.bind_pat(param, arg.as_ref().clone())?;
        self.expr(body, Some(ret.as_ref().clone()))?;
        Ok(function)
    }

    pub(super) fn tuple_type(
        &mut self,
        items: &[poly_expr::ExprId],
        expected: Option<&Type>,
    ) -> Result<Type, SpecializeError> {
        let expected_items = match expected {
            Some(Type::Tuple(expected_items)) if expected_items.len() == items.len() => {
                Some(expected_items.as_slice())
            }
            _ => None,
        };
        let mut item_types = Vec::with_capacity(items.len());
        for (index, item) in items.iter().enumerate() {
            let expected = expected_items.and_then(|items| items.get(index)).cloned();
            item_types.push(self.expr(*item, expected)?);
        }
        Ok(Type::Tuple(item_types))
    }

    pub(super) fn block_type(
        &mut self,
        expr: Option<poly_expr::ExprId>,
        stmts: &[poly_expr::Stmt],
        tail: Option<poly_expr::ExprId>,
        expected: Option<Type>,
    ) -> Result<Type, SpecializeError> {
        let expected_result = expected.unwrap_or_else(|| self.fresh_value_slot());
        let (result_value, _) = split_runtime_computation_shape(expected_result);
        let mut effects = Vec::new();
        for stmt in stmts {
            match stmt {
                poly_expr::Stmt::Let(_, pat, value) => {
                    let scheme_type = self.local_let_scheme_type(*pat)?;
                    let previous_prebound_local =
                        self.prebind_local_let_scheme(scheme_type.as_ref());
                    if scheme_type
                        .as_ref()
                        .is_some_and(LocalLetSchemeType::is_polymorphic)
                        && self.local_let_value_can_defer(*value)
                    {
                        effects.push(Type::pure_effect());
                        continue;
                    }
                    let expected = scheme_type
                        .as_ref()
                        .and_then(|scheme| scheme.expr_expected());
                    let value_ty = match self.expr(*value, expected) {
                        Ok(value_ty) => value_ty,
                        Err(error) => {
                            self.restore_prebound_local(previous_prebound_local);
                            return Err(error);
                        }
                    };
                    let (value_ty, effect) = split_runtime_computation_shape(value_ty);
                    if !effect.is_pure_effect() {
                        if let Err(error) = self.expr(*value, Some(value_ty.clone())) {
                            self.restore_prebound_local(previous_prebound_local);
                            return Err(error);
                        }
                    }
                    effects.push(effect);
                    let binding_ty = if let Some(scheme) = scheme_type {
                        scheme.binding_type()
                    } else {
                        Some(value_ty)
                    };
                    if let Some(binding_ty) = binding_ty {
                        self.bind_pat(*pat, binding_ty)?;
                    }
                }
                poly_expr::Stmt::Expr(value) => {
                    let value_ty = self.expr(*value, None)?;
                    effects.push(split_runtime_computation_shape(value_ty).1);
                }
                poly_expr::Stmt::Module(_, body) => {
                    let value_ty = self.block_type(None, body, None, None)?;
                    effects.push(split_runtime_computation_shape(value_ty).1);
                }
            }
        }
        let tail_ty = match tail {
            Some(tail) => self.expr(tail, Some(result_value.clone()))?,
            None => Type::unit(),
        };
        effects.push(split_runtime_computation_shape(tail_ty).1);
        let effect = self.join_call_effects(effects)?;
        let result = types::runtime_shape(effect, result_value);
        if let Some(expr) = expr
            && matches!(result, Type::Thunk { .. })
        {
            self.plan.mark_raw_thunk_computation(expr);
        }
        Ok(result)
    }

    pub(super) fn prebind_local_let_scheme(
        &mut self,
        scheme_type: Option<&LocalLetSchemeType>,
    ) -> Option<(poly_expr::DefId, Option<Type>)> {
        let scheme_type = scheme_type?;
        let ty = scheme_type.prebound_type()?;
        Some((
            scheme_type.def,
            self.local_types.insert(scheme_type.def, ty),
        ))
    }

    pub(super) fn restore_prebound_local(
        &mut self,
        previous: Option<(poly_expr::DefId, Option<Type>)>,
    ) {
        let Some((def, previous_ty)) = previous else {
            return;
        };
        match previous_ty {
            Some(previous_ty) => {
                self.local_types.insert(def, previous_ty);
            }
            None => {
                self.local_types.remove(&def);
            }
        }
    }

    pub(super) fn local_let_scheme_type(
        &mut self,
        pat: poly_expr::PatId,
    ) -> Result<Option<LocalLetSchemeType>, SpecializeError> {
        let poly_expr::Pat::Var(def) = self.arena.pat(pat) else {
            return Ok(None);
        };
        let Some(poly_expr::Def::Let {
            scheme: Some(scheme),
            ..
        }) = self.arena.defs.get(*def)
        else {
            return Ok(None);
        };
        if !scheme.quantifiers.is_empty() || !scheme.stack_quantifiers.is_empty() {
            return Ok(Some(LocalLetSchemeType {
                def: *def,
                monomorphic_ty: None,
            }));
        }
        let ty = self.instantiate_monomorphic_scheme(*def, scheme)?;
        Ok(Some(LocalLetSchemeType {
            def: *def,
            monomorphic_ty: Some(ty),
        }))
    }
}
