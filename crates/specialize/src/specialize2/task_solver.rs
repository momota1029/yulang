use super::*;

mod control;
mod finish;

impl<'a> TaskSolver<'a> {
    pub(super) fn solve_root_expr(
        arena: &'a poly_expr::Arena,
        expr: poly_expr::ExprId,
    ) -> Result<SolvedTask, SpecializeError> {
        let mut solver = Self::new(arena);
        solver.required_exprs.insert(expr);
        solver.expr(expr)?;
        solver.finish()
    }

    pub(super) fn solve_def_body(
        arena: &'a poly_expr::Arena,
        _def: poly_expr::DefId,
        body: poly_expr::ExprId,
        signature: Type,
    ) -> Result<SolvedTask, SpecializeError> {
        let mut solver = Self::new(arena);
        solver.required_exprs.insert(body);
        let actual = solver.expr(body)?;
        solver.consume_expr(body, signature.clone())?;
        solver.graph.constrain_exact(actual, signature)?;
        solver.finish()
    }

    pub(super) fn solve_computed_def_signature(
        arena: &'a poly_expr::Arena,
        def: poly_expr::DefId,
        body: poly_expr::ExprId,
    ) -> Result<Type, SpecializeError> {
        let Some(poly_expr::Def::Let {
            scheme: Some(scheme),
            ..
        }) = arena.defs.get(def)
        else {
            return Err(SpecializeError::MissingScheme {
                def: convert_def(def),
            });
        };
        let mut solver = Self::new(arena);
        solver.required_exprs.insert(body);
        let signature = solver.instantiate_scheme(def, scheme)?;
        let actual = solver.expr(body)?;
        solver.consume_expr(body, signature.clone())?;
        solver.graph.constrain_exact(actual, signature.clone())?;
        let solved = solver.finish()?;
        let actual =
            solved
                .actual_type_of(body)
                .cloned()
                .ok_or(SpecializeError::MissingExprType {
                    expr: body.0,
                    role: ExprTypeRole::Actual,
                })?;
        Ok(forced_computation_value_type(actual))
    }

    pub(super) fn new(arena: &'a poly_expr::Arena) -> Self {
        Self {
            arena,
            graph: TypeGraph::new(arena),
            exprs: HashMap::new(),
            locals: HashMap::new(),
            discarded_exprs: HashSet::new(),
            ref_uses: Vec::new(),
            select_uses: Vec::new(),
            typeclass_uses: Vec::new(),
            pat_ref_uses: Vec::new(),
            required_exprs: HashSet::new(),
            raw_thunk_computations: HashSet::new(),
        }
    }

    pub(super) fn expr(&mut self, expr: poly_expr::ExprId) -> Result<Type, SpecializeError> {
        if let Some(ty) = self.exprs.get(&expr) {
            return Ok(ty.actual.clone());
        }
        let ty = self.infer_expr(expr)?;
        self.exprs.entry(expr).or_insert_with(|| ExprType {
            actual: ty.clone(),
            consumer: None,
        });
        Ok(ty)
    }

    pub(super) fn consume_expr(
        &mut self,
        expr: poly_expr::ExprId,
        consumer: Type,
    ) -> Result<(), SpecializeError> {
        let actual = self.expr(expr)?;
        self.add_expr_consumer(expr, actual.clone(), consumer.clone());
        self.graph.constrain_subtype(actual, consumer)
    }

    pub(super) fn consume_expr_value(
        &mut self,
        expr: poly_expr::ExprId,
        consumer: Type,
    ) -> Result<(Type, Type), SpecializeError> {
        let actual = self.expr_with_value_consumer(expr, &consumer)?;
        self.add_expr_consumer(expr, actual.clone(), consumer.clone());
        let (actual_value, actual_effect) = split_runtime_computation_shape(actual);
        self.graph
            .constrain_subtype(actual_value.clone(), consumer)?;
        Ok((actual_value, actual_effect))
    }

    pub(super) fn expr_with_value_consumer(
        &mut self,
        expr: poly_expr::ExprId,
        consumer: &Type,
    ) -> Result<Type, SpecializeError> {
        if let Some(ty) = self.exprs.get(&expr) {
            return Ok(ty.actual.clone());
        }
        if let poly_expr::Expr::Lambda(_, _) = self.arena.expr(expr) {
            return self.lambda_expr_with_signature(expr, consumer.clone());
        }
        let Type::Record(expected_fields) = consumer else {
            return self.expr(expr);
        };
        let Some((fields, spread)) = self.record_expr_parts(expr) else {
            return self.expr(expr);
        };
        self.record_expr_with_expected_fields(expr, &fields, &spread, expected_fields)
    }

    pub(super) fn record_expr_parts(
        &self,
        expr: poly_expr::ExprId,
    ) -> Option<(
        Vec<(String, poly_expr::ExprId)>,
        poly_expr::RecordSpread<poly_expr::ExprId>,
    )> {
        let poly_expr::Expr::Record { fields, spread } = self.arena.expr(expr) else {
            return None;
        };
        let spread = match spread {
            poly_expr::RecordSpread::Head(expr) => poly_expr::RecordSpread::Head(*expr),
            poly_expr::RecordSpread::Tail(expr) => poly_expr::RecordSpread::Tail(*expr),
            poly_expr::RecordSpread::None => poly_expr::RecordSpread::None,
        };
        Some((fields.clone(), spread))
    }

    pub(super) fn consume_expr_computation(
        &mut self,
        expr: poly_expr::ExprId,
        effect: Type,
        value: Type,
    ) -> Result<Type, SpecializeError> {
        let actual = self.expr(expr)?;
        let (actual_value, actual_effect) = split_runtime_computation_shape(actual.clone());
        let consumer_effect = self
            .graph
            .constrain_consumed_computation_effect(actual_effect.clone(), effect)?;
        let consumer = types::runtime_shape(consumer_effect.clone(), value.clone());
        self.add_expr_consumer(expr, actual.clone(), consumer);
        self.graph.constrain_subtype(actual_value, value)?;
        Ok(consumer_effect)
    }

    pub(super) fn consume_discarded_expr(
        &mut self,
        expr: poly_expr::ExprId,
        ty: &Type,
    ) -> Result<(), SpecializeError> {
        let Type::Thunk { effect, value } = ty else {
            return Ok(());
        };
        self.consume_expr_computation(
            expr,
            effect.as_ref().clone(),
            discarded_value_type(value.as_ref()),
        )?;
        Ok(())
    }

    pub(super) fn add_expr_consumer(
        &mut self,
        expr: poly_expr::ExprId,
        actual: Type,
        consumer: Type,
    ) {
        let info = self.exprs.entry(expr).or_insert_with(|| ExprType {
            actual,
            consumer: None,
        });
        info.consumer = Some(match &info.consumer {
            Some(existing) => types::simplify_type(Type::Intersection(
                Box::new(existing.clone()),
                Box::new(consumer.clone()),
            )),
            None => consumer,
        });
    }

    pub(super) fn infer_expr(&mut self, expr: poly_expr::ExprId) -> Result<Type, SpecializeError> {
        use poly_expr::Expr as PolyExpr;
        match self.arena.expr(expr) {
            PolyExpr::Lit(lit) => Ok(lit_type(lit)),
            PolyExpr::PrimitiveOp(op) => Ok(self.primitive_type(*op)),
            PolyExpr::Var(ref_id) => self.var_type(expr, *ref_id),
            PolyExpr::App(callee, arg) => self.apply_type(expr, *callee, *arg),
            PolyExpr::RefSet(reference, value) => self.ref_set_type(*reference, *value),
            PolyExpr::Lambda(param, body) => self.lambda_type(*param, *body),
            PolyExpr::Tuple(items) => self.tuple_type(expr, items),
            PolyExpr::Record { fields, spread } => self.record_type(expr, fields, spread),
            PolyExpr::PolyVariant(tag, payloads) => self.poly_variant_type(expr, tag, payloads),
            PolyExpr::Select(base, select) => self.select_type(expr, *base, *select),
            PolyExpr::Case(scrutinee, arms) => self.case_type(expr, *scrutinee, arms),
            PolyExpr::Catch(body, arms) => self.catch_type(*body, arms),
            PolyExpr::Block(stmts, tail) => self.block_type(expr, stmts, *tail),
        }
    }

    pub(super) fn var_type(
        &mut self,
        expr: poly_expr::ExprId,
        ref_id: poly_expr::RefId,
    ) -> Result<Type, SpecializeError> {
        let Some(def) = self.arena.ref_target(ref_id) else {
            return Err(SpecializeError::UnresolvedRef { ref_id: ref_id.0 });
        };
        if let Some(local) = self.locals.get(&def).cloned() {
            return Ok(local);
        }
        if self.arena.constructors.contains_key(&def) {
            return self.instantiate_def_scheme(def);
        }
        if self.arena.effect_operations.contains_key(&def) {
            return self.instantiate_def_scheme(def);
        }
        match self.arena.defs.get(def) {
            Some(poly_expr::Def::Let {
                scheme: Some(scheme),
                body,
                ..
            }) => {
                let ty = self.instantiate_scheme(def, scheme)?;
                if body.is_some() {
                    self.ref_uses.push(RefUse {
                        expr,
                        ty: ty.clone(),
                    });
                }
                Ok(ty)
            }
            Some(poly_expr::Def::Arg) | Some(poly_expr::Def::Let { body: None, .. }) => {
                Ok(self.graph.fresh_value())
            }
            Some(poly_expr::Def::Let { scheme: None, .. }) => Err(SpecializeError::MissingScheme {
                def: convert_def(def),
            }),
            Some(other) => Err(SpecializeError::UnsupportedDefKind {
                def: convert_def(def),
                kind: def_kind(other),
            }),
            None => Err(SpecializeError::MissingDef {
                def: convert_def(def),
            }),
        }
    }

    pub(super) fn apply_type(
        &mut self,
        expr: poly_expr::ExprId,
        callee: poly_expr::ExprId,
        arg: poly_expr::ExprId,
    ) -> Result<Type, SpecializeError> {
        if let poly_expr::Expr::Var(ref_id) = self.arena.expr(callee)
            && let Some(def) = self.arena.ref_target(*ref_id)
            && self.arena.effect_operations.contains_key(&def)
        {
            return self.effect_operation_apply_type(expr, arg, def);
        }

        let callee_ty = self.expr(callee)?;
        let (callee_value, callee_effect) = split_runtime_computation_shape(callee_ty.clone());
        let (call_arg_effect, ret_effect, ret_value) =
            match function_computation_parts(&callee_value) {
                Some(parts) => {
                    let (call_arg_effect, runtime_arg_effect) = if parts.arg_effect.is_pure_effect()
                    {
                        (
                            self.consume_expr_value(arg, parts.arg.clone())?.1,
                            Type::pure_effect(),
                        )
                    } else {
                        let runtime_arg_effect = self.consume_expr_computation(
                            arg,
                            parts.arg_effect.clone(),
                            parts.arg.clone(),
                        )?;
                        (Type::pure_effect(), runtime_arg_effect)
                    };
                    let callee_consumer = Type::Fun {
                        arg: Box::new(parts.arg.clone()),
                        arg_effect: Box::new(runtime_arg_effect),
                        ret_effect: Box::new(parts.ret_effect.clone()),
                        ret: Box::new(parts.ret.clone()),
                    };
                    self.add_expr_consumer(callee, callee_ty.clone(), callee_consumer.clone());
                    self.graph
                        .constrain_subtype(callee_value.clone(), callee_consumer)?;
                    (call_arg_effect, parts.ret_effect, parts.ret)
                }
                None => {
                    let arg_ty = self.graph.fresh_value();
                    let ret_ty = self.graph.fresh_value();
                    let ret_effect = self.graph.fresh_effect();
                    let callee_consumer = Type::Fun {
                        arg: Box::new(arg_ty.clone()),
                        arg_effect: Box::new(Type::pure_effect()),
                        ret_effect: Box::new(ret_effect.clone()),
                        ret: Box::new(ret_ty.clone()),
                    };
                    self.add_expr_consumer(callee, callee_ty.clone(), callee_consumer.clone());
                    self.graph
                        .constrain_subtype(callee_value.clone(), callee_consumer)?;
                    let call_arg_effect = self.consume_expr_value(arg, arg_ty.clone())?.1;
                    (call_arg_effect, ret_effect, ret_ty)
                }
            };
        let has_evaluation_effect =
            !callee_effect.is_pure_effect() || !call_arg_effect.is_pure_effect();
        let effect = self.join_effects([callee_effect, call_arg_effect, ret_effect])?;
        let result = self.runtime_shape(effect, ret_value)?;
        if has_evaluation_effect && matches!(result, Type::Thunk { .. }) {
            self.mark_raw_thunk_computation(expr);
        }
        Ok(result)
    }

    pub(super) fn effect_operation_apply_type(
        &mut self,
        _expr: poly_expr::ExprId,
        arg: poly_expr::ExprId,
        def: poly_expr::DefId,
    ) -> Result<Type, SpecializeError> {
        let operation_ty = self.instantiate_def_scheme(def)?;
        let Some(parts) = function_computation_parts(&operation_ty) else {
            let arg_ty = self.graph.fresh_value();
            self.consume_expr_value(arg, arg_ty)?;
            return self.runtime_shape(Type::pure_effect(), Type::Never);
        };
        let call_arg_effect = self.consume_expr_value(arg, parts.arg.clone())?.1;
        let (ret_value, ret_runtime_effect) = split_runtime_computation_shape(parts.ret);
        let operation_effect = self.join_effects([parts.ret_effect, ret_runtime_effect])?;
        let effect = self.join_effects([call_arg_effect, operation_effect])?;
        self.runtime_shape(effect, ret_value)
    }

    pub(super) fn ref_set_type(
        &mut self,
        reference: poly_expr::ExprId,
        value: poly_expr::ExprId,
    ) -> Result<Type, SpecializeError> {
        let value_ty = self.expr(value)?;
        let (value_value, value_effect) = split_runtime_computation_shape(value_ty);
        let update_effect = self.graph.fresh_effect();
        let reference_consumer = std_types::ref_type(update_effect.clone(), value_value.clone());
        let (_, reference_effect) = self.consume_expr_value(reference, reference_consumer)?;
        let effect = self.join_effects([reference_effect, value_effect, update_effect])?;
        self.runtime_shape(effect, Type::unit())
    }

    pub(super) fn lambda_type(
        &mut self,
        param: poly_expr::PatId,
        body: poly_expr::ExprId,
    ) -> Result<Type, SpecializeError> {
        let arg = self.graph.fresh_value();
        let arg_effect = self.graph.fresh_effect();
        self.bind_pat(param, types::runtime_shape(arg_effect.clone(), arg.clone()))?;
        let body_ty = self.expr(body)?;
        let (ret, ret_effect) = split_runtime_computation_shape(body_ty);
        self.consume_expr(body, types::runtime_shape(ret_effect.clone(), ret.clone()))?;
        Ok(Type::Fun {
            arg: Box::new(arg),
            arg_effect: Box::new(arg_effect),
            ret_effect: Box::new(ret_effect),
            ret: Box::new(ret),
        })
    }

    pub(super) fn tuple_type(
        &mut self,
        expr: poly_expr::ExprId,
        items: &[poly_expr::ExprId],
    ) -> Result<Type, SpecializeError> {
        let mut values = Vec::with_capacity(items.len());
        let mut effects = Vec::new();
        for item in items {
            let item_ty = self.expr(*item)?;
            let (value, effect) = split_runtime_computation_shape(item_ty);
            self.consume_expr_value(*item, value.clone())?;
            values.push(value);
            effects.push(effect);
        }
        let effect = self.join_effects(effects)?;
        let result = self.runtime_shape(effect, Type::Tuple(values))?;
        if matches!(result, Type::Thunk { .. }) {
            self.mark_raw_thunk_computation(expr);
        }
        Ok(result)
    }

    pub(super) fn record_type(
        &mut self,
        expr: poly_expr::ExprId,
        fields: &[(String, poly_expr::ExprId)],
        spread: &poly_expr::RecordSpread<poly_expr::ExprId>,
    ) -> Result<Type, SpecializeError> {
        self.record_type_with_expected_fields(expr, fields, spread, None)
    }

    pub(super) fn record_expr_with_expected_fields(
        &mut self,
        expr: poly_expr::ExprId,
        fields: &[(String, poly_expr::ExprId)],
        spread: &poly_expr::RecordSpread<poly_expr::ExprId>,
        expected_fields: &[TypeField],
    ) -> Result<Type, SpecializeError> {
        if let Some(ty) = self.exprs.get(&expr) {
            return Ok(ty.actual.clone());
        }
        let ty =
            self.record_type_with_expected_fields(expr, fields, spread, Some(expected_fields))?;
        self.exprs.entry(expr).or_insert_with(|| ExprType {
            actual: ty.clone(),
            consumer: None,
        });
        Ok(ty)
    }

    pub(super) fn record_type_with_expected_fields(
        &mut self,
        expr: poly_expr::ExprId,
        fields: &[(String, poly_expr::ExprId)],
        spread: &poly_expr::RecordSpread<poly_expr::ExprId>,
        expected_fields: Option<&[TypeField]>,
    ) -> Result<Type, SpecializeError> {
        let mut effects = Vec::new();
        let mut typed = Vec::with_capacity(fields.len());
        for (name, value_expr) in fields {
            let expected = expected_fields
                .and_then(|fields| record_field_type(fields, name))
                .map(|field| field.value.clone());
            let (value, effect) = match expected {
                Some(expected) => {
                    let value_ty = self.expr_with_value_consumer(*value_expr, &expected)?;
                    let (value, effect) = split_runtime_computation_shape(value_ty);
                    self.graph.constrain_subtype(value.clone(), expected)?;
                    (value, effect)
                }
                None => {
                    let value_ty = self.expr(*value_expr)?;
                    let (value, effect) = split_runtime_computation_shape(value_ty);
                    self.consume_expr_value(*value_expr, value.clone())?;
                    (value, effect)
                }
            };
            effects.push(effect);
            typed.push(TypeField {
                name: name.clone(),
                value,
                optional: false,
            });
        }
        match spread {
            poly_expr::RecordSpread::None => {}
            poly_expr::RecordSpread::Head(expr) | poly_expr::RecordSpread::Tail(expr) => {
                let spread_ty = self.expr(*expr)?;
                let (spread_value, spread_effect) = split_runtime_computation_shape(spread_ty);
                self.consume_expr_value(*expr, spread_value.clone())?;
                effects.push(spread_effect);
                if let Type::Record(mut spread_fields) = spread_value {
                    if matches!(spread, poly_expr::RecordSpread::Head(_)) {
                        spread_fields.extend(typed);
                        typed = spread_fields;
                    } else {
                        typed.extend(spread_fields);
                    }
                }
            }
        }
        let effect = self.join_effects(effects)?;
        let result = self.runtime_shape(effect, Type::Record(typed))?;
        if matches!(result, Type::Thunk { .. }) {
            self.mark_raw_thunk_computation(expr);
        }
        Ok(result)
    }

    pub(super) fn poly_variant_type(
        &mut self,
        expr: poly_expr::ExprId,
        tag: &str,
        payloads: &[poly_expr::ExprId],
    ) -> Result<Type, SpecializeError> {
        let mut values = Vec::with_capacity(payloads.len());
        let mut effects = Vec::new();
        for payload in payloads {
            let payload_ty = self.expr(*payload)?;
            let (value, effect) = split_runtime_computation_shape(payload_ty);
            self.consume_expr_value(*payload, value.clone())?;
            values.push(value);
            effects.push(effect);
        }
        let effect = self.join_effects(effects)?;
        let result = self.runtime_shape(
            effect,
            Type::PolyVariant(vec![TypeVariant {
                name: tag.to_string(),
                payloads: values,
            }]),
        )?;
        if matches!(result, Type::Thunk { .. }) {
            self.mark_raw_thunk_computation(expr);
        }
        Ok(result)
    }

    pub(super) fn select_type(
        &mut self,
        expr: poly_expr::ExprId,
        base: poly_expr::ExprId,
        select: poly_expr::SelectId,
    ) -> Result<Type, SpecializeError> {
        let select_data = self.arena.select(select);
        match select_data.resolution {
            Some(poly_expr::SelectResolution::RecordField) => {
                let field = self.graph.fresh_value();
                let (_, base_effect) = self.consume_expr_value(
                    base,
                    Type::Record(vec![TypeField {
                        name: select_data.name.clone(),
                        value: field.clone(),
                        optional: false,
                    }]),
                )?;
                let result = self.runtime_shape(base_effect.clone(), field)?;
                if !base_effect.is_pure_effect() && matches!(result, Type::Thunk { .. }) {
                    self.mark_raw_thunk_computation(expr);
                }
                Ok(result)
            }
            Some(poly_expr::SelectResolution::Method { def }) => {
                let method = self.instantiate_def_scheme(def)?;
                let Some(parts) = function_computation_parts(&method) else {
                    self.expr(base)?;
                    return Ok(self.graph.fresh_value());
                };
                let demand = self.consume_selected_method_receiver(base, &parts)?;
                self.select_uses.push(SelectUse {
                    expr,
                    ty: demand.signature,
                });
                let base_effect = demand.evaluation_effect;
                let has_evaluation_effect = !base_effect.is_pure_effect();
                let effect = self.join_effects([base_effect, parts.ret_effect])?;
                let result = self.runtime_shape(effect, parts.ret)?;
                if has_evaluation_effect && matches!(result, Type::Thunk { .. }) {
                    self.mark_raw_thunk_computation(expr);
                }
                Ok(result)
            }
            Some(poly_expr::SelectResolution::TypeclassMethod { member }) => {
                let method = self.instantiate_def_scheme(member)?;
                let Some(parts) = function_computation_parts(&method) else {
                    self.expr(base)?;
                    return Ok(self.graph.fresh_value());
                };
                let demand = self.consume_selected_method_receiver(base, &parts)?;
                self.typeclass_uses.push(TypeclassUse {
                    expr,
                    member,
                    method_ty: demand.signature,
                });
                let base_effect = demand.evaluation_effect;
                let has_evaluation_effect = !base_effect.is_pure_effect();
                let effect = self.join_effects([base_effect, parts.ret_effect])?;
                let result = self.runtime_shape(effect, parts.ret)?;
                if has_evaluation_effect && matches!(result, Type::Thunk { .. }) {
                    self.mark_raw_thunk_computation(expr);
                }
                Ok(result)
            }
            None => {
                self.expr(base)?;
                Ok(self.graph.fresh_value())
            }
        }
    }

    pub(super) fn consume_selected_method_receiver(
        &mut self,
        base: poly_expr::ExprId,
        parts: &FunctionComputationParts,
    ) -> Result<SelectedMethodDemand, SpecializeError> {
        let (evaluation_effect, receiver_effect) = if parts.arg_effect.is_pure_effect() {
            (
                self.consume_expr_value(base, parts.arg.clone())?.1,
                Type::pure_effect(),
            )
        } else {
            (
                Type::pure_effect(),
                self.consume_expr_computation(base, parts.arg_effect.clone(), parts.arg.clone())?,
            )
        };
        Ok(SelectedMethodDemand {
            evaluation_effect,
            signature: Type::Fun {
                arg: Box::new(parts.arg.clone()),
                arg_effect: Box::new(receiver_effect),
                ret_effect: Box::new(parts.ret_effect.clone()),
                ret: Box::new(parts.ret.clone()),
            },
        })
    }
}
