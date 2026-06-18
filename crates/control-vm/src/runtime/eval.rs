use super::*;

impl<'a> Runtime<'a> {
    pub(super) fn eval_expr(&mut self, expr: ExprId, env: &mut CapturedEnv) -> RuntimeResult {
        self.stats.expr_evals += 1;
        let expr_id = expr;
        let expr = EvalExpr::from_expr(
            self.program
                .exprs
                .get(expr.0 as usize)
                .ok_or(RuntimeError::MissingExpr { expr })?,
        );
        match expr {
            EvalExpr::Lit(lit) => value_result(Value::from(&lit)),
            EvalExpr::PrimitiveOp { op, context } => self.eval_primitive_op(op, context),
            EvalExpr::Constructor { def, arity } => {
                value_result(constructor_value(def, arity, Vec::new()))
            }
            EvalExpr::EffectOp { path } => value_result(Value::EffectOp { path }),
            EvalExpr::Local(def) => {
                let lookup = env.get(def);
                let value = lookup.value.cloned();
                self.record_env_lookup(value.is_some(), lookup.steps);
                value_result(value.ok_or(RuntimeError::UnboundLocal { def })?)
            }
            EvalExpr::InstanceRef(instance) => {
                let value = self.eval_instance(instance)?;
                value_result(value)
            }
            EvalExpr::Coerce { expr } => {
                let result = self.eval_expr(expr, env)?;
                self.continue_with_frame(result, Frame::Coerce { expr: expr_id })
            }
            EvalExpr::MakeThunk { body } => value_result(Value::Thunk(Rc::new(Thunk::Expr {
                body,
                env: env.clone(),
            }))),
            EvalExpr::ForceThunk { thunk } => {
                let result = self.eval_expr(thunk, env)?;
                self.continue_with_frame(result, Frame::ForceThunk { expr: expr_id })
            }
            EvalExpr::FunctionAdapter { function } => {
                let function = self.eval_expr(function, env)?;
                self.continue_with_frame(function, Frame::MakeFunctionAdapter { expr: expr_id })
            }
            EvalExpr::MarkerFrame { path, body } => {
                let mut frame_env = env.clone();
                let id = self.fresh_guard_id();
                let path_key = self.intern_path(&path);
                let markers = stack_handler_markers(id, path_key);
                self.with_stack_handler_frame(markers, path, move |runtime| {
                    runtime.eval_expr(body, &mut frame_env)
                })
            }
            EvalExpr::Apply { callee, arg } => {
                if let Some((op, context, first_arg)) = self.direct_binary_primitive_apply(callee) {
                    return self.eval_direct_binary_primitive(
                        op,
                        context,
                        first_arg,
                        arg,
                        env.clone(),
                    );
                }
                if let Some((op, context)) = self.direct_unary_primitive_apply(callee) {
                    return self.eval_direct_unary_primitive(op, context, arg, env.clone());
                }
                if let Some(callee) = self.direct_known_callee(callee) {
                    return self.eval_direct_known_apply(callee, arg, env.clone());
                }
                let env_for_arg = env.clone();
                let callee = self.eval_expr(callee, env)?;
                self.continue_with_frame(
                    callee,
                    Frame::ApplyCallee {
                        arg,
                        env: env_for_arg,
                    },
                )
            }
            EvalExpr::RefSet { reference, value } => {
                self.eval_ref_set(reference, value, env.clone())
            }
            EvalExpr::Lambda { param, body } => value_result(Value::Closure(Rc::new(Closure {
                param,
                body,
                env: env.clone(),
            }))),
            EvalExpr::Tuple => self.eval_tuple(expr_id, env.clone()),
            EvalExpr::Record => self.eval_record(expr_id, env.clone()),
            EvalExpr::PolyVariant => self.eval_poly_variant(expr_id, env.clone()),
            EvalExpr::Select {
                base,
                name,
                resolution,
            } => self.eval_select(base, name, resolution, env),
            EvalExpr::Case { scrutinee } => {
                let scrutinee = self.eval_expr(scrutinee, env)?;
                let env = env.clone();
                let arms = self.prepare_case_arms(expr_id)?;
                self.continue_with_frame(scrutinee, Frame::CaseScrutineeForce { arms, env })
            }
            EvalExpr::Catch { body } => self.eval_catch(expr_id, body, env),
            EvalExpr::Block => {
                let block = self.prepare_block(expr_id)?;
                self.eval_block_parts(block.stmts, block.tail, env.clone())
            }
        }
    }

    pub(super) fn eval_record(&mut self, record: ExprId, env: CapturedEnv) -> RuntimeResult {
        match self.record_spread(record)? {
            RecordSpread::None => self.eval_record_fields(record, env, Vec::new(), 0),
            RecordSpread::Head(expr) => {
                let mut spread_env = env.clone();
                let spread = self.eval_expr(expr, &mut spread_env)?;
                self.continue_with_frame(spread, Frame::RecordHeadSpread { record, env })
            }
            RecordSpread::Tail(expr) => {
                let fields_result = self.eval_record_fields(record, env.clone(), Vec::new(), 0)?;
                self.continue_with_frame(
                    fields_result,
                    Frame::RecordTailFields { spread: expr, env },
                )
            }
        }
    }

    fn direct_binary_primitive_apply(
        &self,
        callee: ExprId,
    ) -> Option<(PrimitiveOp, PrimitiveContext, ExprId)> {
        let Expr::Apply {
            callee: primitive,
            arg: first_arg,
        } = self.program.exprs.get(callee.0 as usize)?
        else {
            return None;
        };
        let (op, context) = self.direct_known_primitive_op(*primitive)?;
        (op.arity() == 2).then(|| (*op, context.clone(), *first_arg))
    }

    fn direct_unary_primitive_apply(
        &self,
        callee: ExprId,
    ) -> Option<(PrimitiveOp, PrimitiveContext)> {
        let (op, context) = self.direct_known_primitive_op(callee)?;
        (op.arity() == 1).then(|| (*op, context.clone()))
    }

    fn direct_known_primitive_op(&self, expr: ExprId) -> Option<(&PrimitiveOp, &PrimitiveContext)> {
        match self.program.exprs.get(expr.0 as usize)? {
            Expr::PrimitiveOp { op, context } => Some((op, context)),
            Expr::InstanceRef(instance) => {
                let entry = self
                    .program
                    .instances
                    .get(instance.0 as usize)
                    .map(|instance| instance.entry)?;
                match self.program.exprs.get(entry.0 as usize)? {
                    Expr::PrimitiveOp { op, context } => Some((op, context)),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn direct_known_callee(&self, expr: ExprId) -> Option<DirectKnownCallee> {
        match self.program.exprs.get(expr.0 as usize)? {
            Expr::PrimitiveOp { op, context } => Some(DirectKnownCallee::Primitive {
                op: *op,
                context: context.clone(),
            }),
            Expr::Constructor { def, arity } => Some(DirectKnownCallee::Constructor {
                def: *def,
                arity: *arity,
            }),
            Expr::EffectOp { path } => Some(DirectKnownCallee::EffectOp { path: path.clone() }),
            Expr::InstanceRef(instance) => {
                let entry = self
                    .program
                    .instances
                    .get(instance.0 as usize)
                    .map(|instance| instance.entry)?;
                self.direct_known_callee_entry(entry)
            }
            _ => None,
        }
    }

    fn direct_known_callee_entry(&self, expr: ExprId) -> Option<DirectKnownCallee> {
        match self.program.exprs.get(expr.0 as usize)? {
            Expr::PrimitiveOp { op, context } => Some(DirectKnownCallee::Primitive {
                op: *op,
                context: context.clone(),
            }),
            Expr::Constructor { def, arity } => Some(DirectKnownCallee::Constructor {
                def: *def,
                arity: *arity,
            }),
            Expr::EffectOp { path } => Some(DirectKnownCallee::EffectOp { path: path.clone() }),
            Expr::Lambda { param, body } => Some(DirectKnownCallee::Closure {
                param: param.clone(),
                body: *body,
            }),
            _ => None,
        }
    }

    pub(super) fn apply_direct_instance_if_known(
        &mut self,
        instance: InstanceId,
        arg: Value,
    ) -> RuntimeResult {
        let entry = self
            .program
            .instances
            .get(instance.0 as usize)
            .map(|instance| instance.entry)
            .ok_or(RuntimeError::MissingInstance { instance })?;
        match self.direct_known_callee_entry(entry) {
            Some(callee) => self.apply_direct_known_callee_scoped(callee, arg),
            None => {
                let method = self.eval_instance(instance)?;
                self.apply_scoped_value(method, arg)
            }
        }
    }

    fn eval_direct_known_apply(
        &mut self,
        callee: DirectKnownCallee,
        arg: ExprId,
        env: CapturedEnv,
    ) -> RuntimeResult {
        let active_markers = self.active_marker_plans.last().cloned();
        let mut arg_env = env;
        let result = self.eval_expr(arg, &mut arg_env)?;
        match result {
            EvalResult::Value(arg) => self.apply_direct_known_callee_scoped(callee, arg),
            EvalResult::Request(request) => Ok(EvalResult::Request(push_frame(
                &mut self.stats,
                request,
                Frame::ApplyArg {
                    callee: match active_markers {
                        Some(markers) => mark_value_shared(callee.into_value(), &markers),
                        None => callee.into_value(),
                    },
                },
            ))),
        }
    }

    fn apply_direct_known_callee_scoped(
        &mut self,
        callee: DirectKnownCallee,
        arg: Value,
    ) -> RuntimeResult {
        let Some(markers) = self.active_marker_plans.last() else {
            return self.apply_direct_known_callee(callee, arg);
        };
        let markers = shared_markers_for_function_call(markers);
        if markers.is_empty() {
            return self.apply_direct_known_callee(callee, arg);
        }
        if !callee.evaluates_body() {
            let result = self.apply_direct_known_callee(callee, arg)?;
            return self.close_shared_scoped_result(result, markers);
        }
        self.with_shared_marker_frame(markers, move |runtime| {
            runtime.apply_direct_known_callee(callee, arg)
        })
    }

    fn apply_direct_known_callee(
        &mut self,
        callee: DirectKnownCallee,
        arg: Value,
    ) -> RuntimeResult {
        match callee {
            DirectKnownCallee::Closure { param, body } => self.bind_pat(
                param,
                arg,
                CapturedEnv::default(),
                BindThen::ApplyClosure { body },
            ),
            callee => self.apply_value(callee.into_value(), arg),
        }
    }

    fn eval_direct_binary_primitive(
        &mut self,
        op: PrimitiveOp,
        context: PrimitiveContext,
        first_arg: ExprId,
        second_arg: ExprId,
        env: CapturedEnv,
    ) -> RuntimeResult {
        let mut first_env = env.clone();
        let first = self.eval_expr(first_arg, &mut first_env)?;
        self.continue_with_frame(
            first,
            Frame::DirectBinarySecond {
                op,
                context,
                second_arg,
                env,
            },
        )
    }

    fn eval_direct_unary_primitive(
        &mut self,
        op: PrimitiveOp,
        context: PrimitiveContext,
        arg: ExprId,
        env: CapturedEnv,
    ) -> RuntimeResult {
        let mut arg_env = env;
        let arg = self.eval_expr(arg, &mut arg_env)?;
        self.continue_with_frame(arg, Frame::DirectUnaryApply { op, context })
    }

    pub(super) fn eval_ref_set(
        &mut self,
        reference: ExprId,
        value: ExprId,
        env: CapturedEnv,
    ) -> RuntimeResult {
        let mut reference_env = env.clone();
        let reference_result = self.eval_expr(reference, &mut reference_env)?;
        self.continue_with_frame(reference_result, Frame::RefSetReference { value, env })
    }

    pub(super) fn handle_ref_set_result(
        &mut self,
        result: EvalResult,
        assigned: Value,
    ) -> RuntimeResult {
        match result {
            EvalResult::Value(value) => {
                let resolved = self.resolve_ref_set_value(value, assigned)?;
                self.continue_with_frame(resolved, Frame::RefSetResolvedUnit)
            }
            EvalResult::Request(request) if is_ref_update_request(&request.path) => {
                let resumed = self.resume(request.continuation, assigned.clone())?;
                self.handle_ref_set_result(resumed, assigned)
            }
            EvalResult::Request(request) => {
                let payload = request.payload.clone();
                let resolved_payload = self.resolve_ref_set_value(payload, assigned.clone())?;
                self.continue_with_frame(
                    resolved_payload,
                    Frame::RefSetEmitResolvedRequest {
                        request,
                        assigned,
                        mode: RefSetResumeMode::Result,
                    },
                )
            }
        }
    }

    pub(super) fn resolve_ref_set_value(&mut self, value: Value, assigned: Value) -> RuntimeResult {
        match value {
            Value::Marked { value, markers } => {
                let resolved = self.resolve_ref_set_value(*value, assigned)?;
                self.continue_with_frame(resolved, Frame::MarkValue { markers })
            }
            Value::Tuple(items) => self.resolve_ref_set_values(
                items.iter().cloned().collect(),
                assigned,
                Vec::new(),
                0,
                RefSetFinish::Tuple,
            ),
            Value::List(items) => self.resolve_ref_set_values(
                items
                    .to_vec()
                    .into_iter()
                    .map(|item| (*item).clone())
                    .collect(),
                assigned,
                Vec::new(),
                0,
                RefSetFinish::List,
            ),
            Value::Record(fields) => self.resolve_ref_set_fields(
                fields.iter().cloned().collect(),
                assigned,
                Vec::new(),
                0,
            ),
            Value::PolyVariant { tag, payloads } => self.resolve_ref_set_values(
                payloads.iter().cloned().collect(),
                assigned,
                Vec::new(),
                0,
                RefSetFinish::PolyVariant { tag },
            ),
            Value::DataConstructor { def, payloads } => self.resolve_ref_set_values(
                payloads.iter().cloned().collect(),
                assigned,
                Vec::new(),
                0,
                RefSetFinish::DataConstructor { def },
            ),
            value if value_is_thunk_like(&value) => {
                let result = self.force_thunk(value)?;
                self.handle_ref_set_value_result(result, assigned)
            }
            value => value_result(value),
        }
    }

    pub(super) fn resolve_ref_set_values(
        &mut self,
        values: Vec<Value>,
        assigned: Value,
        out: Vec<Value>,
        index: usize,
        finish: RefSetFinish,
    ) -> RuntimeResult {
        if index >= values.len() {
            return value_result(finish_ref_set_values(finish, out));
        }
        let resolved = self.resolve_ref_set_value(values[index].clone(), assigned.clone())?;
        self.continue_with_frame(
            resolved,
            Frame::ResolveRefSetValues {
                values,
                assigned,
                out,
                index,
                finish,
            },
        )
    }

    pub(super) fn resolve_ref_set_fields(
        &mut self,
        fields: Vec<ValueField>,
        assigned: Value,
        out: Vec<ValueField>,
        index: usize,
    ) -> RuntimeResult {
        if index >= fields.len() {
            return value_result(Value::Record(shared_value_fields(out)));
        }
        let field = fields[index].clone();
        let resolved = self.resolve_ref_set_value(field.value, assigned.clone())?;
        self.continue_with_frame(
            resolved,
            Frame::ResolveRefSetFields {
                fields,
                assigned,
                out,
                index,
            },
        )
    }

    pub(super) fn handle_ref_set_value_result(
        &mut self,
        result: EvalResult,
        assigned: Value,
    ) -> RuntimeResult {
        match result {
            EvalResult::Value(value) => self.resolve_ref_set_value(value, assigned),
            EvalResult::Request(request) if is_ref_update_request(&request.path) => {
                let resumed = self.resume(request.continuation, assigned.clone())?;
                self.handle_ref_set_value_result(resumed, assigned)
            }
            EvalResult::Request(request) => {
                let payload = request.payload.clone();
                let resolved_payload = self.resolve_ref_set_value(payload, assigned.clone())?;
                self.continue_with_frame(
                    resolved_payload,
                    Frame::RefSetEmitResolvedRequest {
                        request,
                        assigned,
                        mode: RefSetResumeMode::ValueResult,
                    },
                )
            }
        }
    }

    pub(super) fn eval_record_fields(
        &mut self,
        record: ExprId,
        env: CapturedEnv,
        values: Vec<ValueField>,
        index: usize,
    ) -> RuntimeResult {
        let Some(value) = self.record_field_value(record, index)? else {
            return value_result(Value::Record(shared_value_fields(values)));
        };

        let mut field_env = env.clone();
        let result = self.eval_expr(value, &mut field_env)?;
        self.continue_with_frame(
            result,
            Frame::RecordField {
                record,
                env,
                values,
                index,
            },
        )
    }

    pub(super) fn eval_tuple(&mut self, tuple: ExprId, env: CapturedEnv) -> RuntimeResult {
        self.eval_tuple_items(tuple, env, Vec::new(), 0)
    }

    pub(super) fn eval_tuple_items(
        &mut self,
        tuple: ExprId,
        env: CapturedEnv,
        values: Vec<Value>,
        index: usize,
    ) -> RuntimeResult {
        let Some(item) = self.tuple_item(tuple, index)? else {
            return value_result(Value::Tuple(shared_values(values)));
        };
        let mut item_env = env.clone();
        let result = self.eval_expr(item, &mut item_env)?;
        self.continue_with_frame(
            result,
            Frame::TupleItem {
                tuple,
                env,
                values,
                index,
            },
        )
    }

    pub(super) fn eval_poly_variant(&mut self, variant: ExprId, env: CapturedEnv) -> RuntimeResult {
        self.eval_poly_variant_payloads(variant, env, Vec::new(), 0)
    }

    pub(super) fn eval_poly_variant_payloads(
        &mut self,
        variant: ExprId,
        env: CapturedEnv,
        values: Vec<Value>,
        index: usize,
    ) -> RuntimeResult {
        let Some(payload) = self.poly_variant_payload(variant, index)? else {
            return value_result(Value::PolyVariant {
                tag: self.poly_variant_tag(variant)?.to_string(),
                payloads: shared_values(values),
            });
        };
        let mut payload_env = env.clone();
        let result = self.eval_expr(payload, &mut payload_env)?;
        self.continue_with_frame(
            result,
            Frame::PolyVariantPayload {
                variant,
                env,
                values,
                index,
            },
        )
    }

    pub(super) fn record_spread(
        &self,
        record: ExprId,
    ) -> Result<RecordSpread<ExprId>, RuntimeError> {
        match self.program.exprs.get(record.0 as usize) {
            Some(Expr::Record { spread, .. }) => Ok(spread.clone()),
            Some(_) | None => Err(RuntimeError::MissingExpr { expr: record }),
        }
    }

    pub(super) fn record_field_value(
        &self,
        record: ExprId,
        index: usize,
    ) -> Result<Option<ExprId>, RuntimeError> {
        match self.program.exprs.get(record.0 as usize) {
            Some(Expr::Record { fields, .. }) => Ok(fields.get(index).map(|field| field.value)),
            Some(_) | None => Err(RuntimeError::MissingExpr { expr: record }),
        }
    }

    pub(super) fn record_field_name(
        &self,
        record: ExprId,
        index: usize,
    ) -> Result<String, RuntimeError> {
        match self.program.exprs.get(record.0 as usize) {
            Some(Expr::Record { fields, .. }) => fields
                .get(index)
                .map(|field| field.name.clone())
                .ok_or(RuntimeError::MissingExpr { expr: record }),
            Some(_) | None => Err(RuntimeError::MissingExpr { expr: record }),
        }
    }

    pub(super) fn tuple_item(
        &self,
        tuple: ExprId,
        index: usize,
    ) -> Result<Option<ExprId>, RuntimeError> {
        match self.program.exprs.get(tuple.0 as usize) {
            Some(Expr::Tuple(items)) => Ok(items.get(index).copied()),
            Some(_) | None => Err(RuntimeError::MissingExpr { expr: tuple }),
        }
    }

    pub(super) fn poly_variant_payload(
        &self,
        variant: ExprId,
        index: usize,
    ) -> Result<Option<ExprId>, RuntimeError> {
        match self.program.exprs.get(variant.0 as usize) {
            Some(Expr::PolyVariant { payloads, .. }) => Ok(payloads.get(index).copied()),
            Some(_) | None => Err(RuntimeError::MissingExpr { expr: variant }),
        }
    }

    pub(super) fn poly_variant_tag(&self, variant: ExprId) -> Result<&str, RuntimeError> {
        match self.program.exprs.get(variant.0 as usize) {
            Some(Expr::PolyVariant { tag, .. }) => Ok(tag),
            Some(_) | None => Err(RuntimeError::MissingExpr { expr: variant }),
        }
    }

    pub(super) fn coerce_types(&self, expr: ExprId) -> Result<(Type, Type), RuntimeError> {
        match self.program.exprs.get(expr.0 as usize) {
            Some(Expr::Coerce { source, target, .. }) => Ok((source.clone(), target.clone())),
            Some(_) | None => Err(RuntimeError::MissingExpr { expr }),
        }
    }

    pub(super) fn force_thunk_target_value_is_thunk(
        &self,
        expr: ExprId,
    ) -> Result<bool, RuntimeError> {
        match self.program.exprs.get(expr.0 as usize) {
            Some(Expr::ForceThunk { target, .. }) => Ok(matches!(target.value, Type::Thunk { .. })),
            Some(_) | None => Err(RuntimeError::MissingExpr { expr }),
        }
    }

    pub(super) fn function_adapter_value(
        &self,
        expr: ExprId,
        function: Value,
    ) -> Result<Value, RuntimeError> {
        match self.program.exprs.get(expr.0 as usize) {
            Some(Expr::FunctionAdapter {
                source,
                target,
                hygiene,
                ..
            }) => Ok(Value::FunctionAdapter(Rc::new(FunctionAdapter {
                source: source.clone(),
                target: target.clone(),
                function: Box::new(function),
                hygiene: hygiene.clone(),
            }))),
            Some(_) | None => Err(RuntimeError::MissingExpr { expr }),
        }
    }

    pub(super) fn eval_select(
        &mut self,
        base: ExprId,
        name: String,
        resolution: Option<SelectResolution>,
        env: &mut CapturedEnv,
    ) -> RuntimeResult {
        let result = self.eval_expr(base, env)?;
        self.continue_with_frame(result, Frame::Select { name, resolution })
    }

    pub(super) fn eval_case(
        &mut self,
        scrutinee: Value,
        arms: RuntimeCaseArms,
        env: CapturedEnv,
    ) -> RuntimeResult {
        self.eval_case_arm(scrutinee, arms, env, 0)
    }

    pub(super) fn eval_case_arm(
        &mut self,
        scrutinee: Value,
        arms: RuntimeCaseArms,
        env: CapturedEnv,
        index: usize,
    ) -> RuntimeResult {
        if index >= arms.len() {
            return Err(RuntimeError::NoMatchingCase);
        }

        let arm = &arms[index];
        self.bind_pat(
            arm.pat.clone(),
            scrutinee.clone(),
            env.clone(),
            BindThen::CaseArm {
                scrutinee,
                arms,
                env,
                index,
            },
        )
    }

    fn prepare_case_arms(&mut self, expr: ExprId) -> Result<RuntimeCaseArms, RuntimeError> {
        if let Some(arms) = self.case_arms.get(&expr) {
            return Ok(arms.clone());
        }
        let arms = match self.program.exprs.get(expr.0 as usize) {
            Some(Expr::Case { arms, .. }) => shared_case_arms(arms),
            Some(_) | None => return Err(RuntimeError::MissingExpr { expr }),
        };
        self.case_arms.insert(expr, arms.clone());
        Ok(arms)
    }

    pub(super) fn eval_catch(
        &mut self,
        expr: ExprId,
        body: ExprId,
        env: &mut CapturedEnv,
    ) -> RuntimeResult {
        let catch_env = env.clone();
        let arms = self.prepare_catch_arms(expr)?;
        let result = self.eval_expr(body, env)?;
        self.handle_catch_result(result, arms, catch_env)
    }

    fn prepare_catch_arms(&mut self, expr: ExprId) -> Result<RuntimeCatchArms, RuntimeError> {
        if let Some(arms) = self.catch_arms.get(&expr) {
            return Ok(arms.clone());
        }
        let arms = match self.program.exprs.get(expr.0 as usize) {
            Some(Expr::Catch { arms, .. }) => arms,
            Some(_) | None => return Err(RuntimeError::MissingExpr { expr }),
        };
        let arms: RuntimeCatchArms = arms
            .iter()
            .map(|arm| RuntimeCatchArm {
                operation_key: arm
                    .operation_path
                    .as_ref()
                    .map(|path| self.intern_path(path)),
                pat: arm.pat.clone(),
                continuation: arm.continuation.clone(),
                guard: arm.guard,
                body: arm.body,
            })
            .collect::<Vec<_>>()
            .into();
        self.catch_arms.insert(expr, arms.clone());
        Ok(arms)
    }

    pub(super) fn handle_catch_result(
        &mut self,
        result: EvalResult,
        arms: RuntimeCatchArms,
        env: CapturedEnv,
    ) -> RuntimeResult {
        match result {
            EvalResult::Value(value) => self.handle_catch_value(value, arms, env),
            EvalResult::Request(request) => self.handle_catch_request(request, arms, env),
        }
    }

    pub(super) fn handle_catch_value(
        &mut self,
        value: Value,
        arms: RuntimeCatchArms,
        env: CapturedEnv,
    ) -> RuntimeResult {
        self.handle_catch_value_arm(value, arms, env, 0)
    }

    pub(super) fn handle_catch_value_arm(
        &mut self,
        value: Value,
        arms: RuntimeCatchArms,
        env: CapturedEnv,
        index: usize,
    ) -> RuntimeResult {
        if index >= arms.len() {
            return value_result(value);
        }

        let arm = &arms[index];
        if arm.operation_key.is_some() {
            return self.handle_catch_value_arm(value, arms, env, index + 1);
        }

        self.bind_pat(
            arm.pat.clone(),
            value.clone(),
            env.clone(),
            BindThen::CatchValue {
                value,
                arms,
                env,
                index,
            },
        )
    }

    pub(super) fn handle_catch_request(
        &mut self,
        request: Request,
        arms: RuntimeCatchArms,
        env: CapturedEnv,
    ) -> RuntimeResult {
        self.handle_catch_request_arm(request, arms, env, 0)
    }

    pub(super) fn handle_catch_request_arm(
        &mut self,
        request: Request,
        arms: RuntimeCatchArms,
        env: CapturedEnv,
        index: usize,
    ) -> RuntimeResult {
        if index < arms.len() {
            let arm = &arms[index];
            let operation_matches = arm
                .operation_key
                .as_ref()
                .is_some_and(|key| counted_path_eq(&mut self.stats, key, &request.path_key));
            let skipped_guard = arm
                .operation_key
                .as_ref()
                .filter(|_| operation_matches)
                .and_then(|key| self.request_guard_for_path(&request, key));
            if !operation_matches || skipped_guard.is_some() {
                let request = if let Some(guard_id) = skipped_guard {
                    request_without_guard_id(request, guard_id)
                } else {
                    request
                };
                return self.handle_catch_request_arm(request, arms, env, index + 1);
            }

            return self.bind_pat(
                arm.pat.clone(),
                request.payload.clone(),
                env.clone(),
                BindThen::CatchRequestPayload {
                    request,
                    arms,
                    env,
                    index,
                },
            );
        }

        Ok(EvalResult::Request(push_frame(
            &mut self.stats,
            request,
            Frame::CatchResult { arms, env },
        )))
    }

    pub(super) fn eval_handler_body(
        &mut self,
        body: ExprId,
        env: &mut CapturedEnv,
    ) -> RuntimeResult {
        let result = self.eval_expr(body, env)?;
        self.continue_with_frame(result, Frame::HandlerBodyForce)
    }

    pub(super) fn eval_block_parts(
        &mut self,
        stmts: RuntimeBlockStmts,
        tail: Option<ExprId>,
        env: CapturedEnv,
    ) -> RuntimeResult {
        self.eval_block_step(stmts, tail, env, 0, Value::Unit)
    }

    pub(super) fn eval_block_step(
        &mut self,
        stmts: RuntimeBlockStmts,
        tail: Option<ExprId>,
        env: CapturedEnv,
        index: usize,
        last: Value,
    ) -> RuntimeResult {
        if index >= stmts.len() {
            if let Some(tail) = tail {
                let mut env = env;
                return self.eval_expr(tail, &mut env);
            }
            return value_result(last);
        }

        match &stmts[index] {
            Stmt::Let(_, pat, value) => {
                let pat = pat.clone();
                let value = *value;
                let mut value_env = env.clone();
                let result = self.eval_expr(value, &mut value_env)?;
                self.continue_with_frame(
                    result,
                    Frame::BlockLetValue {
                        pat,
                        stmts,
                        tail,
                        env,
                        index,
                    },
                )
            }
            Stmt::Expr(expr) => {
                let expr = *expr;
                let mut expr_env = env.clone();
                let result = self.eval_expr(expr, &mut expr_env)?;
                self.continue_with_frame(
                    result,
                    Frame::BlockExprValue {
                        stmts,
                        tail,
                        env,
                        index,
                    },
                )
            }
            Stmt::Module(_, module_stmts) => {
                let module_stmts = shared_block_stmts(module_stmts);
                let result = self.eval_block_parts(module_stmts, None, env.clone())?;
                self.continue_with_frame(
                    result,
                    Frame::BlockExprValue {
                        stmts,
                        tail,
                        env,
                        index,
                    },
                )
            }
        }
    }

    fn prepare_block(&mut self, expr: ExprId) -> Result<RuntimeBlock, RuntimeError> {
        if let Some(block) = self.blocks.get(&expr) {
            return Ok(block.clone());
        }
        let block = match self.program.exprs.get(expr.0 as usize) {
            Some(Expr::Block(block)) => RuntimeBlock {
                stmts: shared_block_stmts(&block.stmts),
                tail: block.tail,
            },
            Some(_) | None => return Err(RuntimeError::MissingExpr { expr }),
        };
        self.blocks.insert(expr, block.clone());
        Ok(block)
    }
}

#[derive(Clone)]
enum DirectKnownCallee {
    Closure {
        param: Pat,
        body: ExprId,
    },
    Primitive {
        op: PrimitiveOp,
        context: PrimitiveContext,
    },
    Constructor {
        def: DefId,
        arity: usize,
    },
    EffectOp {
        path: Vec<String>,
    },
}

impl DirectKnownCallee {
    fn evaluates_body(&self) -> bool {
        matches!(self, Self::Closure { .. })
    }

    fn into_value(self) -> Value {
        match self {
            Self::Closure { param, body } => Value::Closure(Rc::new(Closure {
                param,
                body,
                env: CapturedEnv::default(),
            })),
            Self::Primitive { op, context } => Value::PrimitiveOp(PrimitiveValue {
                op,
                context,
                args: Vec::new(),
            }),
            Self::Constructor { def, arity } => constructor_value(def, arity, Vec::new()),
            Self::EffectOp { path } => Value::EffectOp { path },
        }
    }
}

// This releases the immutable program borrow before evaluation calls back into
// `&mut Runtime`. Structural payloads stay in `Program` and are revisited by
// `ExprId` so frame snapshots do not clone static item/field vectors.
enum EvalExpr {
    Lit(Lit),
    PrimitiveOp {
        op: PrimitiveOp,
        context: PrimitiveContext,
    },
    Constructor {
        def: DefId,
        arity: usize,
    },
    EffectOp {
        path: Vec<String>,
    },
    Local(DefId),
    InstanceRef(InstanceId),
    Coerce {
        expr: ExprId,
    },
    MakeThunk {
        body: ExprId,
    },
    ForceThunk {
        thunk: ExprId,
    },
    FunctionAdapter {
        function: ExprId,
    },
    MarkerFrame {
        path: Vec<String>,
        body: ExprId,
    },
    Apply {
        callee: ExprId,
        arg: ExprId,
    },
    RefSet {
        reference: ExprId,
        value: ExprId,
    },
    Lambda {
        param: Pat,
        body: ExprId,
    },
    Tuple,
    Record,
    PolyVariant,
    Select {
        base: ExprId,
        name: String,
        resolution: Option<SelectResolution>,
    },
    Case {
        scrutinee: ExprId,
    },
    Catch {
        body: ExprId,
    },
    Block,
}

impl EvalExpr {
    fn from_expr(expr: &Expr) -> Self {
        match expr {
            Expr::Lit(lit) => Self::Lit(lit.clone()),
            Expr::PrimitiveOp { op, context } => Self::PrimitiveOp {
                op: *op,
                context: context.clone(),
            },
            Expr::Constructor { def, arity } => Self::Constructor {
                def: *def,
                arity: *arity,
            },
            Expr::EffectOp { path } => Self::EffectOp { path: path.clone() },
            Expr::Local(def) => Self::Local(*def),
            Expr::InstanceRef(instance) => Self::InstanceRef(*instance),
            Expr::Coerce { expr, .. } => Self::Coerce { expr: *expr },
            Expr::MakeThunk { body, .. } => Self::MakeThunk { body: *body },
            Expr::ForceThunk { thunk, .. } => Self::ForceThunk { thunk: *thunk },
            Expr::FunctionAdapter { function, .. } => Self::FunctionAdapter {
                function: *function,
            },
            Expr::MarkerFrame { path, body } => Self::MarkerFrame {
                path: path.clone(),
                body: *body,
            },
            Expr::Apply { callee, arg } => Self::Apply {
                callee: *callee,
                arg: *arg,
            },
            Expr::RefSet { reference, value } => Self::RefSet {
                reference: *reference,
                value: *value,
            },
            Expr::Lambda { param, body } => Self::Lambda {
                param: param.clone(),
                body: *body,
            },
            Expr::Tuple(_) => Self::Tuple,
            Expr::Record { .. } => Self::Record,
            Expr::PolyVariant { .. } => Self::PolyVariant,
            Expr::Select {
                base,
                name,
                resolution,
            } => Self::Select {
                base: *base,
                name: name.clone(),
                resolution: resolution.clone(),
            },
            Expr::Case { scrutinee, .. } => Self::Case {
                scrutinee: *scrutinee,
            },
            Expr::Catch { body, .. } => Self::Catch { body: *body },
            Expr::Block(_) => Self::Block,
        }
    }
}
