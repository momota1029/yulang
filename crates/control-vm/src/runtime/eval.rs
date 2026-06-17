use super::*;

impl<'a> Runtime<'a> {
    pub(super) fn eval_expr(&mut self, expr: ExprId, env: &mut CapturedEnv) -> RuntimeResult<'a> {
        self.stats.expr_evals += 1;
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
            EvalExpr::Local(def) => value_result(
                self.mark_active_value(
                    env.get(def)
                        .cloned()
                        .ok_or(RuntimeError::UnboundLocal { def })?,
                ),
            ),
            EvalExpr::InstanceRef(instance) => {
                let value = self.eval_instance(instance)?;
                value_result(self.mark_active_value(value))
            }
            EvalExpr::Coerce {
                source,
                target,
                expr,
            } => {
                let result = self.eval_expr(expr, env)?;
                self.continue_with(result, move |runtime, value| {
                    runtime.adapt_value(value, &source, &target)
                })
            }
            EvalExpr::MakeThunk { body } => {
                value_result(self.mark_active_created_value(Value::Thunk(Thunk::Expr {
                    body,
                    env: env.clone(),
                })))
            }
            EvalExpr::ForceThunk {
                target_value,
                thunk,
            } => {
                let result = self.eval_expr(thunk, env)?;
                self.continue_with(result, move |runtime, thunk| {
                    let result = runtime.force_thunk(thunk)?;
                    if matches!(target_value, Type::Thunk { .. }) {
                        return Ok(result);
                    }
                    runtime
                        .continue_with(result, |runtime, value| runtime.force_value_if_thunk(value))
                })
            }
            EvalExpr::FunctionAdapter {
                source,
                target,
                function,
                hygiene,
            } => {
                let function = self.eval_expr(function, env)?;
                self.continue_with(function, move |runtime, function| {
                    value_result(runtime.mark_active_created_value(Value::FunctionAdapter(
                        FunctionAdapter {
                            source: source.clone(),
                            target: target.clone(),
                            function: Box::new(function),
                            hygiene: hygiene.clone(),
                        },
                    )))
                })
            }
            EvalExpr::MarkerFrame { path, body } => {
                let mut frame_env = env.clone();
                let id = self.fresh_guard_id();
                let path_key = self.intern_path(&path);
                let markers = stack_handler_markers(id, path.clone(), path_key);
                self.with_stack_handler_frame(markers, path, move |runtime| {
                    runtime.eval_expr(body, &mut frame_env)
                })
            }
            EvalExpr::Apply { callee, arg } => {
                let env_for_arg = env.clone();
                let callee = self.eval_expr(callee, env)?;
                self.continue_with(callee, move |runtime, callee| {
                    let mut env = env_for_arg.clone();
                    let arg_result = runtime.eval_expr(arg, &mut env)?;
                    runtime.continue_with(arg_result, move |runtime, arg| {
                        runtime.apply_value(callee.clone(), arg)
                    })
                })
            }
            EvalExpr::RefSet { reference, value } => {
                self.eval_ref_set(reference, value, env.clone())
            }
            EvalExpr::Lambda { param, body } => {
                value_result(self.mark_active_created_value(Value::Closure(Closure {
                    param,
                    body,
                    env: env.clone(),
                })))
            }
            EvalExpr::Tuple(items) => self.eval_tuple(items, env.clone()),
            EvalExpr::Record { fields, spread } => self.eval_record(fields, spread, env.clone()),
            EvalExpr::PolyVariant { tag, payloads } => {
                self.eval_poly_variant(tag, payloads, env.clone())
            }
            EvalExpr::Select {
                base,
                name,
                resolution,
            } => self.eval_select(base, name, resolution, env),
            EvalExpr::Case { scrutinee, arms } => {
                let scrutinee = self.eval_expr(scrutinee, env)?;
                let env = env.clone();
                self.continue_with(scrutinee, move |runtime, scrutinee| {
                    let scrutinee = runtime.force_value_if_thunk(scrutinee)?;
                    runtime.continue_with(scrutinee, {
                        let arms = arms.clone();
                        let env = env.clone();
                        move |runtime, scrutinee| {
                            runtime.eval_case(scrutinee, arms.clone(), env.clone())
                        }
                    })
                })
            }
            EvalExpr::Catch { body, arms } => self.eval_catch(body, arms, env),
            EvalExpr::Block(block) => self.eval_block(block, env),
        }
    }

    pub(super) fn eval_record(
        &mut self,
        fields: Vec<RecordField>,
        spread: RecordSpread<ExprId>,
        env: CapturedEnv,
    ) -> RuntimeResult<'a> {
        match spread {
            RecordSpread::None => self.eval_record_fields(fields, env, Vec::new(), 0),
            RecordSpread::Head(expr) => {
                let mut spread_env = env.clone();
                let spread = self.eval_expr(expr, &mut spread_env)?;
                self.continue_with(spread, move |runtime, spread| {
                    let spread_fields = runtime.expect_record(spread)?;
                    runtime.eval_record_fields(fields.clone(), env.clone(), spread_fields, 0)
                })
            }
            RecordSpread::Tail(expr) => {
                let fields_result =
                    self.eval_record_fields(fields.clone(), env.clone(), Vec::new(), 0)?;
                self.continue_with(fields_result, move |runtime, fields| {
                    let fields = runtime.expect_record(fields)?;
                    let mut spread_env = env.clone();
                    let spread = runtime.eval_expr(expr, &mut spread_env)?;
                    runtime.continue_with(spread, move |runtime, spread| {
                        let mut combined = fields.clone();
                        combined.extend(runtime.expect_record(spread)?);
                        value_result(Value::Record(combined))
                    })
                })
            }
        }
    }

    pub(super) fn eval_ref_set(
        &mut self,
        reference: ExprId,
        value: ExprId,
        env: CapturedEnv,
    ) -> RuntimeResult<'a> {
        let mut reference_env = env.clone();
        let reference_result = self.eval_expr(reference, &mut reference_env)?;
        self.continue_with(reference_result, move |runtime, reference| {
            let reference = runtime.force_value_if_thunk(reference)?;
            let value_env = env.clone();
            runtime.continue_with(reference, move |runtime, reference| {
                let mut value_env = value_env.clone();
                let value_result = runtime.eval_expr(value, &mut value_env)?;
                runtime.continue_with(value_result, move |runtime, value| {
                    let value = runtime.force_value_if_thunk(value)?;
                    let reference = reference.clone();
                    runtime.continue_with(value, move |runtime, assigned| {
                        let update_effect =
                            runtime.project_record_field(reference.clone(), "update_effect")?;
                        let result = runtime.apply_value(update_effect, Value::Unit)?;
                        runtime.handle_ref_set_result(result, assigned)
                    })
                })
            })
        })
    }

    pub(super) fn handle_ref_set_result(
        &mut self,
        result: EvalResult<'a>,
        assigned: Value,
    ) -> RuntimeResult<'a> {
        match result {
            EvalResult::Value(value) => {
                let resolved = self.resolve_ref_set_value(value, assigned)?;
                self.continue_with(resolved, |_, _| value_result(Value::Unit))
            }
            EvalResult::Request(request) if is_ref_update_request(&request.path) => {
                let resumed = (request.resume)(self, assigned.clone())?;
                self.handle_ref_set_result(resumed, assigned)
            }
            EvalResult::Request(request) => {
                let path = request.path;
                let path_key = request.path_key;
                let guard_ids = request.guard_ids;
                let carried_guard_ids = request.carried_guard_ids;
                let payload = request.payload;
                let request_resume = request.resume.clone();
                let resolved_payload = self.resolve_ref_set_value(payload, assigned.clone())?;
                self.continue_with(resolved_payload, move |_, payload| {
                    Ok(EvalResult::Request(Request {
                        path: path.clone(),
                        path_key: path_key.clone(),
                        guard_ids: guard_ids.clone(),
                        carried_guard_ids: carried_guard_ids.clone(),
                        payload,
                        resume: Rc::new({
                            let assigned = assigned.clone();
                            let request_resume = request_resume.clone();
                            move |runtime, value| {
                                let resumed = request_resume(runtime, value)?;
                                runtime.handle_ref_set_result(resumed, assigned.clone())
                            }
                        }),
                    }))
                })
            }
        }
    }

    pub(super) fn resolve_ref_set_value(
        &mut self,
        value: Value,
        assigned: Value,
    ) -> RuntimeResult<'a> {
        match value {
            Value::Marked { value, markers } => {
                let resolved = self.resolve_ref_set_value(*value, assigned)?;
                self.continue_with(resolved, move |_, value| {
                    value_result(mark_value(value, &markers))
                })
            }
            Value::Tuple(items) => {
                self.resolve_ref_set_values(items, assigned, Vec::new(), 0, Rc::new(Value::Tuple))
            }
            Value::List(items) => self.resolve_ref_set_values(
                items
                    .to_vec()
                    .into_iter()
                    .map(|item| (*item).clone())
                    .collect(),
                assigned,
                Vec::new(),
                0,
                Rc::new(|items| Value::List(ListTree::from_items(items.into_iter().map(Rc::new)))),
            ),
            Value::Record(fields) => self.resolve_ref_set_fields(fields, assigned, Vec::new(), 0),
            Value::PolyVariant { tag, payloads } => self.resolve_ref_set_values(
                payloads,
                assigned,
                Vec::new(),
                0,
                Rc::new(move |payloads| Value::PolyVariant {
                    tag: tag.clone(),
                    payloads,
                }),
            ),
            Value::DataConstructor { def, payloads } => self.resolve_ref_set_values(
                payloads,
                assigned,
                Vec::new(),
                0,
                Rc::new(move |payloads| Value::DataConstructor { def, payloads }),
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
        finish: Rc<dyn Fn(Vec<Value>) -> Value + 'a>,
    ) -> RuntimeResult<'a> {
        if index >= values.len() {
            return value_result(finish(out));
        }
        let resolved = self.resolve_ref_set_value(values[index].clone(), assigned.clone())?;
        self.continue_with(resolved, move |runtime, value| {
            let mut out = out.clone();
            out.push(value);
            runtime.resolve_ref_set_values(
                values.clone(),
                assigned.clone(),
                out,
                index + 1,
                finish.clone(),
            )
        })
    }

    pub(super) fn resolve_ref_set_fields(
        &mut self,
        fields: Vec<ValueField>,
        assigned: Value,
        out: Vec<ValueField>,
        index: usize,
    ) -> RuntimeResult<'a> {
        if index >= fields.len() {
            return value_result(Value::Record(out));
        }
        let field = fields[index].clone();
        let resolved = self.resolve_ref_set_value(field.value, assigned.clone())?;
        self.continue_with(resolved, move |runtime, value| {
            let mut out = out.clone();
            out.push(ValueField {
                name: field.name.clone(),
                value,
            });
            runtime.resolve_ref_set_fields(fields.clone(), assigned.clone(), out, index + 1)
        })
    }

    pub(super) fn handle_ref_set_value_result(
        &mut self,
        result: EvalResult<'a>,
        assigned: Value,
    ) -> RuntimeResult<'a> {
        match result {
            EvalResult::Value(value) => self.resolve_ref_set_value(value, assigned),
            EvalResult::Request(request) if is_ref_update_request(&request.path) => {
                let resumed = (request.resume)(self, assigned.clone())?;
                self.handle_ref_set_value_result(resumed, assigned)
            }
            EvalResult::Request(request) => {
                let path = request.path;
                let path_key = request.path_key;
                let guard_ids = request.guard_ids;
                let carried_guard_ids = request.carried_guard_ids;
                let payload = request.payload;
                let request_resume = request.resume.clone();
                let resolved_payload = self.resolve_ref_set_value(payload, assigned.clone())?;
                self.continue_with(resolved_payload, move |_, payload| {
                    Ok(EvalResult::Request(Request {
                        path: path.clone(),
                        path_key: path_key.clone(),
                        guard_ids: guard_ids.clone(),
                        carried_guard_ids: carried_guard_ids.clone(),
                        payload,
                        resume: Rc::new({
                            let assigned = assigned.clone();
                            let request_resume = request_resume.clone();
                            move |runtime, value| {
                                let resumed = request_resume(runtime, value)?;
                                runtime.handle_ref_set_value_result(resumed, assigned.clone())
                            }
                        }),
                    }))
                })
            }
        }
    }

    pub(super) fn eval_record_fields(
        &mut self,
        fields: Vec<RecordField>,
        env: CapturedEnv,
        values: Vec<ValueField>,
        index: usize,
    ) -> RuntimeResult<'a> {
        if index >= fields.len() {
            return value_result(Value::Record(values));
        }

        let field = fields[index].clone();
        let mut field_env = env.clone();
        let result = self.eval_expr(field.value, &mut field_env)?;
        self.continue_with(result, move |runtime, value| {
            let mut values = values.clone();
            values.push(ValueField {
                name: field.name.clone(),
                value,
            });
            runtime.eval_record_fields(fields.clone(), env.clone(), values, index + 1)
        })
    }

    pub(super) fn eval_tuple(&mut self, items: Vec<ExprId>, env: CapturedEnv) -> RuntimeResult<'a> {
        self.eval_tuple_items(items, env, Vec::new(), 0)
    }

    pub(super) fn eval_tuple_items(
        &mut self,
        items: Vec<ExprId>,
        env: CapturedEnv,
        values: Vec<Value>,
        index: usize,
    ) -> RuntimeResult<'a> {
        if index >= items.len() {
            return value_result(Value::Tuple(values));
        }
        let mut item_env = env.clone();
        let result = self.eval_expr(items[index], &mut item_env)?;
        self.continue_with(result, move |runtime, value| {
            let mut values = values.clone();
            values.push(value);
            runtime.eval_tuple_items(items.clone(), env.clone(), values, index + 1)
        })
    }

    pub(super) fn eval_poly_variant(
        &mut self,
        tag: String,
        payloads: Vec<ExprId>,
        env: CapturedEnv,
    ) -> RuntimeResult<'a> {
        self.eval_poly_variant_payloads(tag, payloads, env, Vec::new(), 0)
    }

    pub(super) fn eval_poly_variant_payloads(
        &mut self,
        tag: String,
        payloads: Vec<ExprId>,
        env: CapturedEnv,
        values: Vec<Value>,
        index: usize,
    ) -> RuntimeResult<'a> {
        if index >= payloads.len() {
            return value_result(Value::PolyVariant {
                tag,
                payloads: values,
            });
        }
        let mut payload_env = env.clone();
        let result = self.eval_expr(payloads[index], &mut payload_env)?;
        self.continue_with(result, move |runtime, value| {
            let mut values = values.clone();
            values.push(value);
            runtime.eval_poly_variant_payloads(
                tag.clone(),
                payloads.clone(),
                env.clone(),
                values,
                index + 1,
            )
        })
    }

    pub(super) fn eval_select(
        &mut self,
        base: ExprId,
        name: String,
        resolution: Option<SelectResolution>,
        env: &mut CapturedEnv,
    ) -> RuntimeResult<'a> {
        let result = self.eval_expr(base, env)?;
        self.continue_with(result, move |runtime, base| match resolution {
            Some(SelectResolution::RecordField) => {
                value_result(runtime.project_record_field(base, &name)?)
            }
            Some(SelectResolution::Method { instance }) => {
                let method = runtime.eval_instance(instance)?;
                runtime.apply_value(method, base)
            }
            Some(SelectResolution::TypeclassMethod { .. }) => Err(RuntimeError::UnsupportedExpr {
                feature: format!("typeclass method select .{name}"),
            }),
            None => Err(RuntimeError::UnresolvedSelect { name: name.clone() }),
        })
    }

    pub(super) fn eval_case(
        &mut self,
        scrutinee: Value,
        arms: Vec<CaseArm>,
        env: CapturedEnv,
    ) -> RuntimeResult<'a> {
        self.eval_case_arm(scrutinee, arms, env, 0)
    }

    pub(super) fn eval_case_arm(
        &mut self,
        scrutinee: Value,
        arms: Vec<CaseArm>,
        env: CapturedEnv,
        index: usize,
    ) -> RuntimeResult<'a> {
        if index >= arms.len() {
            return Err(RuntimeError::NoMatchingCase);
        }

        let arm = arms[index].clone();
        let bind = self.bind_pat(arm.pat.clone(), scrutinee.clone(), env.clone())?;
        self.continue_bind(bind, move |runtime, matched, mut arm_env| {
            if !matched {
                return runtime.eval_case_arm(
                    scrutinee.clone(),
                    arms.clone(),
                    env.clone(),
                    index + 1,
                );
            }
            let Some(guard) = arm.guard else {
                return runtime.eval_expr(arm.body, &mut arm_env);
            };

            let guard_result = runtime.eval_expr(guard, &mut arm_env)?;
            let scrutinee_for_guard = scrutinee.clone();
            let arms_for_guard = arms.clone();
            let env_for_guard = env.clone();
            runtime.continue_with(guard_result, move |runtime, guard| match guard {
                Value::Bool(true) => runtime.eval_expr(arm.body, &mut arm_env.clone()),
                Value::Bool(false) => runtime.eval_case_arm(
                    scrutinee_for_guard.clone(),
                    arms_for_guard.clone(),
                    env_for_guard.clone(),
                    index + 1,
                ),
                value => Err(RuntimeError::NonBoolGuard { value }),
            })
        })
    }

    pub(super) fn eval_catch(
        &mut self,
        body: ExprId,
        arms: Vec<CatchArm>,
        env: &mut CapturedEnv,
    ) -> RuntimeResult<'a> {
        let catch_env = env.clone();
        let result = self.eval_expr(body, env)?;
        self.handle_catch_result(result, arms, catch_env)
    }

    pub(super) fn handle_catch_result(
        &mut self,
        result: EvalResult<'a>,
        arms: Vec<CatchArm>,
        env: CapturedEnv,
    ) -> RuntimeResult<'a> {
        match result {
            EvalResult::Value(value) => self.handle_catch_value(value, &arms, &env),
            EvalResult::Request(request) => self.handle_catch_request(request, arms, env),
        }
    }

    pub(super) fn handle_catch_value(
        &mut self,
        value: Value,
        arms: &[CatchArm],
        env: &CapturedEnv,
    ) -> RuntimeResult<'a> {
        self.handle_catch_value_arm(value, arms.to_vec(), env.clone(), 0)
    }

    pub(super) fn handle_catch_value_arm(
        &mut self,
        value: Value,
        arms: Vec<CatchArm>,
        env: CapturedEnv,
        index: usize,
    ) -> RuntimeResult<'a> {
        if index >= arms.len() {
            return value_result(value);
        }

        let arm = arms[index].clone();
        if arm.operation_path.is_some() {
            return self.handle_catch_value_arm(value, arms, env, index + 1);
        }

        let bind = self.bind_pat(arm.pat.clone(), value.clone(), env.clone())?;
        self.continue_bind(bind, move |runtime, matched, mut arm_env| {
            if !matched {
                return runtime.handle_catch_value_arm(
                    value.clone(),
                    arms.clone(),
                    env.clone(),
                    index + 1,
                );
            }
            let Some(guard) = arm.guard else {
                return runtime.eval_expr(arm.body, &mut arm_env);
            };

            let guard_result = runtime.eval_expr(guard, &mut arm_env)?;
            let value_for_guard = value.clone();
            let arms_for_guard = arms.clone();
            let env_for_guard = env.clone();
            runtime.continue_with(guard_result, move |runtime, guard| match guard {
                Value::Bool(true) => runtime.eval_expr(arm.body, &mut arm_env.clone()),
                Value::Bool(false) => runtime.handle_catch_value_arm(
                    value_for_guard.clone(),
                    arms_for_guard.clone(),
                    env_for_guard.clone(),
                    index + 1,
                ),
                value => Err(RuntimeError::NonBoolGuard { value }),
            })
        })
    }

    pub(super) fn handle_catch_request(
        &mut self,
        request: Request<'a>,
        arms: Vec<CatchArm>,
        env: CapturedEnv,
    ) -> RuntimeResult<'a> {
        self.handle_catch_request_arm(request, arms, env, 0)
    }

    pub(super) fn handle_catch_request_arm(
        &mut self,
        request: Request<'a>,
        arms: Vec<CatchArm>,
        env: CapturedEnv,
        index: usize,
    ) -> RuntimeResult<'a> {
        if index < arms.len() {
            let arm = arms[index].clone();
            let operation_path = arm.operation_path.as_ref();
            let operation_key = operation_path.map(|path| self.intern_path(path));
            let operation_matches = operation_key
                .as_ref()
                .is_some_and(|key| counted_path_eq(&mut self.stats, key, &request.path_key));
            let skipped_guard = operation_key
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

            let bind = self.bind_pat(arm.pat.clone(), request.payload.clone(), env.clone())?;
            return self.continue_bind(bind, move |runtime, matched, arm_env| {
                if !matched {
                    return runtime.handle_catch_request_arm(
                        request.clone(),
                        arms.clone(),
                        env.clone(),
                        index + 1,
                    );
                }
                runtime.stats.catch_request_matches += 1;
                let continuation = arm.continuation.clone();
                let guard = arm.guard;
                let body = arm.body;
                if let Some(continuation) = continuation {
                    let id = runtime.store_continuation(request.resume.clone());
                    let bind = runtime.bind_pat(continuation, Value::Continuation(id), arm_env)?;
                    let request_for_continuation = request.clone();
                    let arms_for_continuation = arms.clone();
                    let env_for_continuation = env.clone();
                    return runtime.continue_bind(bind, move |runtime, matched, mut arm_env| {
                        if !matched {
                            return runtime.handle_catch_request_arm(
                                request_for_continuation.clone(),
                                arms_for_continuation.clone(),
                                env_for_continuation.clone(),
                                index + 1,
                            );
                        }
                        let Some(guard) = guard else {
                            return runtime.eval_handler_body(body, &mut arm_env);
                        };

                        let guard_result = runtime.eval_expr(guard, &mut arm_env)?;
                        let request_for_guard = request_for_continuation.clone();
                        let arms_for_guard = arms_for_continuation.clone();
                        let env_for_guard = env_for_continuation.clone();
                        runtime.continue_with(guard_result, move |runtime, guard| match guard {
                            Value::Bool(true) => {
                                runtime.eval_handler_body(body, &mut arm_env.clone())
                            }
                            Value::Bool(false) => runtime.handle_catch_request_arm(
                                request_for_guard.clone(),
                                arms_for_guard.clone(),
                                env_for_guard.clone(),
                                index + 1,
                            ),
                            value => Err(RuntimeError::NonBoolGuard { value }),
                        })
                    });
                }

                let mut arm_env = arm_env;
                let Some(guard) = guard else {
                    return runtime.eval_handler_body(body, &mut arm_env);
                };

                let guard_result = runtime.eval_expr(guard, &mut arm_env)?;
                let request_for_guard = request.clone();
                let arms_for_guard = arms.clone();
                let env_for_guard = env.clone();
                runtime.continue_with(guard_result, move |runtime, guard| match guard {
                    Value::Bool(true) => runtime.eval_handler_body(body, &mut arm_env.clone()),
                    Value::Bool(false) => runtime.handle_catch_request_arm(
                        request_for_guard.clone(),
                        arms_for_guard.clone(),
                        env_for_guard.clone(),
                        index + 1,
                    ),
                    value => Err(RuntimeError::NonBoolGuard { value }),
                })
            });
        }

        let arms_for_resume = arms.clone();
        let env_for_resume = env.clone();
        let resume = request.resume.clone();
        Ok(EvalResult::Request(Request {
            path: request.path,
            path_key: request.path_key,
            guard_ids: request.guard_ids,
            carried_guard_ids: request.carried_guard_ids,
            payload: request.payload,
            resume: Rc::new(move |runtime, value| {
                let resumed = resume(runtime, value)?;
                runtime.handle_catch_result(
                    resumed,
                    arms_for_resume.clone(),
                    env_for_resume.clone(),
                )
            }),
        }))
    }

    pub(super) fn eval_handler_body(
        &mut self,
        body: ExprId,
        env: &mut CapturedEnv,
    ) -> RuntimeResult<'a> {
        let result = self.eval_expr(body, env)?;
        self.continue_with(result, |runtime, value| runtime.force_value_if_thunk(value))
    }

    pub(super) fn eval_block(&mut self, block: Block, env: &mut CapturedEnv) -> RuntimeResult<'a> {
        self.eval_block_parts(block.stmts, block.tail, env.clone())
    }

    pub(super) fn eval_block_parts(
        &mut self,
        stmts: Vec<Stmt>,
        tail: Option<ExprId>,
        env: CapturedEnv,
    ) -> RuntimeResult<'a> {
        self.eval_block_step(stmts, tail, env, 0, Value::Unit)
    }

    pub(super) fn eval_block_step(
        &mut self,
        stmts: Vec<Stmt>,
        tail: Option<ExprId>,
        env: CapturedEnv,
        index: usize,
        last: Value,
    ) -> RuntimeResult<'a> {
        if index >= stmts.len() {
            if let Some(tail) = tail {
                let mut env = env;
                return self.eval_expr(tail, &mut env);
            }
            return value_result(last);
        }

        match stmts[index].clone() {
            Stmt::Let(_, pat, value) => {
                let mut value_env = env.clone();
                let result = self.eval_expr(value, &mut value_env)?;
                self.continue_with(result, move |runtime, value| {
                    let value = recursive_let_value(&pat, value);
                    let bind = runtime.bind_pat(pat.clone(), value.clone(), env.clone())?;
                    let stmts_for_bind = stmts.clone();
                    let value_for_bind = value.clone();
                    runtime.continue_bind(bind, move |runtime, matched, next_env| {
                        if !matched {
                            return Err(RuntimeError::PatternMismatch);
                        }
                        runtime.eval_block_step(
                            stmts_for_bind.clone(),
                            tail,
                            next_env,
                            index + 1,
                            value_for_bind.clone(),
                        )
                    })
                })
            }
            Stmt::Expr(expr) => {
                let mut expr_env = env.clone();
                let result = self.eval_expr(expr, &mut expr_env)?;
                self.continue_with(result, move |runtime, value| {
                    runtime.eval_block_step(stmts.clone(), tail, env.clone(), index + 1, value)
                })
            }
            Stmt::Module(_, module_stmts) => {
                let result = self.eval_block_parts(module_stmts, None, env.clone())?;
                self.continue_with(result, move |runtime, value| {
                    runtime.eval_block_step(stmts.clone(), tail, env.clone(), index + 1, value)
                })
            }
        }
    }
}

// This releases the immutable program borrow before evaluation calls back into
// `&mut Runtime`, while avoiding a full `Expr` clone for copy-only nodes.
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
        source: Type,
        target: Type,
        expr: ExprId,
    },
    MakeThunk {
        body: ExprId,
    },
    ForceThunk {
        target_value: Type,
        thunk: ExprId,
    },
    FunctionAdapter {
        source: Type,
        target: Type,
        function: ExprId,
        hygiene: FunctionAdapterHygiene,
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
    Tuple(Vec<ExprId>),
    Record {
        fields: Vec<RecordField>,
        spread: RecordSpread<ExprId>,
    },
    PolyVariant {
        tag: String,
        payloads: Vec<ExprId>,
    },
    Select {
        base: ExprId,
        name: String,
        resolution: Option<SelectResolution>,
    },
    Case {
        scrutinee: ExprId,
        arms: Vec<CaseArm>,
    },
    Catch {
        body: ExprId,
        arms: Vec<CatchArm>,
    },
    Block(Block),
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
            Expr::Coerce {
                source,
                target,
                expr,
            } => Self::Coerce {
                source: source.clone(),
                target: target.clone(),
                expr: *expr,
            },
            Expr::MakeThunk { body, .. } => Self::MakeThunk { body: *body },
            Expr::ForceThunk { target, thunk, .. } => Self::ForceThunk {
                target_value: target.value.clone(),
                thunk: *thunk,
            },
            Expr::FunctionAdapter {
                source,
                target,
                function,
                hygiene,
            } => Self::FunctionAdapter {
                source: source.clone(),
                target: target.clone(),
                function: *function,
                hygiene: hygiene.clone(),
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
            Expr::Tuple(items) => Self::Tuple(items.clone()),
            Expr::Record { fields, spread } => Self::Record {
                fields: fields.clone(),
                spread: spread.clone(),
            },
            Expr::PolyVariant { tag, payloads } => Self::PolyVariant {
                tag: tag.clone(),
                payloads: payloads.clone(),
            },
            Expr::Select {
                base,
                name,
                resolution,
            } => Self::Select {
                base: *base,
                name: name.clone(),
                resolution: resolution.clone(),
            },
            Expr::Case { scrutinee, arms } => Self::Case {
                scrutinee: *scrutinee,
                arms: arms.clone(),
            },
            Expr::Catch { body, arms } => Self::Catch {
                body: *body,
                arms: arms.clone(),
            },
            Expr::Block(block) => Self::Block(block.clone()),
        }
    }
}
