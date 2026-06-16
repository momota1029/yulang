use super::*;

impl<'a> Runtime<'a> {
    pub(super) fn eval_expr(&mut self, expr: &Expr, env: &mut CapturedEnv) -> RuntimeResult<'a> {
        match &expr.kind {
            ExprKind::Lit(lit) => value_result(Value::from(lit)),
            ExprKind::PrimitiveOp { op, context } => self.eval_primitive_op(*op, context.clone()),
            ExprKind::Constructor { def, arity } => {
                value_result(constructor_value(*def, *arity, Vec::new()))
            }
            ExprKind::EffectOp { path } => value_result(Value::EffectOp { path: path.clone() }),
            ExprKind::Local(def) => value_result(
                self.mark_active_value(
                    env.locals
                        .get(def)
                        .cloned()
                        .ok_or(RuntimeError::UnboundLocal { def: *def })?,
                ),
            ),
            ExprKind::InstanceRef(instance) => {
                let value = self.eval_instance(*instance)?;
                value_result(self.mark_active_value(value))
            }
            ExprKind::Coerce {
                source,
                target,
                expr,
            } => {
                let source = source.clone();
                let target = target.clone();
                let result = self.eval_expr(expr, env)?;
                self.continue_with(result, move |runtime, value| {
                    runtime.adapt_value(value, &source, &target)
                })
            }
            ExprKind::MakeThunk { body, .. } => {
                value_result(self.mark_active_created_value(Value::Thunk(Thunk::Expr {
                    body: body.as_ref().clone(),
                    env: env.clone(),
                })))
            }
            ExprKind::ForceThunk { target, thunk, .. } => {
                let target_value = target.value.clone();
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
            ExprKind::FunctionAdapter {
                source,
                target,
                function,
                hygiene,
            } => {
                let function = self.eval_expr(function, env)?;
                let source = source.clone();
                let target = target.clone();
                let hygiene = hygiene.clone();
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
            ExprKind::MarkerFrame { path, body } => {
                let body = body.as_ref().clone();
                let mut frame_env = env.clone();
                let id = self.fresh_guard_id();
                let markers = stack_handler_markers(id, path.clone());
                self.with_stack_handler_frame(markers, path.clone(), move |runtime| {
                    runtime.eval_expr(&body, &mut frame_env)
                })
            }
            ExprKind::Apply(callee, arg) => {
                let arg = arg.as_ref().clone();
                let env_for_arg = env.clone();
                let callee = self.eval_expr(callee, env)?;
                self.continue_with(callee, move |runtime, callee| {
                    let mut env = env_for_arg.clone();
                    let arg_result = runtime.eval_expr(&arg, &mut env)?;
                    runtime.continue_with(arg_result, move |runtime, arg| {
                        runtime.apply_value(callee.clone(), arg)
                    })
                })
            }
            ExprKind::RefSet(_, _) => Err(RuntimeError::UnsupportedExpr {
                feature: "ref set".to_string(),
            }),
            ExprKind::Lambda(param, body) => {
                value_result(self.mark_active_created_value(Value::Closure(Closure {
                    param: param.clone(),
                    body: body.as_ref().clone(),
                    env: env.clone(),
                })))
            }
            ExprKind::Tuple(items) => self.eval_tuple(items.clone(), env.clone()),
            ExprKind::Record { fields, spread } => {
                self.eval_record(fields.clone(), spread.clone(), env.clone())
            }
            ExprKind::PolyVariant { tag, payloads } => {
                self.eval_poly_variant(tag.clone(), payloads.clone(), env.clone())
            }
            ExprKind::Select {
                base,
                name,
                resolution,
            } => self.eval_select(base, name, *resolution, env),
            ExprKind::Case { scrutinee, arms } => {
                let scrutinee = self.eval_expr(scrutinee, env)?;
                let arms = arms.clone();
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
            ExprKind::Catch { body, arms } => self.eval_catch(body, arms, env),
            ExprKind::Block(block) => self.eval_block(block, env),
        }
    }

    pub(super) fn eval_record(
        &mut self,
        fields: Vec<RecordField>,
        spread: RecordSpread<Box<Expr>>,
        env: CapturedEnv,
    ) -> RuntimeResult<'a> {
        match spread {
            RecordSpread::None => self.eval_record_fields(fields, env, Vec::new(), 0),
            RecordSpread::Head(expr) => {
                let mut spread_env = env.clone();
                let spread = self.eval_expr(&expr, &mut spread_env)?;
                self.continue_with(spread, move |runtime, spread| {
                    let spread_fields = runtime.expect_record(spread)?;
                    runtime.eval_record_fields(fields.clone(), env.clone(), spread_fields, 0)
                })
            }
            RecordSpread::Tail(expr) => {
                let fields_result = self.eval_record_fields(fields, env.clone(), Vec::new(), 0)?;
                self.continue_with(fields_result, move |runtime, fields| {
                    let fields = runtime.expect_record(fields)?;
                    let mut spread_env = env.clone();
                    let spread = runtime.eval_expr(&expr, &mut spread_env)?;
                    runtime.continue_with(spread, move |runtime, spread| {
                        let mut fields = fields.clone();
                        fields.extend(runtime.expect_record(spread)?);
                        value_result(Value::Record(fields))
                    })
                })
            }
        }
    }

    pub(super) fn eval_tuple(&mut self, items: Vec<Expr>, env: CapturedEnv) -> RuntimeResult<'a> {
        self.eval_tuple_items(items, env, Vec::new(), 0)
    }

    pub(super) fn eval_tuple_items(
        &mut self,
        items: Vec<Expr>,
        env: CapturedEnv,
        values: Vec<Value>,
        index: usize,
    ) -> RuntimeResult<'a> {
        if index >= items.len() {
            return value_result(Value::Tuple(values));
        }

        let item = items[index].clone();
        let mut item_env = env.clone();
        let result = self.eval_expr(&item, &mut item_env)?;
        self.continue_with(result, move |runtime, value| {
            let mut values = values.clone();
            values.push(value);
            runtime.eval_tuple_items(items.clone(), env.clone(), values, index + 1)
        })
    }

    pub(super) fn eval_poly_variant(
        &mut self,
        tag: String,
        payloads: Vec<Expr>,
        env: CapturedEnv,
    ) -> RuntimeResult<'a> {
        self.eval_poly_variant_payloads(tag, payloads, env, Vec::new(), 0)
    }

    pub(super) fn eval_poly_variant_payloads(
        &mut self,
        tag: String,
        payloads: Vec<Expr>,
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

        let payload = payloads[index].clone();
        let mut payload_env = env.clone();
        let result = self.eval_expr(&payload, &mut payload_env)?;
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
        let result = self.eval_expr(&field.value, &mut field_env)?;
        self.continue_with(result, move |runtime, value| {
            let mut values = values.clone();
            values.push(ValueField {
                name: field.name.clone(),
                value,
            });
            runtime.eval_record_fields(fields.clone(), env.clone(), values, index + 1)
        })
    }

    pub(super) fn eval_select(
        &mut self,
        base: &Expr,
        name: &str,
        resolution: Option<SelectResolution>,
        env: &mut CapturedEnv,
    ) -> RuntimeResult<'a> {
        let result = self.eval_expr(base, env)?;
        let name = name.to_string();
        self.continue_with(result, move |runtime, base| match resolution {
            Some(SelectResolution::RecordField) => {
                value_result(runtime.project_record_field(base, &name)?)
            }
            Some(SelectResolution::Method { instance }) => {
                let method = runtime.eval_instance(instance)?;
                runtime.apply_value(method, base)
            }
            Some(SelectResolution::TypeclassMethod { member }) => {
                Err(RuntimeError::UnsupportedExpr {
                    feature: format!("typeclass method d{}", member.0),
                })
            }
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
            let body = arm.body.clone();
            let Some(guard) = arm.guard.clone() else {
                return runtime.eval_expr(&body, &mut arm_env);
            };

            let guard_result = runtime.eval_expr(&guard, &mut arm_env)?;
            let scrutinee_for_guard = scrutinee.clone();
            let arms_for_guard = arms.clone();
            let env_for_guard = env.clone();
            runtime.continue_with(guard_result, move |runtime, guard| match guard {
                Value::Bool(true) => runtime.eval_expr(&body, &mut arm_env.clone()),
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
        body: &Expr,
        arms: &[CatchArm],
        env: &mut CapturedEnv,
    ) -> RuntimeResult<'a> {
        let arms = arms.to_vec();
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
            let body = arm.body.clone();
            let Some(guard) = arm.guard.clone() else {
                return runtime.eval_expr(&body, &mut arm_env);
            };

            let guard_result = runtime.eval_expr(&guard, &mut arm_env)?;
            let value_for_guard = value.clone();
            let arms_for_guard = arms.clone();
            let env_for_guard = env.clone();
            runtime.continue_with(guard_result, move |runtime, guard| match guard {
                Value::Bool(true) => runtime.eval_expr(&body, &mut arm_env.clone()),
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
            let skipped_guard = operation_path
                .filter(|path| *path == &request.path)
                .and_then(|path| self.request_guard_for_path(&request, path));
            if operation_path != Some(&request.path) || skipped_guard.is_some() {
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
                let continuation = arm.continuation.clone();
                let guard = arm.guard.clone();
                let body = arm.body.clone();
                if let Some(continuation) = continuation {
                    let continuation_guard = guard.clone();
                    let continuation_body = body.clone();
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
                        let Some(guard) = continuation_guard.clone() else {
                            return runtime.eval_handler_body(&continuation_body, &mut arm_env);
                        };

                        let guard_result = runtime.eval_expr(&guard, &mut arm_env)?;
                        let continuation_body_for_guard = continuation_body.clone();
                        let request_for_guard = request_for_continuation.clone();
                        let arms_for_guard = arms_for_continuation.clone();
                        let env_for_guard = env_for_continuation.clone();
                        runtime.continue_with(guard_result, move |runtime, guard| match guard {
                            Value::Bool(true) => runtime.eval_handler_body(
                                &continuation_body_for_guard,
                                &mut arm_env.clone(),
                            ),
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
                    return runtime.eval_handler_body(&body, &mut arm_env);
                };

                let guard_result = runtime.eval_expr(&guard, &mut arm_env)?;
                let body_for_guard = body.clone();
                let request_for_guard = request.clone();
                let arms_for_guard = arms.clone();
                let env_for_guard = env.clone();
                runtime.continue_with(guard_result, move |runtime, guard| match guard {
                    Value::Bool(true) => {
                        runtime.eval_handler_body(&body_for_guard, &mut arm_env.clone())
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

        let arms_for_resume = arms.clone();
        let env_for_resume = env.clone();
        let resume = request.resume.clone();
        Ok(EvalResult::Request(Request {
            path: request.path,
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
        body: &Expr,
        env: &mut CapturedEnv,
    ) -> RuntimeResult<'a> {
        let result = self.eval_expr(body, env)?;
        self.continue_with(result, |runtime, value| runtime.force_value_if_thunk(value))
    }

    pub(super) fn eval_block(&mut self, block: &Block, env: &mut CapturedEnv) -> RuntimeResult<'a> {
        self.eval_block_parts(
            block.stmts.clone(),
            block.tail.as_deref().cloned(),
            env.clone(),
        )
    }

    pub(super) fn eval_block_parts(
        &mut self,
        stmts: Vec<Stmt>,
        tail: Option<Expr>,
        env: CapturedEnv,
    ) -> RuntimeResult<'a> {
        self.eval_block_step(stmts, tail, env, 0, Value::Unit)
    }

    pub(super) fn eval_block_step(
        &mut self,
        stmts: Vec<Stmt>,
        tail: Option<Expr>,
        mut env: CapturedEnv,
        index: usize,
        last: Value,
    ) -> RuntimeResult<'a> {
        if index >= stmts.len() {
            if let Some(tail) = tail {
                return self.eval_expr(&tail, &mut env);
            }
            return value_result(last);
        }

        match stmts[index].clone() {
            Stmt::Let(_, pat, expr) => {
                let result = self.eval_expr(&expr, &mut env)?;
                self.continue_with(result, move |runtime, value| {
                    let value = recursive_let_value(&pat, value);
                    let bind = runtime.bind_pat(pat.clone(), value.clone(), env.clone())?;
                    let stmts_for_bind = stmts.clone();
                    let tail_for_bind = tail.clone();
                    let value_for_bind = value.clone();
                    runtime.continue_bind(bind, move |runtime, matched, next_env| {
                        if !matched {
                            return Err(RuntimeError::PatternMismatch);
                        }
                        runtime.eval_block_step(
                            stmts_for_bind.clone(),
                            tail_for_bind.clone(),
                            next_env,
                            index + 1,
                            value_for_bind.clone(),
                        )
                    })
                })
            }
            Stmt::Expr(expr) => {
                let result = self.eval_expr(&expr, &mut env)?;
                self.continue_with(result, move |runtime, value| {
                    runtime.eval_block_step(
                        stmts.clone(),
                        tail.clone(),
                        env.clone(),
                        index + 1,
                        value,
                    )
                })
            }
            Stmt::Module(_, module_stmts) => {
                let result = self.eval_block_parts(module_stmts, None, env.clone())?;
                self.continue_with(result, move |runtime, value| {
                    runtime.eval_block_step(
                        stmts.clone(),
                        tail.clone(),
                        env.clone(),
                        index + 1,
                        value,
                    )
                })
            }
        }
    }
}
