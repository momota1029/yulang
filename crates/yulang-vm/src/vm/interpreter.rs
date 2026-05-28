use super::*;

pub(super) struct VmInterpreter<'m> {
    module: &'m Module,
    bindings: HashMap<typed_ir::Path, usize>,
    next_guard_id: u64,
    guard_stack: GuardStack,
    eval_depth: usize,
    profile: VmProfile,
}

impl<'m> VmInterpreter<'m> {
    pub(super) fn new(module: &'m Module) -> Self {
        Self {
            module,
            bindings: module
                .bindings
                .iter()
                .enumerate()
                .map(|(index, binding)| (binding.name.clone(), index))
                .collect(),
            next_guard_id: 0,
            guard_stack: GuardStack::default(),
            eval_depth: 0,
            profile: VmProfile::default(),
        }
    }

    pub(super) fn profile(&self) -> VmProfile {
        self.profile
    }

    pub(super) fn eval_root_expr(&mut self, index: usize) -> Result<VmResult, VmError> {
        let expr = self
            .module
            .root_exprs
            .get(index)
            .ok_or(VmError::MissingRootExpr(index))?;
        let result = self.eval_expr(expr, &Env::new())?;
        self.normalize_root_result(result)
    }

    fn normalize_root_result(&mut self, mut result: VmResult) -> Result<VmResult, VmError> {
        loop {
            result = match result {
                VmResult::Value(VmValue::Thunk(thunk)) => self.bind_here(VmValue::Thunk(thunk))?,
                VmResult::Request(request) => match self.propagate_request(request)? {
                    VmResult::Request(request) => return Ok(VmResult::Request(request)),
                    result => result,
                },
                result => return Ok(result),
            };
        }
    }

    pub(super) fn eval_expr(&mut self, expr: &Expr, env: &Env) -> Result<VmResult, VmError> {
        self.profile.eval_expr_calls += 1;
        self.eval_depth += 1;
        self.profile.max_eval_depth = self.profile.max_eval_depth.max(self.eval_depth);
        let result = self.eval_expr_inner(expr, env);
        self.eval_depth -= 1;
        result
    }

    fn eval_expr_inner(&mut self, expr: &Expr, env: &Env) -> Result<VmResult, VmError> {
        match &expr.kind {
            ExprKind::Var(path) => self.eval_var(path, env),
            ExprKind::EffectOp(path) => Ok(VmResult::Value(VmValue::EffectOp(path.clone()))),
            ExprKind::PrimitiveOp(typed_ir::PrimitiveOp::YadaYada) => Err(VmError::YadaYada),
            ExprKind::PrimitiveOp(op) => Ok(VmResult::Value(VmValue::PrimitiveOp(Rc::new(
                VmPrimitive {
                    op: *op,
                    args: Vec::new(),
                },
            )))),
            ExprKind::Lit(lit) => Ok(VmResult::Value(value_from_lit(lit))),
            ExprKind::Lambda {
                param,
                param_effect_annotation,
                param_function_allowed_effects,
                body,
                ..
            } => {
                let (param_ty, ret) = match &expr.ty {
                    Type::Fun { param, ret } => (param.as_ref().clone(), ret.as_ref().clone()),
                    _ => (Type::Value(typed_ir::Type::Any), body.ty.clone()),
                };
                Ok(VmResult::Value(VmValue::Closure(Rc::new(VmClosure {
                    param: param.clone(),
                    param_ty: lambda_param_type(
                        param_ty,
                        param_effect_annotation.as_ref(),
                        param_function_allowed_effects.as_ref(),
                    ),
                    body: (**body).clone(),
                    ret,
                    env: env.clone(),
                    guard_stack: self.guard_stack.clone(),
                    self_name: None,
                }))))
            }
            ExprKind::Apply { callee, arg, .. } => {
                let delay_arg = expects_thunk_arg(&callee.ty);
                trace_apply_eval_entry("apply_eval.entry", &callee.kind, &arg.kind, delay_arg);
                trace_apply_callee_ty(&callee.kind, &callee.ty);
                match self.eval_expr(callee, env)? {
                    VmResult::Value(callee) => {
                        trace_apply_eval_callee_ready(&callee);
                        self.continue_apply_arg(callee, arg, env, delay_arg)
                    }
                    VmResult::Request(request) => Ok(VmResult::Request(push_frame(
                        request,
                        Frame::ApplyCallee {
                            arg: (**arg).clone(),
                            env: env.clone(),
                            delay_arg,
                        },
                    ))),
                }
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                let result = self.eval_expr(cond, env)?;
                self.continue_if_result(result, then_branch, else_branch, env)
            }
            ExprKind::Tuple(items) => self.eval_tuple(
                Vec::new(),
                items.clone(),
                env.clone(),
                tuple_type_forces_items(&expr.ty),
            ),
            ExprKind::Record { fields, spread } => self.eval_record(fields, spread, env),
            ExprKind::Variant { tag, value } => {
                if let Some(value) = value {
                    let result = self.eval_expr(value, env)?;
                    let result = self.force_value_result(result, true)?;
                    return self.continue_variant_value(tag.clone(), result);
                }
                Ok(VmResult::Value(VmValue::Variant {
                    tag: tag.clone(),
                    value: None,
                }))
            }
            ExprKind::Select { base, field } => match self.eval_expr(base, env)? {
                VmResult::Value(value) => self.select_field(value, field),
                VmResult::Request(request) => Ok(VmResult::Request(push_frame(
                    request,
                    Frame::Select {
                        field: field.clone(),
                    },
                ))),
            },
            ExprKind::Match {
                scrutinee, arms, ..
            } => match self.eval_expr(scrutinee, env)? {
                VmResult::Value(value) => self.eval_match(value, arms, env),
                VmResult::Request(request) => Ok(VmResult::Request(push_frame(
                    request,
                    Frame::Match {
                        arms: arms.clone(),
                        env: env.clone(),
                    },
                ))),
            },
            ExprKind::Block { stmts, tail } => {
                self.eval_block(stmts.clone(), tail.as_deref().cloned(), env.clone())
            }
            ExprKind::Handle {
                body,
                arms,
                evidence,
                ..
            } => self.eval_handle(body, arms, &Type::value(evidence.result.clone()), env),
            ExprKind::BindHere { expr } => match self.eval_expr(expr, env)? {
                VmResult::Value(value) => self.bind_here(value),
                VmResult::Request(request) => {
                    Ok(VmResult::Request(push_frame(request, Frame::BindHere)))
                }
            },
            ExprKind::Thunk { expr, .. } => Ok(VmResult::Value(VmValue::Thunk(Rc::new(VmThunk {
                body: ThunkBody::Expr((**expr).clone()),
                env: env.clone(),
                guard_stack: self.guard_stack.clone(),
                blocked: Vec::new(),
            })))),
            ExprKind::LocalPushId { id: var, body } => {
                let id = self.fresh_guard_id();
                let parent = self.guard_stack.clone();
                self.guard_stack = parent.push(GuardEntry { var: *var, id });
                let result = self.eval_expr(body, env);
                self.guard_stack = parent.clone();
                match result? {
                    VmResult::Request(request) => Ok(VmResult::Request(push_frame(
                        request,
                        Frame::LocalPushId { parent },
                    ))),
                    value => Ok(value),
                }
            }
            ExprKind::PeekId => {
                let id = self.guard_stack.peek().ok_or(VmError::UnsupportedFindId)?;
                Ok(VmResult::Value(VmValue::EffectId(id)))
            }
            ExprKind::FindId { id } => {
                Ok(VmResult::Value(VmValue::Bool(self.find_effect_id(*id)?)))
            }
            ExprKind::AddId {
                id,
                allowed,
                active,
                thunk,
            } => {
                let id = self.eval_effect_id(*id)?;
                let result = self.eval_expr(thunk, env)?;
                let VmResult::Value(VmValue::Thunk(thunk)) = result else {
                    return Ok(match result {
                        VmResult::Request(request) => {
                            let blocked = [BlockedEffect {
                                guard_id: id,
                                allowed: allowed.clone(),
                                active: *active,
                            }];
                            let request = if *active {
                                mark_request_with_active_blocked(request, &blocked)
                            } else {
                                mark_request_with_blocked(request, &blocked)
                            };
                            VmResult::Request(request)
                        }
                        other => other,
                    });
                };
                let mut thunk = (*thunk).clone();
                thunk.blocked.push(BlockedEffect {
                    guard_id: id,
                    allowed: allowed.clone(),
                    active: *active,
                });
                Ok(VmResult::Value(VmValue::Thunk(Rc::new(thunk))))
            }
            ExprKind::Coerce { to, expr, .. } => match self.eval_expr(expr, env)? {
                VmResult::Value(value) => Ok(VmResult::Value(cast_value(value, to))),
                VmResult::Request(request) => Ok(VmResult::Request(push_frame(
                    request,
                    Frame::Coerce { to: to.clone() },
                ))),
            },
            ExprKind::Pack { expr, .. } => self.eval_expr(expr, env),
        }
    }

    pub(super) fn eval_var(
        &mut self,
        path: &typed_ir::Path,
        env: &Env,
    ) -> Result<VmResult, VmError> {
        if let Some(value) = env.get(path) {
            trace_eval_var("env_hit", path, &value);
            return Ok(VmResult::Value(value.clone()));
        }
        if let Some(index) = self.bindings.get(path).copied() {
            trace_eval_var_binding("binding_lookup", path);
            let binding = &self.module.bindings[index];
            return self.eval_expr(&binding.body, &Env::new());
        }
        if path.segments.len() > 1 {
            trace_eval_var_effect_op("effect_op", path);
            return Ok(VmResult::Value(VmValue::EffectOp(path.clone())));
        }
        Err(VmError::UnboundVariable(path.clone()))
    }

    pub(super) fn continue_if_result(
        &mut self,
        result: VmResult,
        then_branch: &Expr,
        else_branch: &Expr,
        env: &Env,
    ) -> Result<VmResult, VmError> {
        match result {
            VmResult::Value(VmValue::Thunk(thunk)) => {
                match self.bind_here(VmValue::Thunk(thunk))? {
                    VmResult::Value(value) => {
                        self.continue_if_value(value, then_branch, else_branch, env)
                    }
                    VmResult::Request(request) => Ok(VmResult::Request(push_frame(
                        request,
                        Frame::If {
                            then_branch: then_branch.clone(),
                            else_branch: else_branch.clone(),
                            env: env.clone(),
                        },
                    ))),
                }
            }
            VmResult::Value(value) => self.continue_if_value(value, then_branch, else_branch, env),
            VmResult::Request(request) => Ok(VmResult::Request(push_frame(
                request,
                Frame::If {
                    then_branch: then_branch.clone(),
                    else_branch: else_branch.clone(),
                    env: env.clone(),
                },
            ))),
        }
    }

    pub(super) fn continue_if_value(
        &mut self,
        value: VmValue,
        then_branch: &Expr,
        else_branch: &Expr,
        env: &Env,
    ) -> Result<VmResult, VmError> {
        match value {
            VmValue::Bool(true) => self.eval_expr(then_branch, env),
            VmValue::Bool(false) => self.eval_expr(else_branch, env),
            other => Err(VmError::ExpectedBool(other)),
        }
    }

    fn continue_if_value_frame(
        &mut self,
        value: VmValue,
        then_branch: Expr,
        else_branch: Expr,
        env: Env,
    ) -> Result<VmResult, VmError> {
        match value {
            VmValue::Thunk(thunk) => match self.bind_here(VmValue::Thunk(thunk))? {
                VmResult::Value(value) => {
                    self.continue_if_value_frame(value, then_branch, else_branch, env)
                }
                VmResult::Request(request) => Ok(VmResult::Request(push_frame(
                    request,
                    Frame::If {
                        then_branch,
                        else_branch,
                        env,
                    },
                ))),
            },
            VmValue::Bool(true) => self.eval_expr(&then_branch, &env),
            VmValue::Bool(false) => self.eval_expr(&else_branch, &env),
            other => Err(VmError::ExpectedBool(other)),
        }
    }

    pub(super) fn eval_value(&mut self, expr: &Expr, env: &Env) -> Result<VmValue, VmError> {
        match self.eval_expr(expr, env)? {
            VmResult::Value(value) => Ok(value),
            VmResult::Request(request) => Err(VmError::UnexpectedRequest(request.effect)),
        }
    }

    pub(super) fn bind_pattern(
        &mut self,
        pattern: &Pattern,
        value: VmValue,
        env: &mut Env,
    ) -> Result<(), VmError> {
        bind_pattern_with_defaults(pattern, value, env, &mut |default, env| {
            self.eval_pattern_default(default, env)
        })
    }

    fn eval_pattern_default(&mut self, expr: &Expr, env: &Env) -> Result<VmValue, VmError> {
        match self.eval_expr(expr, env)? {
            VmResult::Value(VmValue::Thunk(thunk)) => {
                match self.bind_here(VmValue::Thunk(thunk))? {
                    VmResult::Value(value) => Ok(value),
                    VmResult::Request(request) => Err(VmError::UnexpectedRequest(request.effect)),
                }
            }
            VmResult::Value(value) => Ok(value),
            VmResult::Request(request) => Err(VmError::UnexpectedRequest(request.effect)),
        }
    }

    pub(super) fn bind_here(&mut self, value: VmValue) -> Result<VmResult, VmError> {
        trace_bind_here_entry(&value);
        let parent = self.guard_stack.clone();
        let mut value = value;
        let mut outer_thunks = Vec::new();
        let result = loop {
            let VmValue::Thunk(thunk) = value else {
                break Ok(VmResult::Value(value));
            };
            self.guard_stack = thunk.guard_stack.clone();
            match &thunk.body {
                ThunkBody::Value(next) => {
                    value = next.clone();
                }
                ThunkBody::Expr(expr) => match self.eval_expr(expr, &thunk.env)? {
                    VmResult::Value(next @ VmValue::Thunk(_)) => {
                        outer_thunks.push(thunk.clone());
                        value = next;
                    }
                    VmResult::Request(request) => {
                        let mut request = push_thunk_expr_frames(request, &thunk);
                        for outer in outer_thunks.iter().rev() {
                            request = push_thunk_boundary_frame(request, outer);
                        }
                        break Ok(VmResult::Request(request));
                    }
                    other => break Ok(other),
                },
                ThunkBody::Emit { effect, payload } => {
                    let mut request = push_thunk_boundary_frame(
                        VmRequest {
                            effect: effect.clone(),
                            payload: payload.clone(),
                            continuation: VmContinuation::new(self.guard_stack.clone()),
                            blocked_id: None,
                        },
                        &thunk,
                    );
                    for outer in outer_thunks.iter().rev() {
                        request = push_thunk_boundary_frame(request, outer);
                    }
                    break Ok(VmResult::Request(request));
                }
            }
        };
        self.guard_stack = parent;
        result
    }

    pub(super) fn continue_apply_arg(
        &mut self,
        callee: VmValue,
        arg: &Expr,
        env: &Env,
        delay_arg: bool,
    ) -> Result<VmResult, VmError> {
        if let VmValue::Thunk(_) = callee {
            return self.force_apply_callee(callee, arg.clone(), env.clone(), delay_arg);
        }
        let delay_arg = delay_arg || callee_expects_thunk_arg(&callee);
        if delay_arg {
            return self.apply(
                callee,
                VmValue::Thunk(Rc::new(VmThunk {
                    body: ThunkBody::Expr(arg.clone()),
                    env: env.clone(),
                    guard_stack: self.guard_stack.clone(),
                    blocked: Vec::new(),
                })),
            );
        }
        match self.eval_expr(arg, env)? {
            VmResult::Value(arg) => self.apply(callee, arg),
            VmResult::Request(request) => Ok(VmResult::Request(push_frame(
                request,
                Frame::ApplyArg { callee },
            ))),
        }
    }

    pub(super) fn force_apply_callee(
        &mut self,
        callee: VmValue,
        arg: Expr,
        env: Env,
        delay_arg: bool,
    ) -> Result<VmResult, VmError> {
        match self.bind_here(callee)? {
            VmResult::Value(callee) => self.continue_apply_arg(callee, &arg, &env, delay_arg),
            VmResult::Request(request) => Ok(VmResult::Request(push_frame(
                request,
                Frame::ApplyCallee {
                    arg,
                    env,
                    delay_arg,
                },
            ))),
        }
    }

    pub(super) fn apply(&mut self, callee: VmValue, arg: VmValue) -> Result<VmResult, VmError> {
        trace_apply_entry(&callee, &arg);
        match callee {
            VmValue::Closure(callee) => {
                if closure_param_forces_thunk_arg(&callee.param_ty)
                    && matches!(arg, VmValue::Thunk(_))
                {
                    return self.force_apply_arg(VmValue::Closure(callee), arg);
                }
                let mut env = callee.env.clone();
                if let Some(self_name) = &callee.self_name {
                    env.insert(self_name.clone(), VmValue::Closure(callee.clone()));
                }
                env.insert(typed_ir::Path::from_name(callee.param.clone()), arg);
                let parent_guard_stack = self.guard_stack.clone();
                self.guard_stack = parent_guard_stack.overlay_newer(&callee.guard_stack);
                let result = self.eval_expr(&callee.body, &env)?;
                self.guard_stack = parent_guard_stack.clone();
                if let VmResult::Request(request) = result {
                    return Ok(VmResult::Request(push_frame(
                        request,
                        Frame::LocalPushId {
                            parent: parent_guard_stack,
                        },
                    )));
                }
                Ok(wrap_result_for_type(result, &callee.ret))
            }
            VmValue::Resume(resume) => self.resume(resume.continuation.clone(), arg),
            VmValue::EffectOp(effect) => Ok(VmResult::Value(VmValue::Thunk(Rc::new(VmThunk {
                body: ThunkBody::Emit {
                    effect,
                    payload: arg,
                },
                env: Env::new(),
                guard_stack: self.guard_stack.clone(),
                blocked: Vec::new(),
            })))),
            VmValue::PrimitiveOp(primitive) => {
                if let VmValue::Thunk(_) = arg {
                    return self.force_apply_arg(VmValue::PrimitiveOp(primitive), arg);
                }
                self.apply_primitive(primitive, arg)
            }
            other => Err(VmError::ExpectedClosure(other)),
        }
    }

    pub(super) fn force_apply_arg(
        &mut self,
        callee: VmValue,
        arg: VmValue,
    ) -> Result<VmResult, VmError> {
        match self.bind_here(arg)? {
            VmResult::Value(arg) => self.apply(callee, arg),
            VmResult::Request(request) => Ok(VmResult::Request(push_frame(
                request,
                Frame::ApplyArg { callee },
            ))),
        }
    }

    pub(super) fn apply_primitive(
        &mut self,
        primitive: Rc<VmPrimitive>,
        arg: VmValue,
    ) -> Result<VmResult, VmError> {
        let mut args = primitive.args.clone();
        args.push(arg);
        if args.len() < primitive_arity(primitive.op) {
            return Ok(VmResult::Value(VmValue::PrimitiveOp(Rc::new(
                VmPrimitive {
                    op: primitive.op,
                    args,
                },
            ))));
        }
        Ok(VmResult::Value(apply_primitive(primitive.op, &args)?))
    }

    pub(super) fn eval_tuple(
        &mut self,
        mut done: Vec<VmValue>,
        mut remaining: Vec<Expr>,
        env: Env,
        force_items: bool,
    ) -> Result<VmResult, VmError> {
        remaining.reverse();
        while let Some(next) = remaining.pop() {
            let result = self.eval_expr(&next, &env)?;
            let result = self.force_value_result(
                result,
                force_items || !matches!(next.ty, Type::Thunk { .. }),
            )?;
            match result {
                VmResult::Value(value) => done.push(value),
                VmResult::Request(request) => {
                    remaining.reverse();
                    return Ok(VmResult::Request(push_frame(
                        request,
                        Frame::Tuple {
                            done,
                            remaining,
                            env,
                            force_items,
                        },
                    )));
                }
            }
        }
        Ok(VmResult::Value(VmValue::Tuple(done)))
    }

    fn force_value_result(&mut self, result: VmResult, force: bool) -> Result<VmResult, VmError> {
        if !force {
            return Ok(result);
        }
        match result {
            VmResult::Value(VmValue::Thunk(thunk)) => self.bind_here(VmValue::Thunk(thunk)),
            result => Ok(result),
        }
    }

    fn continue_tuple_item(
        &mut self,
        mut done: Vec<VmValue>,
        remaining: Vec<Expr>,
        env: Env,
        force_items: bool,
        value: VmValue,
    ) -> Result<VmResult, VmError> {
        if force_items {
            if let VmValue::Thunk(thunk) = value {
                return match self.bind_here(VmValue::Thunk(thunk))? {
                    VmResult::Value(value) => {
                        self.continue_tuple_item(done, remaining, env, force_items, value)
                    }
                    VmResult::Request(request) => Ok(VmResult::Request(push_frame(
                        request,
                        Frame::Tuple {
                            done,
                            remaining,
                            env,
                            force_items,
                        },
                    ))),
                };
            }
        }
        done.push(value);
        self.eval_tuple(done, remaining, env, force_items)
    }

    fn continue_variant_value(
        &mut self,
        tag: typed_ir::Name,
        result: VmResult,
    ) -> Result<VmResult, VmError> {
        match result {
            VmResult::Value(VmValue::Thunk(thunk)) => {
                match self.bind_here(VmValue::Thunk(thunk))? {
                    result @ VmResult::Value(_) => self.continue_variant_value(tag, result),
                    VmResult::Request(request) => Ok(VmResult::Request(push_frame(
                        request,
                        Frame::Variant { tag },
                    ))),
                }
            }
            VmResult::Value(value) => Ok(VmResult::Value(VmValue::Variant {
                tag,
                value: Some(Box::new(value)),
            })),
            VmResult::Request(request) => Ok(VmResult::Request(push_frame(
                request,
                Frame::Variant { tag },
            ))),
        }
    }

    pub(super) fn eval_record(
        &mut self,
        fields: &[RecordExprField],
        spread: &Option<RecordSpreadExpr>,
        env: &Env,
    ) -> Result<VmResult, VmError> {
        let mut values = BTreeMap::new();
        if let Some(spread) = spread {
            let spread_expr = match spread {
                RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => expr,
            };
            let VmValue::Record(base) = self.eval_value(spread_expr, env)? else {
                return Err(VmError::ExpectedRecord(self.eval_value(spread_expr, env)?));
            };
            values.extend(base);
        }
        for field in fields {
            values.insert(field.name.clone(), self.eval_value(&field.value, env)?);
        }
        Ok(VmResult::Value(VmValue::Record(values)))
    }

    pub(super) fn select_field(
        &self,
        value: VmValue,
        field: &typed_ir::Name,
    ) -> Result<VmResult, VmError> {
        let VmValue::Record(fields) = value else {
            return Err(VmError::ExpectedRecord(value));
        };
        fields
            .get(field)
            .cloned()
            .map(VmResult::Value)
            .ok_or(VmError::PatternMismatch)
    }

    pub(super) fn eval_match(
        &mut self,
        value: VmValue,
        arms: &[MatchArm],
        env: &Env,
    ) -> Result<VmResult, VmError> {
        let value = match value {
            VmValue::Thunk(thunk) => match self.bind_here(VmValue::Thunk(thunk))? {
                VmResult::Value(value) => value,
                VmResult::Request(request) => {
                    return Ok(VmResult::Request(push_frame(
                        request,
                        Frame::Match {
                            arms: arms.to_vec(),
                            env: env.clone(),
                        },
                    )));
                }
            },
            value => value,
        };
        for arm in arms {
            let mut arm_env = env.clone();
            if self
                .bind_pattern(&arm.pattern, value.clone(), &mut arm_env)
                .is_err()
            {
                continue;
            }
            if let Some(guard) = &arm.guard {
                match self.eval_value(guard, &arm_env)? {
                    VmValue::Bool(true) => {}
                    VmValue::Bool(false) => continue,
                    other => return Err(VmError::ExpectedBool(other)),
                }
            }
            return self.eval_expr(&arm.body, &arm_env);
        }
        Err(VmError::PatternMismatch)
    }

    fn continue_block_expr(
        &mut self,
        value: VmValue,
        remaining: Vec<Stmt>,
        tail: Option<Expr>,
        env: Env,
    ) -> Result<VmResult, VmError> {
        match value {
            VmValue::Thunk(thunk) => match self.bind_here(VmValue::Thunk(thunk))? {
                VmResult::Value(_) => self.eval_block(remaining, tail, env),
                VmResult::Request(request) => Ok(VmResult::Request(push_frame(
                    request,
                    Frame::BlockExpr {
                        remaining,
                        tail,
                        env,
                    },
                ))),
            },
            _ => self.eval_block(remaining, tail, env),
        }
    }

    pub(super) fn eval_block(
        &mut self,
        mut stmts: Vec<Stmt>,
        tail: Option<Expr>,
        mut env: Env,
    ) -> Result<VmResult, VmError> {
        stmts.reverse();
        while let Some(stmt) = stmts.pop() {
            match stmt {
                Stmt::Let { pattern, value } => match self.eval_expr(&value, &env)? {
                    VmResult::Value(VmValue::Thunk(thunk)) => {
                        match self.bind_here(VmValue::Thunk(thunk))? {
                            VmResult::Value(mut value) => {
                                value = make_recursive_local_value(&pattern, value);
                                self.bind_pattern(&pattern, value, &mut env)?;
                            }
                            VmResult::Request(request) => {
                                stmts.reverse();
                                return Ok(VmResult::Request(push_frame(
                                    request,
                                    Frame::BlockLet {
                                        pattern,
                                        remaining: stmts,
                                        tail,
                                        env,
                                    },
                                )));
                            }
                        }
                    }
                    VmResult::Value(mut value) => {
                        value = make_recursive_local_value(&pattern, value);
                        self.bind_pattern(&pattern, value, &mut env)?;
                    }
                    VmResult::Request(request) => {
                        stmts.reverse();
                        return Ok(VmResult::Request(push_frame(
                            request,
                            Frame::BlockLet {
                                pattern,
                                remaining: stmts,
                                tail,
                                env,
                            },
                        )));
                    }
                },
                Stmt::Expr(expr) => match self.eval_expr(&expr, &env)? {
                    VmResult::Value(VmValue::Thunk(thunk)) => {
                        match self.bind_here(VmValue::Thunk(thunk))? {
                            VmResult::Value(_) => {}
                            VmResult::Request(request) => {
                                stmts.reverse();
                                return Ok(VmResult::Request(push_frame(
                                    request,
                                    Frame::BlockExpr {
                                        remaining: stmts,
                                        tail,
                                        env,
                                    },
                                )));
                            }
                        }
                    }
                    VmResult::Value(_) => {}
                    VmResult::Request(request) => {
                        stmts.reverse();
                        return Ok(VmResult::Request(push_frame(
                            request,
                            Frame::BlockExpr {
                                remaining: stmts,
                                tail,
                                env,
                            },
                        )));
                    }
                },
                Stmt::Module { def, body } => {
                    let value = self.eval_value(&body, &env)?;
                    env.insert(def, value);
                }
            }
        }
        match tail {
            Some(tail) => self.eval_expr(&tail, &env),
            None => Ok(VmResult::Value(VmValue::Unit)),
        }
    }

    pub(super) fn eval_handle(
        &mut self,
        body: &Expr,
        arms: &[HandleArm],
        expected_ty: &Type,
        env: &Env,
    ) -> Result<VmResult, VmError> {
        let id = self.fresh_guard_id();
        let handler_guard_stack = self.guard_stack.clone();
        let result = match self.eval_expr(body, env)? {
            VmResult::Value(VmValue::Thunk(thunk)) => self.bind_here(VmValue::Thunk(thunk))?,
            other => other,
        };
        match result {
            VmResult::Value(value) => self.handle_value(value, arms, env, expected_ty),
            VmResult::Request(request) => {
                trace_handle_push("eval_handle.push", id, &request);
                let request = push_frame(
                    request,
                    Frame::Handle {
                        id,
                        arms: arms.to_vec(),
                        env: env.clone(),
                        guard_stack: handler_guard_stack.clone(),
                        expected_ty: expected_ty.clone(),
                    },
                );
                self.propagate_request(request)
            }
        }
    }

    pub(super) fn handle_value(
        &mut self,
        value: VmValue,
        arms: &[HandleArm],
        env: &Env,
        expected_ty: &Type,
    ) -> Result<VmResult, VmError> {
        for arm in arms.iter().filter(|arm| arm.effect.segments.is_empty()) {
            let mut arm_env = env.clone();
            if self
                .bind_pattern(&arm.payload, value.clone(), &mut arm_env)
                .is_err()
            {
                continue;
            }
            let result = self.eval_expr(&arm.body, &arm_env)?;
            return self.force_handle_result_for_type(result, expected_ty);
        }
        Ok(VmResult::Value(value))
    }

    pub(super) fn handle_request(
        &mut self,
        request: VmRequest,
        id: u64,
        arms: &[HandleArm],
        env: &Env,
        handler_guard_stack: &GuardStack,
        expected_ty: &Type,
    ) -> Result<VmResult, VmError> {
        if request_is_blocked_by_stack(&request, handler_guard_stack) {
            trace_handle_request_outcome("blocked_by_stack", id, &request.effect);
            return Ok(VmResult::Request(request));
        }
        let Some((arm_index, arm)) = arms
            .iter()
            .enumerate()
            .find(|(_, arm)| effect_operation_path_matches(&arm.effect, &request.effect))
        else {
            let arm_effects: Vec<String> =
                arms.iter().map(|arm| format!("{:?}", arm.effect)).collect();
            trace_handle_request_arm_miss(id, &request.effect, &arm_effects);
            return Ok(VmResult::Request(request));
        };
        trace_handle_request_outcome("matched", id, &request.effect);
        let remaining_arms = arms[arm_index + 1..].to_vec();
        let outer = request.continuation.clone().outside_handle(id);
        let payload = request.payload.clone();
        if handle_payload_forces_thunk(&arm.payload, &payload) {
            let previous = std::mem::replace(&mut self.guard_stack, handler_guard_stack.clone());
            let payload_result = self.bind_here(payload);
            self.guard_stack = previous;
            let resume = arm.resume.as_ref().map(|resume| resume.name.clone());
            return match payload_result? {
                VmResult::Value(payload) => self.continue_handle_payload(
                    payload,
                    request,
                    outer,
                    id,
                    remaining_arms,
                    env.clone(),
                    handler_guard_stack.clone(),
                    arm.payload.clone(),
                    resume,
                    arm.guard.clone(),
                    arm.body.clone(),
                    expected_ty.clone(),
                ),
                VmResult::Request(mut payload_request) => {
                    let payload_scope_frames = request.continuation.frames.clone();
                    payload_request = push_frame(payload_request, Frame::HandlePayload { request });
                    prepend_frames(&mut payload_request.continuation, payload_scope_frames);
                    self.propagate_request(payload_request)
                }
            };
        }
        self.continue_handle_payload(
            payload,
            request,
            outer,
            id,
            remaining_arms,
            env.clone(),
            handler_guard_stack.clone(),
            arm.payload.clone(),
            arm.resume.as_ref().map(|resume| resume.name.clone()),
            arm.guard.clone(),
            arm.body.clone(),
            expected_ty.clone(),
        )
    }

    pub(super) fn continue_handle_payload(
        &mut self,
        payload: VmValue,
        mut request: VmRequest,
        outer: VmContinuation,
        id: u64,
        arms: Vec<HandleArm>,
        env: Env,
        handler_guard_stack: GuardStack,
        payload_pattern: Pattern,
        resume: Option<typed_ir::Name>,
        guard: Option<Expr>,
        body: Expr,
        expected_ty: Type,
    ) -> Result<VmResult, VmError> {
        request.payload = payload.clone();
        let mut arm_env = env.clone();
        self.bind_pattern(&payload_pattern, payload, &mut arm_env)?;
        if let Some(resume) = resume {
            arm_env.insert(
                typed_ir::Path::from_name(resume),
                VmValue::Resume(Rc::new(VmResume {
                    continuation: request.continuation.clone().inside_handle(id),
                })),
            );
        }
        if let Some(guard) = &guard {
            let previous = std::mem::replace(&mut self.guard_stack, handler_guard_stack.clone());
            let guard_result = self.eval_expr(guard, &arm_env);
            self.guard_stack = previous;
            return match guard_result? {
                VmResult::Value(guard) => self.continue_handle_guard(
                    guard,
                    request,
                    outer,
                    id,
                    arms,
                    env,
                    handler_guard_stack,
                    arm_env,
                    body,
                    expected_ty,
                ),
                VmResult::Request(guard_request) => Ok(VmResult::Request(push_frame(
                    guard_request,
                    Frame::HandleGuard {
                        id,
                        request,
                        outer,
                        handler_guard_stack,
                        arms,
                        env,
                        arm_env,
                        body,
                        expected_ty,
                    },
                ))),
            };
        }
        let previous = std::mem::replace(&mut self.guard_stack, handler_guard_stack.clone());
        let result = self.eval_expr(&body, &arm_env);
        self.guard_stack = previous;
        let result = result?;
        self.continue_handle_result_for_type(result, outer, &expected_ty)
    }

    pub(super) fn continue_handle_guard(
        &mut self,
        guard: VmValue,
        request: VmRequest,
        outer: VmContinuation,
        id: u64,
        arms: Vec<HandleArm>,
        env: Env,
        handler_guard_stack: GuardStack,
        arm_env: Env,
        body: Expr,
        expected_ty: Type,
    ) -> Result<VmResult, VmError> {
        match guard {
            VmValue::Bool(true) => {
                let previous =
                    std::mem::replace(&mut self.guard_stack, handler_guard_stack.clone());
                let result = self.eval_expr(&body, &arm_env);
                self.guard_stack = previous;
                let result = result?;
                self.continue_handle_result_for_type(result, outer, &expected_ty)
            }
            VmValue::Bool(false) => {
                self.handle_request(request, id, &arms, &env, &handler_guard_stack, &expected_ty)
            }
            other => Err(VmError::ExpectedBool(other)),
        }
    }

    pub(super) fn resume(
        &mut self,
        mut continuation: VmContinuation,
        mut value: VmValue,
    ) -> Result<VmResult, VmError> {
        let previous = std::mem::replace(&mut self.guard_stack, continuation.guard_stack.clone());
        self.profile.max_continuation_frames = self
            .profile
            .max_continuation_frames
            .max(continuation.frames.len());
        let result = loop {
            let Some(frame) = continuation.frames.pop() else {
                break Ok(VmResult::Value(value));
            };
            self.profile.continuation_steps += 1;
            self.profile.max_continuation_frames = self
                .profile
                .max_continuation_frames
                .max(continuation.frames.len());
            match self.apply_frame(frame, &mut continuation, value)? {
                VmResult::Value(next) => {
                    value = next;
                }
                VmResult::Request(mut request) => {
                    prepend_frames(&mut request.continuation, continuation.frames);
                    break self.propagate_request(request);
                }
            }
        };
        self.guard_stack = previous;
        result
    }

    pub(super) fn apply_frame(
        &mut self,
        frame: Frame,
        continuation: &mut VmContinuation,
        value: VmValue,
    ) -> Result<VmResult, VmError> {
        match frame {
            Frame::BindHere => self.bind_here(value),
            Frame::ApplyCallee {
                arg,
                env,
                delay_arg,
            } => self.continue_apply_arg(value, &arg, &env, delay_arg),
            Frame::ApplyArg { callee } => self.apply(callee, value),
            Frame::If {
                then_branch,
                else_branch,
                env,
            } => self.continue_if_value_frame(value, then_branch, else_branch, env),
            Frame::Tuple {
                done,
                remaining,
                env,
                force_items,
            } => self.continue_tuple_item(done, remaining, env, force_items, value),
            Frame::Select { field } => self.select_field(value, &field),
            Frame::Match { arms, env } => self.eval_match(value, &arms, &env),
            Frame::Variant { tag } => self.continue_variant_value(tag, VmResult::Value(value)),
            Frame::BlockLet {
                pattern,
                remaining,
                tail,
                mut env,
            } => {
                self.bind_pattern(&pattern, value, &mut env)?;
                self.eval_block(remaining, tail, env)
            }
            Frame::BlockExpr {
                remaining,
                tail,
                env,
            } => self.continue_block_expr(value, remaining, tail, env),
            Frame::Handle {
                id,
                arms,
                env,
                guard_stack,
                expected_ty,
            } => match value {
                VmValue::Thunk(thunk) => {
                    let result = self.bind_here(VmValue::Thunk(thunk))?;
                    trace_handle_repush("frame_handle_thunk.repush", id, &continuation);
                    continuation.frames.push(Frame::Handle {
                        id,
                        arms,
                        env,
                        guard_stack,
                        expected_ty,
                    });
                    Ok(result)
                }
                value => {
                    continuation.guard_stack = guard_stack;
                    self.handle_value(value, &arms, &env, &expected_ty)
                }
            },
            Frame::HandleGuard {
                id,
                request,
                outer,
                handler_guard_stack,
                arms,
                env,
                arm_env,
                body,
                expected_ty,
            } => self.continue_handle_guard(
                value,
                request,
                outer,
                id,
                arms,
                env,
                handler_guard_stack,
                arm_env,
                body,
                expected_ty,
            ),
            Frame::HandlePayload { mut request } => {
                let blocked_ids = request.continuation.blocked_ids.clone();
                request.payload = value;
                request.continuation = VmContinuation {
                    frames: Vec::new(),
                    guard_stack: continuation.guard_stack.clone(),
                    blocked_ids,
                };
                Ok(VmResult::Request(request))
            }
            Frame::LocalPushId { parent } => {
                continuation.guard_stack = parent;
                Ok(VmResult::Value(value))
            }
            Frame::BlockedEffects { .. } => Ok(VmResult::Value(value)),
            Frame::Coerce { to } => Ok(VmResult::Value(cast_value(value, &to))),
            Frame::WrapThunkResult { expected_ty } => {
                Ok(VmResult::Value(wrap_value_for_type(value, &expected_ty)))
            }
        }
    }

    pub(super) fn continue_result(
        &mut self,
        result: VmResult,
        continuation: VmContinuation,
    ) -> Result<VmResult, VmError> {
        match result {
            VmResult::Value(value) => self.resume(continuation, value),
            VmResult::Request(mut request) => {
                prepend_frames(&mut request.continuation, continuation.frames);
                self.propagate_request(request)
            }
        }
    }

    fn force_handle_result_for_type(
        &mut self,
        result: VmResult,
        expected_ty: &Type,
    ) -> Result<VmResult, VmError> {
        if matches!(expected_ty, Type::Thunk { .. }) {
            return Ok(result);
        }
        match result {
            VmResult::Value(VmValue::Thunk(thunk)) => self.bind_here(VmValue::Thunk(thunk)),
            VmResult::Request(request) => {
                Ok(VmResult::Request(push_frame(request, Frame::BindHere)))
            }
            other => Ok(other),
        }
    }

    fn continue_handle_result_for_type(
        &mut self,
        result: VmResult,
        mut continuation: VmContinuation,
        expected_ty: &Type,
    ) -> Result<VmResult, VmError> {
        trace_continue_handle_result(expected_ty, &result, &continuation);
        if matches!(expected_ty, Type::Thunk { .. }) {
            return self.continue_result(result, continuation);
        }
        match result {
            VmResult::Value(VmValue::Thunk(thunk)) => {
                let result = self.bind_here(VmValue::Thunk(thunk))?;
                self.continue_result(result, continuation)
            }
            VmResult::Request(request) => {
                continuation.frames.push(Frame::BindHere);
                self.continue_result(VmResult::Request(request), continuation)
            }
            other => self.continue_result(other, continuation),
        }
    }

    pub(super) fn propagate_request(&mut self, request: VmRequest) -> Result<VmResult, VmError> {
        self.propagate_request_before(request, usize::MAX)
    }

    pub(super) fn propagate_request_before(
        &mut self,
        request: VmRequest,
        before: usize,
    ) -> Result<VmResult, VmError> {
        let end = before.min(request.continuation.frames.len());
        let frames = request.continuation.frames.get(..end).unwrap_or(&[]);
        trace_propagate_entry(&request.effect, before, frames);
        let Some(index) = frames.iter().rposition(|frame| {
            matches!(frame, Frame::Handle { .. } | Frame::BlockedEffects { .. })
        }) else {
            trace_propagate_no_handler(&request.effect);
            return Ok(VmResult::Request(request));
        };
        if let Frame::BlockedEffects { blocked, active } = &frames[index] {
            let (blocked, active) = (blocked.clone(), *active);
            let mut request = request;
            request.continuation.frames.remove(index);
            let request = if active {
                mark_request_with_active_blocked(request, &blocked)
            } else {
                mark_request_with_blocked(request, &blocked)
            };
            return self.propagate_request(request);
        }
        let Frame::Handle {
            id,
            arms,
            env,
            guard_stack,
            expected_ty,
        } = &frames[index]
        else {
            unreachable!();
        };
        let (id, arms, env, handler_guard_stack, expected_ty) = (
            *id,
            arms.clone(),
            env.clone(),
            guard_stack.clone(),
            expected_ty.clone(),
        );
        match self.handle_request(request, id, &arms, &env, &handler_guard_stack, &expected_ty)? {
            VmResult::Request(request) => self.propagate_request_before(request, index),
            value => Ok(value),
        }
    }

    pub(super) fn eval_effect_id(&self, id: EffectIdRef) -> Result<u64, VmError> {
        match id {
            EffectIdRef::Peek => self.guard_stack.peek().ok_or(VmError::UnsupportedFindId),
            EffectIdRef::Var(var) => self
                .guard_stack
                .find_var(var)
                .or_else(|| self.guard_stack.peek())
                .ok_or(VmError::UnsupportedEffectIdVar(var.0)),
        }
    }

    pub(super) fn find_effect_id(&self, id: EffectIdRef) -> Result<bool, VmError> {
        let id = self.eval_effect_id(id)?;
        Ok(self.guard_stack.contains(id))
    }

    pub(super) fn fresh_guard_id(&mut self) -> u64 {
        let id = self.next_guard_id;
        self.next_guard_id += 1;
        id
    }
}

fn make_recursive_local_value(pattern: &Pattern, value: VmValue) -> VmValue {
    let Some(name) = single_bind_name(pattern) else {
        return value;
    };
    let VmValue::Closure(closure) = value else {
        return value;
    };
    let mut closure = (*closure).clone();
    closure.self_name = Some(typed_ir::Path::from_name(name));
    VmValue::Closure(Rc::new(closure))
}

fn push_thunk_expr_frames(request: VmRequest, thunk: &VmThunk) -> VmRequest {
    let request = push_frame(request, Frame::BindHere);
    push_thunk_boundary_frame(request, thunk)
}

fn push_thunk_boundary_frame(request: VmRequest, thunk: &VmThunk) -> VmRequest {
    if thunk.blocked.is_empty() {
        return request;
    }
    push_frame(
        request,
        Frame::BlockedEffects {
            blocked: thunk.blocked.clone(),
            active: thunk.blocked.iter().any(|blocked| blocked.active),
        },
    )
}

thread_local! {
    pub(super) static HANDLE_TRACE_BUFFER: std::cell::RefCell<Vec<String>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

pub(super) fn handle_trace_enabled() -> bool {
    static CACHED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *CACHED.get_or_init(|| std::env::var("YULANG_TRACE_HANDLE").is_ok())
}

fn trace_handle_push(tag: &str, id: u64, request: &VmRequest) {
    if !handle_trace_enabled() {
        return;
    }
    let line = format!(
        "HANDLE_TRACE {tag} id={id} effect={:?} frames_before_push={}",
        request.effect,
        request.continuation.frames.len()
    );
    HANDLE_TRACE_BUFFER.with(|cell| cell.borrow_mut().push(line));
}

fn trace_eval_var(tag: &str, path: &typed_ir::Path, value: &VmValue) {
    if !handle_trace_enabled() {
        return;
    }
    let path_str = format!("{path:?}");
    if !(path_str.contains("&s#") || path_str.contains("run") || path_str.contains("update")) {
        return;
    }
    let value_tag = match value {
        VmValue::Closure(c) => {
            let body_tag = match &c.body.kind {
                ExprKind::Lambda { .. } => "lambda",
                ExprKind::LocalPushId { .. } => "local_push_id",
                ExprKind::Handle { .. } => "handle",
                ExprKind::BindHere { .. } => "bind_here",
                ExprKind::Apply { .. } => "apply",
                ExprKind::AddId { .. } => "add_id",
                ExprKind::Thunk { .. } => "thunk_expr",
                ExprKind::Coerce { .. } => "coerce",
                _ => "other",
            };
            let self_name = c
                .self_name
                .as_ref()
                .map(|p| format!("{p:?}"))
                .unwrap_or_else(|| "<anon>".to_string());
            format!(
                "closure(self_name={self_name},body={body_tag},env_keys={})",
                c.env.len()
            )
        }
        VmValue::Thunk(t) => format!("thunk(blocked={})", t.blocked.len()),
        VmValue::EffectOp(_) => "effect_op".to_string(),
        VmValue::Resume(_) => "resume".to_string(),
        VmValue::Unit => "unit".to_string(),
        _ => "other".to_string(),
    };
    let line = format!("HANDLE_TRACE eval_var.{tag} path={path_str} value={value_tag}");
    HANDLE_TRACE_BUFFER.with(|cell| cell.borrow_mut().push(line));
}

fn trace_eval_var_binding(tag: &str, path: &typed_ir::Path) {
    if !handle_trace_enabled() {
        return;
    }
    let path_str = format!("{path:?}");
    if !(path_str.contains("&s#") || path_str.contains("run") || path_str.contains("update")) {
        return;
    }
    let line = format!("HANDLE_TRACE eval_var.{tag} path={path_str}");
    HANDLE_TRACE_BUFFER.with(|cell| cell.borrow_mut().push(line));
}

fn trace_apply_eval_entry(tag: &str, callee_kind: &ExprKind, arg_kind: &ExprKind, delay_arg: bool) {
    if !handle_trace_enabled() {
        return;
    }
    let callee_tag = match callee_kind {
        ExprKind::Var(p) => format!("Var({p:?})"),
        ExprKind::EffectOp(p) => format!("EffectOp({p:?})"),
        ExprKind::Apply { .. } => "Apply".to_string(),
        ExprKind::Lambda { .. } => "Lambda".to_string(),
        ExprKind::BindHere { .. } => "BindHere".to_string(),
        ExprKind::Thunk { .. } => "Thunk".to_string(),
        ExprKind::Coerce { .. } => "Coerce".to_string(),
        ExprKind::AddId { .. } => "AddId".to_string(),
        _ => "other".to_string(),
    };
    let arg_tag = match arg_kind {
        ExprKind::Var(p) => format!("Var({p:?})"),
        ExprKind::Thunk { .. } => "Thunk".to_string(),
        ExprKind::Apply { .. } => "Apply".to_string(),
        ExprKind::Lit(_) => "Lit".to_string(),
        ExprKind::Coerce { .. } => "Coerce".to_string(),
        ExprKind::AddId { .. } => "AddId".to_string(),
        ExprKind::BindHere { .. } => "BindHere".to_string(),
        ExprKind::EffectOp(p) => format!("EffectOp({p:?})"),
        ExprKind::LocalPushId { .. } => "LocalPushId".to_string(),
        ExprKind::Pack { .. } => "Pack".to_string(),
        _ => "other".to_string(),
    };
    let line = format!(
        "HANDLE_TRACE {tag} callee_kind={callee_tag} arg_kind={arg_tag} delay_arg={delay_arg}"
    );
    HANDLE_TRACE_BUFFER.with(|cell| cell.borrow_mut().push(line));
}

fn trace_apply_callee_ty(callee_kind: &ExprKind, ty: &Type) {
    if !handle_trace_enabled() {
        return;
    }
    let is_set = matches!(callee_kind, ExprKind::EffectOp(p) if format!("{p:?}").contains("set"));
    let is_run = matches!(callee_kind, ExprKind::Var(p) if format!("{p:?}").contains("run"));
    let is_apply_chain = matches!(callee_kind, ExprKind::Apply { .. });
    if !(is_set || is_run || is_apply_chain) {
        return;
    }
    let line = format!("HANDLE_TRACE apply_eval.callee_ty kind=brief ty={ty:?}");
    HANDLE_TRACE_BUFFER.with(|cell| cell.borrow_mut().push(line));
}

fn trace_apply_eval_callee_ready(callee: &VmValue) {
    if !handle_trace_enabled() {
        return;
    }
    let callee_tag = match callee {
        VmValue::Closure(c) => {
            let name = c
                .self_name
                .as_ref()
                .map(|p| format!("{p:?}"))
                .unwrap_or_else(|| "<anon>".to_string());
            let body_tag = match &c.body.kind {
                ExprKind::Lambda { .. } => "lambda",
                ExprKind::LocalPushId { .. } => "local_push_id",
                ExprKind::Handle { .. } => "handle",
                ExprKind::BindHere { .. } => "bind_here",
                ExprKind::Apply { .. } => "apply",
                _ => "other",
            };
            format!("closure(self_name={name},body={body_tag})")
        }
        VmValue::Thunk(_) => "thunk".to_string(),
        VmValue::EffectOp(_) => "effect_op".to_string(),
        VmValue::Resume(_) => "resume".to_string(),
        VmValue::PrimitiveOp(_) => "primitive".to_string(),
        _ => "other".to_string(),
    };
    let line = format!("HANDLE_TRACE apply_eval.callee_ready callee={callee_tag}");
    HANDLE_TRACE_BUFFER.with(|cell| cell.borrow_mut().push(line));
}

fn trace_eval_var_effect_op(tag: &str, path: &typed_ir::Path) {
    if !handle_trace_enabled() {
        return;
    }
    let path_str = format!("{path:?}");
    if !(path_str.contains("set") || path_str.contains("get") || path_str.contains("update")) {
        return;
    }
    let line = format!("HANDLE_TRACE eval_var.{tag} path={path_str}");
    HANDLE_TRACE_BUFFER.with(|cell| cell.borrow_mut().push(line));
}

fn trace_handle_repush(tag: &str, id: u64, continuation: &VmContinuation) {
    if !handle_trace_enabled() {
        return;
    }
    let line = format!(
        "HANDLE_TRACE {tag} id={id} frames_before_push={}",
        continuation.frames.len()
    );
    HANDLE_TRACE_BUFFER.with(|cell| cell.borrow_mut().push(line));
}

fn trace_handle_request_outcome(tag: &str, id: u64, effect: &typed_ir::Path) {
    if !handle_trace_enabled() {
        return;
    }
    let line = format!(
        "HANDLE_TRACE handle_request.{tag} id={id} effect={:?}",
        effect
    );
    HANDLE_TRACE_BUFFER.with(|cell| cell.borrow_mut().push(line));
}

fn trace_handle_request_arm_miss(id: u64, effect: &typed_ir::Path, arm_effects: &[String]) {
    if !handle_trace_enabled() {
        return;
    }
    let line = format!(
        "HANDLE_TRACE handle_request.arm_miss id={id} effect={:?} arms={:?}",
        effect, arm_effects
    );
    HANDLE_TRACE_BUFFER.with(|cell| cell.borrow_mut().push(line));
}

fn trace_propagate_entry(effect: &typed_ir::Path, before: usize, frames: &[Frame]) {
    if !handle_trace_enabled() {
        return;
    }
    let handle_ids: Vec<u64> = frames
        .iter()
        .filter_map(|f| match f {
            Frame::Handle { id, .. } => Some(*id),
            _ => None,
        })
        .collect();
    let blocked_count = frames
        .iter()
        .filter(|f| matches!(f, Frame::BlockedEffects { .. }))
        .count();
    let line = format!(
        "HANDLE_TRACE propagate.entry effect={:?} before={} frames_len={} handle_ids={:?} blocked_count={}",
        effect,
        before,
        frames.len(),
        handle_ids,
        blocked_count
    );
    HANDLE_TRACE_BUFFER.with(|cell| cell.borrow_mut().push(line));
}

fn trace_propagate_no_handler(effect: &typed_ir::Path) {
    if !handle_trace_enabled() {
        return;
    }
    let line = format!("HANDLE_TRACE propagate.no_handler effect={:?}", effect);
    HANDLE_TRACE_BUFFER.with(|cell| cell.borrow_mut().push(line));
}

fn trace_bind_here_entry(value: &VmValue) {
    if !handle_trace_enabled() {
        return;
    }
    let tag = match value {
        VmValue::Thunk(thunk) => {
            let body_tag = match &thunk.body {
                ThunkBody::Expr(_) => "thunk_expr",
                ThunkBody::Value(_) => "thunk_value",
                ThunkBody::Emit { effect, .. } => {
                    let line = format!(
                        "HANDLE_TRACE bind_here.entry value=thunk_emit effect={:?} blocked_count={}",
                        effect,
                        thunk.blocked.len()
                    );
                    HANDLE_TRACE_BUFFER.with(|cell| cell.borrow_mut().push(line));
                    return;
                }
            };
            let line = format!(
                "HANDLE_TRACE bind_here.entry value={} blocked_count={}",
                body_tag,
                thunk.blocked.len()
            );
            HANDLE_TRACE_BUFFER.with(|cell| cell.borrow_mut().push(line));
            return;
        }
        VmValue::Closure(_) => "closure",
        VmValue::Resume(_) => "resume",
        VmValue::EffectOp(_) => "effect_op",
        VmValue::Unit => "unit",
        _ => "other",
    };
    let line = format!("HANDLE_TRACE bind_here.entry value={}", tag);
    HANDLE_TRACE_BUFFER.with(|cell| cell.borrow_mut().push(line));
}

fn trace_apply_entry(callee: &VmValue, arg: &VmValue) {
    if !handle_trace_enabled() {
        return;
    }
    let callee_tag = match callee {
        VmValue::Closure(c) => {
            let name = c
                .self_name
                .as_ref()
                .map(|p| format!("{p:?}"))
                .unwrap_or_else(|| "<anon>".to_string());
            let short_name = if name.contains("&s#")
                || name.contains("run")
                || name.contains("update")
                || name.contains("loop")
            {
                name
            } else {
                "<other_closure>".to_string()
            };
            format!("closure({short_name})")
        }
        VmValue::Resume(_) => "resume".to_string(),
        VmValue::EffectOp(p) => format!("effect_op({p:?})"),
        VmValue::Thunk(_) => "thunk".to_string(),
        VmValue::PrimitiveOp(_) => "primitive".to_string(),
        _ => "other".to_string(),
    };
    let arg_tag = match arg {
        VmValue::Thunk(t) => format!("thunk(blocked={})", t.blocked.len()),
        VmValue::Closure(_) => "closure".to_string(),
        VmValue::Resume(_) => "resume".to_string(),
        VmValue::EffectOp(_) => "effect_op".to_string(),
        VmValue::Unit => "unit".to_string(),
        VmValue::Int(_) => "int".to_string(),
        _ => "other".to_string(),
    };
    let line = format!(
        "HANDLE_TRACE apply.entry callee={} arg={}",
        callee_tag, arg_tag
    );
    HANDLE_TRACE_BUFFER.with(|cell| cell.borrow_mut().push(line));
}

fn trace_continue_handle_result(
    expected_ty: &Type,
    result: &VmResult,
    continuation: &VmContinuation,
) {
    if !handle_trace_enabled() {
        return;
    }
    let expected_tag = match expected_ty {
        Type::Thunk { .. } => "thunk",
        Type::Value(_) => "value",
        Type::Unknown => "unknown",
        _ => "other",
    };
    let result_tag = match result {
        VmResult::Value(VmValue::Thunk(_)) => "value_thunk",
        VmResult::Value(_) => "value_other",
        VmResult::Request(_) => "request",
    };
    let handle_ids: Vec<u64> = continuation
        .frames
        .iter()
        .filter_map(|f| match f {
            Frame::Handle { id, .. } => Some(*id),
            _ => None,
        })
        .collect();
    let line = format!(
        "HANDLE_TRACE continue_handle_result expected={} result={} outer_frames_len={} outer_handle_ids={:?}",
        expected_tag,
        result_tag,
        continuation.frames.len(),
        handle_ids
    );
    HANDLE_TRACE_BUFFER.with(|cell| cell.borrow_mut().push(line));
}

fn tuple_type_forces_items(ty: &Type) -> bool {
    matches!(ty, Type::Value(typed_ir::Type::Tuple(_)))
}

fn closure_param_forces_thunk_arg(param_ty: &Type) -> bool {
    !matches!(
        param_ty,
        Type::Thunk { .. } | Type::Value(typed_ir::Type::Any)
    )
}

fn handle_payload_forces_thunk(pattern: &Pattern, value: &VmValue) -> bool {
    matches!(value, VmValue::Thunk(_)) && !matches!(pattern_ty(pattern), Type::Thunk { .. })
}

fn pattern_ty(pattern: &Pattern) -> &Type {
    match pattern {
        Pattern::Wildcard { ty }
        | Pattern::Bind { ty, .. }
        | Pattern::Lit { ty, .. }
        | Pattern::Tuple { ty, .. }
        | Pattern::List { ty, .. }
        | Pattern::Record { ty, .. }
        | Pattern::Variant { ty, .. }
        | Pattern::Or { ty, .. }
        | Pattern::As { ty, .. } => ty,
    }
}

fn callee_expects_thunk_arg(callee: &VmValue) -> bool {
    matches!(
        callee,
        VmValue::Closure(closure) if matches!(closure.param_ty, Type::Thunk { .. })
    )
}

fn lambda_param_type(
    param_ty: Type,
    annotation: Option<&typed_ir::ParamEffectAnnotation>,
    function_allowed_effects: Option<&typed_ir::FunctionSigAllowedEffects>,
) -> Type {
    if matches!(param_ty, Type::Thunk { .. }) {
        return param_ty;
    }
    if let Some(allowed) = function_allowed_effects {
        return Type::Thunk {
            effect: function_allowed_effect_type(allowed),
            value: Box::new(param_ty),
        };
    }
    let Some(annotation) = annotation else {
        return param_ty;
    };
    Type::Thunk {
        effect: param_effect_annotation_effect(annotation),
        value: Box::new(param_ty),
    }
}

fn function_allowed_effect_type(allowed: &typed_ir::FunctionSigAllowedEffects) -> typed_ir::Type {
    match allowed {
        typed_ir::FunctionSigAllowedEffects::Wildcard => typed_ir::Type::Any,
        typed_ir::FunctionSigAllowedEffects::Effects(paths) => typed_ir::Type::Row {
            items: paths
                .iter()
                .cloned()
                .map(|path| typed_ir::Type::Named {
                    path,
                    args: Vec::new(),
                })
                .collect(),
            tail: Box::new(typed_ir::Type::Never),
        },
    }
}

fn param_effect_annotation_effect(annotation: &typed_ir::ParamEffectAnnotation) -> typed_ir::Type {
    match annotation {
        typed_ir::ParamEffectAnnotation::Wildcard => typed_ir::Type::Any,
        typed_ir::ParamEffectAnnotation::Region(name) => typed_ir::Type::Named {
            path: typed_ir::Path::from_name(name.clone()),
            args: Vec::new(),
        },
    }
}

fn single_bind_name(pattern: &Pattern) -> Option<typed_ir::Name> {
    match pattern {
        Pattern::Bind { name, .. } => Some(name.clone()),
        Pattern::As { name, .. } => Some(name.clone()),
        _ => None,
    }
}
