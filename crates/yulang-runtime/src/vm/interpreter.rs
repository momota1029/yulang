use super::*;

pub(super) struct VmInterpreter<'m> {
    module: &'m Module,
    bindings: HashMap<core_ir::Path, usize>,
    next_guard_id: u64,
    guard_stack: GuardStack,
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
        }
    }

    pub(super) fn eval_root_expr(&mut self, index: usize) -> Result<VmResult, VmError> {
        let expr = self
            .module
            .root_exprs
            .get(index)
            .ok_or(VmError::MissingRootExpr(index))?;
        let result = self.eval_expr(expr, &Env::new())?;
        match result {
            VmResult::Value(VmValue::Thunk(thunk)) => self.bind_here(VmValue::Thunk(thunk)),
            other => Ok(other),
        }
    }

    pub(super) fn eval_expr(&mut self, expr: &Expr, env: &Env) -> Result<VmResult, VmError> {
        match &expr.kind {
            ExprKind::Var(path) => self.eval_var(path, env),
            ExprKind::EffectOp(path) => Ok(VmResult::Value(VmValue::EffectOp(path.clone()))),
            ExprKind::PrimitiveOp(op) => Ok(VmResult::Value(VmValue::PrimitiveOp(Rc::new(
                VmPrimitive {
                    op: *op,
                    args: Vec::new(),
                },
            )))),
            ExprKind::Lit(lit) => Ok(VmResult::Value(value_from_lit(lit))),
            ExprKind::Lambda { param, body, .. } => {
                let (param_ty, ret) = match &expr.ty {
                    Type::Fun { param, ret } => (param.as_ref().clone(), ret.as_ref().clone()),
                    _ => (Type::Core(core_ir::Type::Any), body.ty.clone()),
                };
                Ok(VmResult::Value(VmValue::Closure(Rc::new(VmClosure {
                    param: param.clone(),
                    param_ty,
                    body: (**body).clone(),
                    ret,
                    env: env.clone(),
                    self_name: None,
                }))))
            }
            ExprKind::Apply { callee, arg, .. } => {
                let delay_arg = expects_thunk_arg(&callee.ty);
                match self.eval_expr(callee, env)? {
                    VmResult::Value(callee) => self.continue_apply_arg(callee, arg, env, delay_arg),
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
            ExprKind::Tuple(items) => self.eval_tuple(Vec::new(), items.clone(), env.clone()),
            ExprKind::Record { fields, spread } => self.eval_record(fields, spread, env),
            ExprKind::Variant { tag, value } => Ok(VmResult::Value(VmValue::Variant {
                tag: tag.clone(),
                value: value
                    .as_ref()
                    .map(|value| self.eval_value(value, env))
                    .transpose()?
                    .map(Box::new),
            })),
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
            ExprKind::Handle { body, arms, .. } => self.eval_handle(body, arms, env),
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
            ExprKind::AddId { id, allowed, thunk } => {
                let id = self.eval_effect_id(*id)?;
                let thunk = self.eval_value(thunk, env)?;
                let VmValue::Thunk(thunk) = thunk else {
                    return Err(VmError::ExpectedThunk(thunk));
                };
                let mut thunk = (*thunk).clone();
                thunk.blocked.push(BlockedEffect {
                    guard_id: id,
                    allowed: allowed.clone(),
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
        path: &core_ir::Path,
        env: &Env,
    ) -> Result<VmResult, VmError> {
        if let Some(value) = env.get(path) {
            return Ok(VmResult::Value(value.clone()));
        }
        if let Some(index) = self.bindings.get(path).copied() {
            let binding = &self.module.bindings[index];
            return self.eval_expr(&binding.body, &Env::new());
        }
        if path.segments.len() > 1 {
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
        let VmValue::Thunk(thunk) = value else {
            return Ok(VmResult::Value(value));
        };
        let parent = self.guard_stack.clone();
        self.guard_stack = thunk.guard_stack.clone();
        match &thunk.body {
            ThunkBody::Value(value) => {
                self.guard_stack = parent;
                Ok(VmResult::Value(value.clone()))
            }
            ThunkBody::Expr(expr) => {
                let result = match self.eval_expr(expr, &thunk.env)? {
                    VmResult::Value(VmValue::Thunk(next)) => self.bind_here(VmValue::Thunk(next)),
                    VmResult::Request(request) => Ok(VmResult::Request(push_frame(
                        mark_request(request, &thunk),
                        Frame::BindHere,
                    ))),
                    other => Ok(other),
                };
                self.guard_stack = parent;
                result
            }
            ThunkBody::Emit { effect, payload } => {
                let result = Ok(VmResult::Request(mark_request(
                    VmRequest {
                        effect: effect.clone(),
                        payload: payload.clone(),
                        continuation: VmContinuation::new(self.guard_stack.clone()),
                        blocked_id: None,
                    },
                    &thunk,
                )));
                self.guard_stack = parent;
                result
            }
        }
    }

    pub(super) fn continue_apply_arg(
        &mut self,
        callee: VmValue,
        arg: &Expr,
        env: &Env,
        delay_arg: bool,
    ) -> Result<VmResult, VmError> {
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

    pub(super) fn apply(&mut self, callee: VmValue, arg: VmValue) -> Result<VmResult, VmError> {
        match callee {
            VmValue::Closure(callee) => {
                if !matches!(callee.param_ty, Type::Thunk { .. }) {
                    if let VmValue::Thunk(_) = arg {
                        return self.force_apply_arg(VmValue::Closure(callee), arg);
                    }
                }
                let mut env = callee.env.clone();
                if let Some(self_name) = &callee.self_name {
                    env.insert(self_name.clone(), VmValue::Closure(callee.clone()));
                }
                env.insert(core_ir::Path::from_name(callee.param.clone()), arg);
                let result = self.eval_expr(&callee.body, &env)?;
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
    ) -> Result<VmResult, VmError> {
        if remaining.is_empty() {
            return Ok(VmResult::Value(VmValue::Tuple(done)));
        }
        let next = remaining.remove(0);
        match self.eval_expr(&next, &env)? {
            VmResult::Value(value) => {
                done.push(value);
                self.eval_tuple(done, remaining, env)
            }
            VmResult::Request(request) => Ok(VmResult::Request(push_frame(
                request,
                Frame::Tuple {
                    done,
                    remaining,
                    env,
                },
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
        field: &core_ir::Name,
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

    pub(super) fn eval_block(
        &mut self,
        mut stmts: Vec<Stmt>,
        tail: Option<Expr>,
        mut env: Env,
    ) -> Result<VmResult, VmError> {
        if stmts.is_empty() {
            return match tail {
                Some(tail) => self.eval_expr(&tail, &env),
                None => Ok(VmResult::Value(VmValue::Unit)),
            };
        }
        let stmt = stmts.remove(0);
        match stmt {
            Stmt::Let { pattern, value } => match self.eval_expr(&value, &env)? {
                VmResult::Value(mut value) => {
                    value = make_recursive_local_value(&pattern, value);
                    self.bind_pattern(&pattern, value, &mut env)?;
                    self.eval_block(stmts, tail, env)
                }
                VmResult::Request(request) => Ok(VmResult::Request(push_frame(
                    request,
                    Frame::BlockLet {
                        pattern,
                        remaining: stmts,
                        tail,
                        env,
                    },
                ))),
            },
            Stmt::Expr(expr) => match self.eval_expr(&expr, &env)? {
                VmResult::Value(VmValue::Thunk(thunk)) => {
                    match self.bind_here(VmValue::Thunk(thunk))? {
                        VmResult::Value(_) => self.eval_block(stmts, tail, env),
                        VmResult::Request(request) => Ok(VmResult::Request(push_frame(
                            request,
                            Frame::BlockExpr {
                                remaining: stmts,
                                tail,
                                env,
                            },
                        ))),
                    }
                }
                VmResult::Value(_) => self.eval_block(stmts, tail, env),
                VmResult::Request(request) => Ok(VmResult::Request(push_frame(
                    request,
                    Frame::BlockExpr {
                        remaining: stmts,
                        tail,
                        env,
                    },
                ))),
            },
            Stmt::Module { def, body } => {
                let value = self.eval_value(&body, &env)?;
                env.insert(def, value);
                self.eval_block(stmts, tail, env)
            }
        }
    }

    pub(super) fn eval_handle(
        &mut self,
        body: &Expr,
        arms: &[HandleArm],
        env: &Env,
    ) -> Result<VmResult, VmError> {
        let id = self.fresh_guard_id();
        let handler_guard_stack = self.guard_stack.clone();
        let result = match self.eval_expr(body, env)? {
            VmResult::Value(VmValue::Thunk(thunk)) => self.bind_here(VmValue::Thunk(thunk))?,
            other => other,
        };
        match result {
            VmResult::Value(value) => self.handle_value(value, arms, env),
            VmResult::Request(request) => {
                let request = push_frame(
                    request,
                    Frame::Handle {
                        id,
                        arms: arms.to_vec(),
                        env: env.clone(),
                        guard_stack: handler_guard_stack.clone(),
                    },
                );
                self.handle_request(request, id, arms, env, &handler_guard_stack)
            }
        }
    }

    pub(super) fn handle_value(
        &mut self,
        value: VmValue,
        arms: &[HandleArm],
        env: &Env,
    ) -> Result<VmResult, VmError> {
        for arm in arms.iter().filter(|arm| arm.effect.segments.is_empty()) {
            let mut arm_env = env.clone();
            if self
                .bind_pattern(&arm.payload, value.clone(), &mut arm_env)
                .is_err()
            {
                continue;
            }
            return self.eval_expr(&arm.body, &arm_env);
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
    ) -> Result<VmResult, VmError> {
        if request
            .blocked_id
            .is_some_and(|blocked| handler_guard_stack.contains(blocked))
        {
            return Ok(VmResult::Request(request));
        }
        let Some(arm) = arms.iter().find(|arm| arm.effect == request.effect) else {
            return Ok(VmResult::Request(request));
        };
        let outer = request.continuation.clone().outside_handle(id);
        let mut arm_env = env.clone();
        self.bind_pattern(&arm.payload, request.payload.clone(), &mut arm_env)?;
        if let Some(resume) = &arm.resume {
            arm_env.insert(
                core_ir::Path::from_name(resume.name.clone()),
                VmValue::Resume(Rc::new(VmResume {
                    continuation: request.continuation.clone().inside_handle(id),
                })),
            );
        }
        if let Some(guard) = &arm.guard {
            return match self.eval_expr(guard, &arm_env)? {
                VmResult::Value(guard) => self.continue_handle_guard(
                    guard,
                    request,
                    outer,
                    id,
                    arms.to_vec(),
                    env.clone(),
                    arm_env,
                    arm.body.clone(),
                ),
                VmResult::Request(guard_request) => Ok(VmResult::Request(push_frame(
                    guard_request,
                    Frame::HandleGuard {
                        id,
                        request,
                        outer,
                        handler_guard_stack: handler_guard_stack.clone(),
                        arms: arms.to_vec(),
                        env: env.clone(),
                        arm_env,
                        body: arm.body.clone(),
                    },
                ))),
            };
        }
        let result = self.eval_expr(&arm.body, &arm_env)?;
        self.continue_result(result, outer)
    }

    pub(super) fn continue_handle_guard(
        &mut self,
        guard: VmValue,
        request: VmRequest,
        outer: VmContinuation,
        _id: u64,
        _arms: Vec<HandleArm>,
        _env: Env,
        arm_env: Env,
        body: Expr,
    ) -> Result<VmResult, VmError> {
        match guard {
            VmValue::Bool(true) => {
                let result = self.eval_expr(&body, &arm_env)?;
                self.continue_result(result, outer)
            }
            VmValue::Bool(false) => Ok(VmResult::Request(request)),
            other => Err(VmError::ExpectedBool(other)),
        }
    }

    pub(super) fn resume(
        &mut self,
        mut continuation: VmContinuation,
        value: VmValue,
    ) -> Result<VmResult, VmError> {
        let previous = std::mem::replace(&mut self.guard_stack, continuation.guard_stack.clone());
        let result = match continuation.frames.pop() {
            Some(frame) => self.apply_frame(frame, continuation, value),
            None => Ok(VmResult::Value(value)),
        };
        self.guard_stack = previous;
        result
    }

    pub(super) fn apply_frame(
        &mut self,
        frame: Frame,
        continuation: VmContinuation,
        value: VmValue,
    ) -> Result<VmResult, VmError> {
        match frame {
            Frame::BindHere => {
                let result = self.bind_here(value)?;
                self.continue_result(result, continuation)
            }
            Frame::ApplyCallee {
                arg,
                env,
                delay_arg,
            } => {
                let result = self.continue_apply_arg(value, &arg, &env, delay_arg)?;
                self.continue_result(result, continuation)
            }
            Frame::ApplyArg { callee } => {
                let result = self.apply(callee, value)?;
                self.continue_result(result, continuation)
            }
            Frame::If {
                then_branch,
                else_branch,
                env,
            } => match value {
                VmValue::Bool(true) => {
                    let result = self.eval_expr(&then_branch, &env)?;
                    self.continue_result(result, continuation)
                }
                VmValue::Bool(false) => {
                    let result = self.eval_expr(&else_branch, &env)?;
                    self.continue_result(result, continuation)
                }
                other => Err(VmError::ExpectedBool(other)),
            },
            Frame::Tuple {
                mut done,
                remaining,
                env,
            } => {
                done.push(value);
                let result = self.eval_tuple(done, remaining, env)?;
                self.continue_result(result, continuation)
            }
            Frame::Select { field } => {
                let result = self.select_field(value, &field)?;
                self.continue_result(result, continuation)
            }
            Frame::Match { arms, env } => {
                let result = self.eval_match(value, &arms, &env)?;
                self.continue_result(result, continuation)
            }
            Frame::BlockLet {
                pattern,
                remaining,
                tail,
                mut env,
            } => {
                self.bind_pattern(&pattern, value, &mut env)?;
                let result = self.eval_block(remaining, tail, env)?;
                self.continue_result(result, continuation)
            }
            Frame::BlockExpr {
                remaining,
                tail,
                env,
            } => {
                let result = self.eval_block(remaining, tail, env)?;
                self.continue_result(result, continuation)
            }
            Frame::Handle {
                id,
                arms,
                env,
                guard_stack,
            } => match value {
                VmValue::Thunk(thunk) => {
                    let result = self.bind_here(VmValue::Thunk(thunk))?;
                    let mut continuation = continuation;
                    continuation.frames.push(Frame::Handle {
                        id,
                        arms,
                        env,
                        guard_stack,
                    });
                    self.continue_result(result, continuation)
                }
                value => {
                    let result = self.handle_value(value, &arms, &env)?;
                    let mut continuation = continuation;
                    continuation.guard_stack = guard_stack;
                    self.continue_result(result, continuation)
                }
            },
            Frame::HandleGuard {
                id,
                request,
                outer,
                handler_guard_stack: _,
                arms,
                env,
                arm_env,
                body,
            } => {
                let result = self
                    .continue_handle_guard(value, request, outer, id, arms, env, arm_env, body)?;
                self.continue_result(result, continuation)
            }
            Frame::LocalPushId { parent } => {
                let mut continuation = continuation;
                continuation.guard_stack = parent;
                self.resume(continuation, value)
            }
            Frame::Coerce { to } => {
                let result = VmResult::Value(cast_value(value, &to));
                self.continue_result(result, continuation)
            }
            Frame::WrapThunkResult { expected_ty } => {
                let result = VmResult::Value(wrap_value_for_type(value, &expected_ty));
                self.continue_result(result, continuation)
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
        let Some(index) = frames
            .iter()
            .rposition(|frame| matches!(frame, Frame::Handle { .. }))
        else {
            return Ok(VmResult::Request(request));
        };
        let Frame::Handle {
            id,
            arms,
            env,
            guard_stack,
        } = &frames[index]
        else {
            unreachable!();
        };
        let (id, arms, env, handler_guard_stack) =
            (*id, arms.clone(), env.clone(), guard_stack.clone());
        match self.handle_request(request, id, &arms, &env, &handler_guard_stack)? {
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
    closure.self_name = Some(core_ir::Path::from_name(name));
    VmValue::Closure(Rc::new(closure))
}

fn single_bind_name(pattern: &Pattern) -> Option<core_ir::Name> {
    match pattern {
        Pattern::Bind { name, .. } => Some(name.clone()),
        Pattern::As { name, .. } => Some(name.clone()),
        _ => None,
    }
}
