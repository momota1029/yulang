use super::*;

#[derive(Clone, Default)]
pub(super) struct Continuation {
    pub(super) frames: VecDeque<Frame>,
}

#[derive(Clone)]
pub(super) enum Frame {
    AdaptValue {
        source: Type,
        target: Type,
    },
    WrapThunkValue,
    ForceValueIfThunk,
    ApplyForcedThunk {
        arg: Value,
    },
    ApplyArg {
        callee: Value,
    },
    ApplyCallee {
        arg: ExprId,
        env: CapturedEnv,
    },
    ApplyAdapterArg {
        function: Value,
        markers: SharedMarkers,
        source_ret: Type,
        target_ret: Type,
    },
    ApplyAdapterResult {
        markers: SharedMarkers,
        source_ret: Type,
        target_ret: Type,
    },
    DirectBinarySecond {
        op: PrimitiveOp,
        context: PrimitiveContext,
        second_arg: ExprId,
        env: CapturedEnv,
    },
    DirectBinaryApply {
        op: PrimitiveOp,
        context: PrimitiveContext,
        first: Value,
    },
    DirectUnaryApply {
        op: PrimitiveOp,
        context: PrimitiveContext,
    },
    Coerce {
        source: Type,
        target: Type,
    },
    ForceThunk {
        target_value: Type,
    },
    MakeFunctionAdapter {
        source: Type,
        target: Type,
        hygiene: FunctionAdapterHygiene,
    },
    MarkerScope {
        resume_markers: SharedMarkers,
        activate_add_ids: bool,
        handler_key: Option<InternedPath>,
        inner_frame_count: usize,
    },
    MarkerExit {
        resume_markers: SharedMarkers,
        activate_add_ids: bool,
        handler_key: Option<InternedPath>,
        guard_len: usize,
        frame_len: usize,
        add_id_len: usize,
        plan_len: usize,
    },
    RefSetReference {
        value: ExprId,
        env: CapturedEnv,
    },
    RefSetForcedReference {
        value: ExprId,
        env: CapturedEnv,
    },
    RefSetValue {
        reference: Value,
    },
    RefSetForcedValue {
        reference: Value,
    },
    RefSetResolvedUnit,
    RefSetHandleResult {
        assigned: Value,
    },
    RefSetHandleValueResult {
        assigned: Value,
    },
    RefSetEmitResolvedRequest {
        request: Request,
        assigned: Value,
        mode: RefSetResumeMode,
    },
    MarkValue {
        markers: Vec<ValueMarker>,
    },
    ResolveRefSetValues {
        values: Vec<Value>,
        assigned: Value,
        out: Vec<Value>,
        index: usize,
        finish: RefSetFinish,
    },
    ResolveRefSetFields {
        fields: Vec<ValueField>,
        assigned: Value,
        out: Vec<ValueField>,
        index: usize,
    },
    RecordHeadSpread {
        fields: Vec<RecordField>,
        env: CapturedEnv,
    },
    RecordTailFields {
        spread: ExprId,
        env: CapturedEnv,
    },
    RecordTailSpread {
        fields: Vec<ValueField>,
    },
    RecordField {
        fields: Vec<RecordField>,
        env: CapturedEnv,
        values: Vec<ValueField>,
        index: usize,
    },
    TupleItem {
        items: Vec<ExprId>,
        env: CapturedEnv,
        values: Vec<Value>,
        index: usize,
    },
    PolyVariantPayload {
        tag: String,
        payloads: Vec<ExprId>,
        env: CapturedEnv,
        values: Vec<Value>,
        index: usize,
    },
    Select {
        name: String,
        resolution: Option<SelectResolution>,
    },
    CaseScrutineeForce {
        arms: Vec<CaseArm>,
        env: CapturedEnv,
    },
    CaseScrutinee {
        arms: Vec<CaseArm>,
        env: CapturedEnv,
    },
    CaseGuard {
        scrutinee: Value,
        arms: Vec<CaseArm>,
        env: CapturedEnv,
        index: usize,
        arm_env: CapturedEnv,
        body: ExprId,
    },
    CatchResult {
        arms: RuntimeCatchArms,
        env: CapturedEnv,
    },
    CatchValueGuard {
        value: Value,
        arms: RuntimeCatchArms,
        env: CapturedEnv,
        index: usize,
        arm_env: CapturedEnv,
        body: ExprId,
    },
    CatchRequestGuard {
        request: Request,
        arms: RuntimeCatchArms,
        env: CapturedEnv,
        index: usize,
        arm_env: CapturedEnv,
        body: ExprId,
    },
    HandlerBodyForce,
    BlockLetValue {
        pat: Pat,
        stmts: Vec<Stmt>,
        tail: Option<ExprId>,
        env: CapturedEnv,
        index: usize,
    },
    BlockExprValue {
        stmts: Vec<Stmt>,
        tail: Option<ExprId>,
        env: CapturedEnv,
        index: usize,
    },
    BindValue {
        pat: Pat,
        env: CapturedEnv,
        then: BindThen,
    },
    BindRecordDefault {
        pat: Pat,
        fields: Vec<RecordPatField>,
        spread: RecordSpread<DefId>,
        record_fields: Vec<ValueField>,
        markers: Vec<ValueMarker>,
        used: HashSet<usize>,
        env: CapturedEnv,
        then: BindThen,
    },
}

#[derive(Clone)]
pub(super) enum BindThen {
    ApplyClosure {
        body: ExprId,
    },
    BlockLet {
        stmts: Vec<Stmt>,
        tail: Option<ExprId>,
        index: usize,
        last: Value,
    },
    CaseArm {
        scrutinee: Value,
        arms: Vec<CaseArm>,
        env: CapturedEnv,
        index: usize,
        arm: CaseArm,
    },
    CatchValue {
        value: Value,
        arms: RuntimeCatchArms,
        env: CapturedEnv,
        index: usize,
        arm: RuntimeCatchArm,
    },
    CatchRequestPayload {
        request: Request,
        arms: RuntimeCatchArms,
        env: CapturedEnv,
        index: usize,
        arm: RuntimeCatchArm,
    },
    CatchRequestContinuation {
        request: Request,
        arms: RuntimeCatchArms,
        env: CapturedEnv,
        index: usize,
        guard: Option<ExprId>,
        body: ExprId,
    },
    Sequence {
        entries: Vec<(Pat, Value)>,
        then: Box<BindThen>,
    },
    Or {
        right: Pat,
        value: Value,
        env: CapturedEnv,
        then: Box<BindThen>,
    },
    As {
        def: DefId,
        value: Value,
        then: Box<BindThen>,
    },
    RecordField {
        fields: Vec<RecordPatField>,
        spread: RecordSpread<DefId>,
        record_fields: Vec<ValueField>,
        markers: Vec<ValueMarker>,
        used: HashSet<usize>,
        then: Box<BindThen>,
    },
}

#[derive(Clone)]
pub(super) enum RefSetFinish {
    Tuple,
    List,
    PolyVariant { tag: String },
    DataConstructor { def: DefId },
}

#[derive(Clone, Copy)]
pub(super) enum RefSetResumeMode {
    Result,
    ValueResult,
}

impl Frame {
    fn handles_eval_result(&self) -> bool {
        matches!(
            self,
            Frame::CatchResult { .. }
                | Frame::RefSetHandleResult { .. }
                | Frame::RefSetHandleValueResult { .. }
                | Frame::MarkerExit { .. }
        )
    }
}

impl<'a> Runtime<'a> {
    pub(super) fn resume(
        &mut self,
        mut continuation: Continuation,
        mut value: Value,
    ) -> RuntimeResult {
        'resume: loop {
            let Some(frame) = continuation.frames.pop_back() else {
                return value_result(value);
            };
            self.stats.request_resume_steps += 1;
            let result = if frame.handles_eval_result() {
                self.apply_result_frame(frame, EvalResult::Value(value))?
            } else {
                self.apply_frame(frame, &mut continuation, value)?
            };
            match result {
                EvalResult::Value(next) => value = next,
                EvalResult::Request(request) => {
                    let mut result = EvalResult::Request(request);
                    loop {
                        while continuation
                            .frames
                            .back()
                            .is_some_and(Frame::handles_eval_result)
                        {
                            let frame = continuation.frames.pop_back().expect("checked frame");
                            self.stats.request_resume_steps += 1;
                            result = self.apply_result_frame(frame, result)?;
                            if let EvalResult::Value(next) = result {
                                value = next;
                                continue 'resume;
                            }
                        }
                        let EvalResult::Request(request) = result else {
                            unreachable!("value result continues the resume loop");
                        };
                        if continuation
                            .frames
                            .iter()
                            .any(|frame| matches!(frame, Frame::MarkerExit { .. }))
                        {
                            result =
                                self.close_innermost_marker_request(&mut continuation, request)?;
                            continue;
                        }
                        let mut request = request;
                        prepend_frames(&mut request.continuation, continuation.frames);
                        return Ok(EvalResult::Request(request));
                    }
                }
            }
        }
    }

    pub(super) fn continue_with_frame(
        &mut self,
        result: EvalResult,
        frame: Frame,
    ) -> RuntimeResult {
        match result {
            EvalResult::Value(value) => {
                self.stats.continue_with_values += 1;
                let mut continuation = Continuation::default();
                let result = if frame.handles_eval_result() {
                    self.apply_result_frame(frame, EvalResult::Value(value))?
                } else {
                    self.apply_frame(frame, &mut continuation, value)?
                };
                self.finish_inline_result(result, continuation)
            }
            EvalResult::Request(request) => {
                self.stats.continue_with_requests += 1;
                Ok(EvalResult::Request(push_frame(request, frame)))
            }
        }
    }

    fn continue_with_current_frame(
        &mut self,
        result: EvalResult,
        frame: Frame,
        continuation: &mut Continuation,
    ) -> RuntimeResult {
        match result {
            EvalResult::Value(value) => {
                self.stats.continue_with_values += 1;
                continuation.frames.push_back(frame);
                value_result(value)
            }
            EvalResult::Request(request) => {
                self.stats.continue_with_requests += 1;
                Ok(EvalResult::Request(push_frame(request, frame)))
            }
        }
    }

    fn finish_inline_result(
        &mut self,
        result: EvalResult,
        mut continuation: Continuation,
    ) -> RuntimeResult {
        match result {
            EvalResult::Value(value) if continuation.frames.is_empty() => value_result(value),
            EvalResult::Value(value) => self.resume(continuation, value),
            EvalResult::Request(request) => self.finish_inline_request(request, &mut continuation),
        }
    }

    fn finish_inline_request(
        &mut self,
        request: Request,
        continuation: &mut Continuation,
    ) -> RuntimeResult {
        let mut result = EvalResult::Request(request);
        loop {
            while continuation
                .frames
                .back()
                .is_some_and(Frame::handles_eval_result)
            {
                let frame = continuation.frames.pop_back().expect("checked frame");
                self.stats.request_resume_steps += 1;
                result = self.apply_result_frame(frame, result)?;
                if let EvalResult::Value(value) = result {
                    return self.resume(std::mem::take(continuation), value);
                }
            }
            let EvalResult::Request(request) = result else {
                unreachable!("value result is handled above");
            };
            if continuation
                .frames
                .iter()
                .any(|frame| matches!(frame, Frame::MarkerExit { .. }))
            {
                result = self.close_innermost_marker_request(continuation, request)?;
                continue;
            }
            let mut request = request;
            prepend_frames(
                &mut request.continuation,
                std::mem::take(&mut continuation.frames),
            );
            return Ok(EvalResult::Request(request));
        }
    }

    fn apply_result_frame(&mut self, frame: Frame, result: EvalResult) -> RuntimeResult {
        match frame {
            Frame::CatchResult { arms, env } => self.handle_catch_result(result, arms, env),
            Frame::RefSetHandleResult { assigned } => self.handle_ref_set_result(result, assigned),
            Frame::RefSetHandleValueResult { assigned } => {
                self.handle_ref_set_value_result(result, assigned)
            }
            Frame::MarkerExit {
                resume_markers,
                activate_add_ids,
                handler_key,
                guard_len,
                frame_len,
                add_id_len,
                plan_len,
            } => {
                self.pop_marker_frame(guard_len, frame_len, add_id_len, plan_len);
                self.close_shared_resume_marker_frame_result(
                    result,
                    resume_markers,
                    activate_add_ids,
                    handler_key,
                )
            }
            frame => {
                let EvalResult::Value(value) = result else {
                    unreachable!("request result is only delivered to result frames");
                };
                let mut continuation = Continuation::default();
                self.apply_frame(frame, &mut continuation, value)
            }
        }
    }

    fn apply_frame(
        &mut self,
        frame: Frame,
        continuation: &mut Continuation,
        value: Value,
    ) -> RuntimeResult {
        match frame {
            Frame::CatchResult { .. }
            | Frame::RefSetHandleResult { .. }
            | Frame::RefSetHandleValueResult { .. }
            | Frame::MarkerExit { .. } => {
                unreachable!("result frames are handled before value frames")
            }
            Frame::AdaptValue { source, target } => self.adapt_value(value, &source, &target),
            Frame::WrapThunkValue => value_result(Value::Thunk(Thunk::Value(Box::new(value)))),
            Frame::ForceValueIfThunk => self.force_value_if_thunk(value),
            Frame::ApplyForcedThunk { arg } => self.apply_value(value, arg),
            Frame::ApplyArg { callee } => self.apply_value(callee, value),
            Frame::ApplyCallee { arg, env } => {
                let mut env = env;
                let arg = self.eval_expr(arg, &mut env)?;
                self.continue_with_current_frame(
                    arg,
                    Frame::ApplyArg { callee: value },
                    continuation,
                )
            }
            Frame::ApplyAdapterArg {
                function,
                markers,
                source_ret,
                target_ret,
            } => {
                let arg = mark_value(value, &markers);
                let result = self.apply_value(function, arg)?;
                self.continue_with_current_frame(
                    result,
                    Frame::ApplyAdapterResult {
                        markers,
                        source_ret,
                        target_ret,
                    },
                    continuation,
                )
            }
            Frame::ApplyAdapterResult {
                markers,
                source_ret,
                target_ret,
            } => {
                let result = mark_value(value, &markers);
                self.adapt_value(result, &source_ret, &target_ret)
            }
            Frame::DirectBinarySecond {
                op,
                context,
                second_arg,
                env,
            } => {
                let mut env = env;
                let second = self.eval_expr(second_arg, &mut env)?;
                self.continue_with_current_frame(
                    second,
                    Frame::DirectBinaryApply {
                        op,
                        context,
                        first: value,
                    },
                    continuation,
                )
            }
            Frame::DirectBinaryApply { op, context, first } => {
                self.stats.primitive_apply_calls += 1;
                self.stats.primitive_apply_complete += 1;
                let args = [first, value];
                value_result(apply_primitive(op, &context, &args)?)
            }
            Frame::DirectUnaryApply { op, context } => {
                self.stats.primitive_apply_calls += 1;
                self.stats.primitive_apply_complete += 1;
                let args = [value];
                value_result(apply_primitive(op, &context, &args)?)
            }
            Frame::Coerce { source, target } => self.adapt_value(value, &source, &target),
            Frame::ForceThunk { target_value } => {
                let result = self.force_thunk(value)?;
                if matches!(target_value, Type::Thunk { .. }) {
                    return Ok(result);
                }
                self.continue_with_current_frame(result, Frame::ForceValueIfThunk, continuation)
            }
            Frame::MakeFunctionAdapter {
                source,
                target,
                hygiene,
            } => value_result(self.mark_active_created_value(Value::FunctionAdapter(
                FunctionAdapter {
                    source,
                    target,
                    function: Box::new(value),
                    hygiene,
                },
            ))),
            Frame::MarkerScope {
                resume_markers,
                activate_add_ids,
                handler_key,
                inner_frame_count,
            } => {
                self.stats.marker_frame_resume_steps += 1;
                let split_at = continuation.frames.len().saturating_sub(inner_frame_count);
                let mut inner_frames = continuation.frames.split_off(split_at);
                self.stats.marker_frame_calls += 1;
                if resume_markers.is_empty() {
                    self.stats.marker_frame_empty += 1;
                    continuation.frames.append(&mut inner_frames);
                    return value_result(value);
                }
                let guard_len = self.guard_ids.len();
                let frame_len = self.active_frames.len();
                let add_id_len = self.active_add_ids.len();
                let plan_len = self.active_marker_plans.len();
                self.stats.marker_frame_pushes += 1;
                self.push_marker_frame(&resume_markers, activate_add_ids, handler_key.clone());
                continuation.frames.push_back(Frame::MarkerExit {
                    resume_markers,
                    activate_add_ids,
                    handler_key,
                    guard_len,
                    frame_len,
                    add_id_len,
                    plan_len,
                });
                continuation.frames.append(&mut inner_frames);
                value_result(value)
            }
            Frame::RefSetReference { value: expr, env } => {
                let reference = self.force_value_if_thunk(value)?;
                self.continue_with_current_frame(
                    reference,
                    Frame::RefSetForcedReference { value: expr, env },
                    continuation,
                )
            }
            Frame::RefSetForcedReference { value: expr, env } => {
                let mut env = env;
                let value_result = self.eval_expr(expr, &mut env)?;
                self.continue_with_current_frame(
                    value_result,
                    Frame::RefSetValue { reference: value },
                    continuation,
                )
            }
            Frame::RefSetValue { reference } => {
                let value = self.force_value_if_thunk(value)?;
                self.continue_with_current_frame(
                    value,
                    Frame::RefSetForcedValue { reference },
                    continuation,
                )
            }
            Frame::RefSetForcedValue { reference } => {
                let update_effect = self.project_record_field(reference, "update_effect")?;
                let result = self.apply_value(update_effect, Value::Unit)?;
                self.handle_ref_set_result(result, value)
            }
            Frame::RefSetResolvedUnit => value_result(Value::Unit),
            Frame::RefSetEmitResolvedRequest {
                mut request,
                assigned,
                mode,
            } => {
                request.payload = value;
                request.continuation = push_continuation_frame(
                    request.continuation,
                    match mode {
                        RefSetResumeMode::Result => Frame::RefSetHandleResult { assigned },
                        RefSetResumeMode::ValueResult => {
                            Frame::RefSetHandleValueResult { assigned }
                        }
                    },
                );
                Ok(EvalResult::Request(request))
            }
            Frame::MarkValue { markers } => value_result(mark_value(value, &markers)),
            Frame::ResolveRefSetValues {
                values,
                assigned,
                mut out,
                index,
                finish,
            } => {
                out.push(value);
                self.resolve_ref_set_values(values, assigned, out, index + 1, finish)
            }
            Frame::ResolveRefSetFields {
                fields,
                assigned,
                mut out,
                index,
            } => {
                out.push(ValueField {
                    name: fields[index].name.clone(),
                    value,
                });
                self.resolve_ref_set_fields(fields, assigned, out, index + 1)
            }
            Frame::RecordHeadSpread { fields, env } => {
                let spread_fields = self.expect_record(value)?;
                self.eval_record_fields(fields, env, spread_fields, 0)
            }
            Frame::RecordTailFields { spread, env } => {
                let fields = self.expect_record(value)?;
                let mut env = env;
                let spread = self.eval_expr(spread, &mut env)?;
                self.continue_with_current_frame(
                    spread,
                    Frame::RecordTailSpread { fields },
                    continuation,
                )
            }
            Frame::RecordTailSpread { mut fields } => {
                fields.extend(self.expect_record(value)?);
                value_result(Value::Record(fields))
            }
            Frame::RecordField {
                fields,
                env,
                mut values,
                index,
            } => {
                let field = fields[index].clone();
                values.push(ValueField {
                    name: field.name,
                    value,
                });
                self.eval_record_fields(fields, env, values, index + 1)
            }
            Frame::TupleItem {
                items,
                env,
                mut values,
                index,
            } => {
                values.push(value);
                self.eval_tuple_items(items, env, values, index + 1)
            }
            Frame::PolyVariantPayload {
                tag,
                payloads,
                env,
                mut values,
                index,
            } => {
                values.push(value);
                self.eval_poly_variant_payloads(tag, payloads, env, values, index + 1)
            }
            Frame::Select { name, resolution } => match resolution {
                Some(SelectResolution::RecordField) => {
                    value_result(self.project_record_field(value, &name)?)
                }
                Some(SelectResolution::Method { instance }) => {
                    self.apply_direct_instance_if_known(instance, value)
                }
                Some(SelectResolution::TypeclassMethod { .. }) => {
                    Err(RuntimeError::UnsupportedExpr {
                        feature: format!("typeclass method select .{name}"),
                    })
                }
                None => Err(RuntimeError::UnresolvedSelect { name }),
            },
            Frame::CaseScrutineeForce { arms, env } => {
                let scrutinee = self.force_value_if_thunk(value)?;
                self.continue_with_current_frame(
                    scrutinee,
                    Frame::CaseScrutinee { arms, env },
                    continuation,
                )
            }
            Frame::CaseScrutinee { arms, env } => self.eval_case(value, arms, env),
            Frame::CaseGuard {
                scrutinee,
                arms,
                env,
                index,
                arm_env,
                body,
            } => match value {
                Value::Bool(true) => {
                    let mut arm_env = arm_env;
                    self.eval_expr(body, &mut arm_env)
                }
                Value::Bool(false) => self.eval_case_arm(scrutinee, arms, env, index + 1),
                value => Err(RuntimeError::NonBoolGuard { value }),
            },
            Frame::CatchValueGuard {
                value: caught,
                arms,
                env,
                index,
                arm_env,
                body,
            } => match value {
                Value::Bool(true) => {
                    let mut arm_env = arm_env;
                    self.eval_expr(body, &mut arm_env)
                }
                Value::Bool(false) => self.handle_catch_value_arm(caught, arms, env, index + 1),
                value => Err(RuntimeError::NonBoolGuard { value }),
            },
            Frame::CatchRequestGuard {
                request,
                arms,
                env,
                index,
                arm_env,
                body,
            } => match value {
                Value::Bool(true) => {
                    let mut arm_env = arm_env;
                    self.eval_handler_body(body, &mut arm_env)
                }
                Value::Bool(false) => self.handle_catch_request_arm(request, arms, env, index + 1),
                value => Err(RuntimeError::NonBoolGuard { value }),
            },
            Frame::HandlerBodyForce => self.force_value_if_thunk(value),
            Frame::BlockLetValue {
                pat,
                stmts,
                tail,
                env,
                index,
            } => {
                let value = recursive_let_value(&pat, value);
                self.bind_pat(
                    pat,
                    value.clone(),
                    env,
                    BindThen::BlockLet {
                        stmts,
                        tail,
                        index,
                        last: value,
                    },
                )
            }
            Frame::BlockExprValue {
                stmts,
                tail,
                env,
                index,
            } => self.eval_block_step(stmts, tail, env, index + 1, value),
            Frame::BindValue { pat, env, then } => self.bind_pat(pat, value, env, then),
            Frame::BindRecordDefault {
                pat,
                fields,
                spread,
                record_fields,
                markers,
                used,
                env,
                then,
            } => {
                let value = mark_value(value, &markers);
                self.bind_record_field_value(
                    pat,
                    value,
                    fields,
                    spread,
                    record_fields,
                    markers,
                    used,
                    env,
                    then,
                )
            }
        }
    }

    fn close_innermost_marker_request(
        &mut self,
        continuation: &mut Continuation,
        mut request: Request,
    ) -> RuntimeResult {
        let Some(marker_index) = continuation
            .frames
            .iter()
            .rposition(|frame| matches!(frame, Frame::MarkerExit { .. }))
        else {
            unreachable!("caller checked for a marker exit");
        };
        let inner_frames = continuation.frames.split_off(marker_index + 1);
        let Some(Frame::MarkerExit {
            resume_markers,
            activate_add_ids,
            handler_key,
            guard_len,
            frame_len,
            add_id_len,
            plan_len,
        }) = continuation.frames.pop_back()
        else {
            unreachable!("rposition found a marker exit");
        };
        prepend_frames(&mut request.continuation, inner_frames);
        self.pop_marker_frame(guard_len, frame_len, add_id_len, plan_len);
        self.stats.marker_frame_request_closes += 1;
        self.close_marker_request(request, resume_markers, activate_add_ids, handler_key)
    }

    pub(super) fn finish_bind(
        &mut self,
        matched: bool,
        env: CapturedEnv,
        then: BindThen,
    ) -> RuntimeResult {
        match then {
            BindThen::ApplyClosure { body } => {
                if !matched {
                    return Err(RuntimeError::PatternMismatch);
                }
                let mut env = env;
                self.eval_expr(body, &mut env)
            }
            BindThen::BlockLet {
                stmts,
                tail,
                index,
                last,
            } => {
                if !matched {
                    return Err(RuntimeError::PatternMismatch);
                }
                self.eval_block_step(stmts, tail, env, index + 1, last)
            }
            BindThen::CaseArm {
                scrutinee,
                arms,
                env: outer_env,
                index,
                arm,
            } => {
                if !matched {
                    return self.eval_case_arm(scrutinee, arms, outer_env, index + 1);
                }
                let mut arm_env = env;
                let Some(guard) = arm.guard else {
                    return self.eval_expr(arm.body, &mut arm_env);
                };
                let guard_result = self.eval_expr(guard, &mut arm_env)?;
                self.continue_with_frame(
                    guard_result,
                    Frame::CaseGuard {
                        scrutinee,
                        arms,
                        env: outer_env,
                        index,
                        arm_env,
                        body: arm.body,
                    },
                )
            }
            BindThen::CatchValue {
                value,
                arms,
                env: outer_env,
                index,
                arm,
            } => {
                if !matched {
                    return self.handle_catch_value_arm(value, arms, outer_env, index + 1);
                }
                let mut arm_env = env;
                let Some(guard) = arm.guard else {
                    return self.eval_expr(arm.body, &mut arm_env);
                };
                let guard_result = self.eval_expr(guard, &mut arm_env)?;
                self.continue_with_frame(
                    guard_result,
                    Frame::CatchValueGuard {
                        value,
                        arms,
                        env: outer_env,
                        index,
                        arm_env,
                        body: arm.body,
                    },
                )
            }
            BindThen::CatchRequestPayload {
                request,
                arms,
                env: outer_env,
                index,
                arm,
            } => {
                if !matched {
                    return self.handle_catch_request_arm(request, arms, outer_env, index + 1);
                }
                self.stats.catch_request_matches += 1;
                if let Some(continuation) = arm.continuation.clone() {
                    let id = self.store_continuation(request.continuation.clone());
                    return self.bind_pat(
                        continuation,
                        Value::Continuation(id),
                        env,
                        BindThen::CatchRequestContinuation {
                            request,
                            arms,
                            env: outer_env,
                            index,
                            guard: arm.guard,
                            body: arm.body,
                        },
                    );
                }
                self.finish_catch_request_match(
                    request, arms, outer_env, index, env, arm.guard, arm.body,
                )
            }
            BindThen::CatchRequestContinuation {
                request,
                arms,
                env: outer_env,
                index,
                guard,
                body,
            } => {
                if !matched {
                    return self.handle_catch_request_arm(request, arms, outer_env, index + 1);
                }
                self.finish_catch_request_match(request, arms, outer_env, index, env, guard, body)
            }
            BindThen::Sequence { entries, then } => {
                if !matched {
                    return self.finish_bind(false, env, *then);
                }
                self.bind_pat_sequence(entries, env, *then)
            }
            BindThen::Or {
                right,
                value,
                env: right_env,
                then,
            } => {
                if matched {
                    return self.finish_bind(true, env, *then);
                }
                self.bind_pat(right, value, right_env, *then)
            }
            BindThen::As { def, value, then } => {
                if !matched {
                    return self.finish_bind(false, env, *then);
                }
                let mut env = env;
                env.insert(def, value);
                self.finish_bind(true, env, *then)
            }
            BindThen::RecordField {
                fields,
                spread,
                record_fields,
                markers,
                used,
                then,
            } => {
                if !matched {
                    return self.finish_bind(false, env, *then);
                }
                self.bind_record_pat(fields, spread, record_fields, markers, used, env, *then)
            }
        }
    }

    fn finish_catch_request_match(
        &mut self,
        request: Request,
        arms: RuntimeCatchArms,
        outer_env: CapturedEnv,
        index: usize,
        mut arm_env: CapturedEnv,
        guard: Option<ExprId>,
        body: ExprId,
    ) -> RuntimeResult {
        let Some(guard) = guard else {
            return self.eval_handler_body(body, &mut arm_env);
        };
        let guard_result = self.eval_expr(guard, &mut arm_env)?;
        self.continue_with_frame(
            guard_result,
            Frame::CatchRequestGuard {
                request,
                arms,
                env: outer_env,
                index,
                arm_env,
                body,
            },
        )
    }
}

pub(super) fn push_frame(mut request: Request, frame: Frame) -> Request {
    request.continuation.frames.push_front(frame);
    request
}

pub(super) fn push_continuation_frame(
    mut continuation: Continuation,
    frame: Frame,
) -> Continuation {
    continuation.frames.push_front(frame);
    continuation
}

fn prepend_frames(continuation: &mut Continuation, mut frames: VecDeque<Frame>) {
    frames.append(&mut continuation.frames);
    continuation.frames = frames;
}
