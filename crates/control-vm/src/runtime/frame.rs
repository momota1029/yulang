use super::*;

#[derive(Clone)]
pub(super) struct Continuation {
    pub(super) frames: VecDeque<SharedFrame>,
    pub(super) marker_scopes: Option<SharedMarkerScopes>,
}

impl Default for Continuation {
    fn default() -> Self {
        Self {
            frames: VecDeque::new(),
            marker_scopes: None,
        }
    }
}

#[derive(Clone)]
pub(super) struct ContinuationMarkerScope {
    pub(super) frames_remaining: usize,
    pub(super) resume_markers: SharedMarkers,
    pub(super) activate_add_ids: bool,
    pub(super) handler_key: Option<InternedPathPrefix>,
}

struct ActiveContinuationMarkerScope {
    frames_remaining: usize,
    resume_markers: SharedMarkers,
    activate_add_ids: bool,
    handler_key: Option<InternedPathPrefix>,
    checkpoint: MarkerCheckpoint,
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
        arg_markers: SharedMarkers,
        ret_markers: SharedMarkers,
        source_ret: Type,
        target_ret: Type,
    },
    ApplyAdapterResult {
        ret_markers: SharedMarkers,
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
        expr: ExprId,
    },
    ForceThunk {
        expr: ExprId,
    },
    MakeFunctionAdapter {
        expr: ExprId,
        markers: Option<SharedMarkers>,
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
        markers: SharedMarkers,
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
        record: ExprId,
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
        record: ExprId,
        env: CapturedEnv,
        values: Vec<ValueField>,
        index: usize,
    },
    TupleItem {
        tuple: ExprId,
        env: CapturedEnv,
        values: Vec<Value>,
        index: usize,
    },
    PolyVariantPayload {
        variant: ExprId,
        env: CapturedEnv,
        values: Vec<Value>,
        index: usize,
    },
    Select {
        name: String,
        resolution: Option<SelectResolution>,
    },
    CaseScrutineeForce {
        arms: RuntimeCaseArms,
        env: CapturedEnv,
    },
    CaseScrutinee {
        arms: RuntimeCaseArms,
        env: CapturedEnv,
    },
    CaseGuard {
        scrutinee: Value,
        arms: RuntimeCaseArms,
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
        stmts: RuntimeBlockStmts,
        tail: Option<ExprId>,
        env: CapturedEnv,
        index: usize,
    },
    BlockExprValue {
        stmts: RuntimeBlockStmts,
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
        record_fields: SharedValueFields,
        markers: SharedMarkers,
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
        stmts: RuntimeBlockStmts,
        tail: Option<ExprId>,
        index: usize,
        last: Value,
    },
    CaseArm {
        scrutinee: Value,
        arms: RuntimeCaseArms,
        env: CapturedEnv,
        index: usize,
    },
    CatchValue {
        value: Value,
        arms: RuntimeCatchArms,
        env: CapturedEnv,
        index: usize,
    },
    CatchRequestPayload {
        request: Request,
        arms: RuntimeCatchArms,
        env: CapturedEnv,
        index: usize,
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
        remaining_reversed: Vec<(Pat, Value)>,
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
        record_fields: SharedValueFields,
        markers: SharedMarkers,
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
        )
    }

    fn applies_borrowed_value(&self) -> bool {
        matches!(
            self,
            Frame::AdaptValue { .. }
                | Frame::WrapThunkValue
                | Frame::ForceValueIfThunk
                | Frame::ApplyForcedThunk { .. }
                | Frame::ApplyArg { .. }
                | Frame::ApplyCallee { .. }
                | Frame::ApplyAdapterArg { .. }
                | Frame::ApplyAdapterResult { .. }
                | Frame::DirectBinaryApply { .. }
                | Frame::DirectUnaryApply { .. }
                | Frame::Coerce { .. }
                | Frame::ForceThunk { .. }
                | Frame::MarkValue { .. }
                | Frame::Select { .. }
                | Frame::CaseScrutineeForce { .. }
                | Frame::CaseScrutinee { .. }
                | Frame::HandlerBodyForce
                | Frame::BlockLetValue { .. }
                | Frame::BlockExprValue { .. }
                | Frame::RefSetResolvedUnit
        )
    }

    fn clone_bucket(&self) -> FrameCloneBucket {
        match self {
            Frame::ApplyForcedThunk { .. }
            | Frame::ApplyArg { .. }
            | Frame::ApplyCallee { .. }
            | Frame::ApplyAdapterArg { .. }
            | Frame::ApplyAdapterResult { .. } => FrameCloneBucket::Apply,
            Frame::AdaptValue { .. }
            | Frame::WrapThunkValue
            | Frame::ForceValueIfThunk
            | Frame::DirectBinarySecond { .. }
            | Frame::DirectBinaryApply { .. }
            | Frame::DirectUnaryApply { .. }
            | Frame::Coerce { .. }
            | Frame::ForceThunk { .. }
            | Frame::MakeFunctionAdapter { .. }
            | Frame::HandlerBodyForce => FrameCloneBucket::Direct,
            Frame::MarkValue { .. }
            | Frame::RecordHeadSpread { .. }
            | Frame::RecordTailFields { .. }
            | Frame::RecordTailSpread { .. }
            | Frame::RecordField { .. }
            | Frame::TupleItem { .. }
            | Frame::PolyVariantPayload { .. }
            | Frame::Select { .. } => FrameCloneBucket::Data,
            Frame::CaseScrutineeForce { .. }
            | Frame::CaseScrutinee { .. }
            | Frame::CaseGuard { .. } => FrameCloneBucket::Case,
            Frame::CatchResult { .. }
            | Frame::CatchValueGuard { .. }
            | Frame::CatchRequestGuard { .. } => FrameCloneBucket::Catch,
            Frame::BlockLetValue { .. } | Frame::BlockExprValue { .. } => FrameCloneBucket::Block,
            Frame::BindValue { .. } | Frame::BindRecordDefault { .. } => FrameCloneBucket::Bind,
            Frame::RefSetReference { .. }
            | Frame::RefSetForcedReference { .. }
            | Frame::RefSetValue { .. }
            | Frame::RefSetForcedValue { .. }
            | Frame::RefSetResolvedUnit
            | Frame::RefSetHandleResult { .. }
            | Frame::RefSetHandleValueResult { .. }
            | Frame::RefSetEmitResolvedRequest { .. }
            | Frame::ResolveRefSetValues { .. }
            | Frame::ResolveRefSetFields { .. } => FrameCloneBucket::RefSet,
        }
    }
}

#[derive(Clone, Copy)]
enum FrameCloneBucket {
    Apply,
    Direct,
    Data,
    Case,
    Catch,
    Block,
    Bind,
    RefSet,
}

impl<'a> Runtime<'a> {
    pub(super) fn resume(&mut self, mut continuation: Continuation, value: Value) -> RuntimeResult {
        let checkpoint = self.marker_checkpoint();
        let mut marker_scopes = self.enter_continuation_marker_scopes(std::mem::replace(
            &mut continuation.marker_scopes,
            None,
        ));
        let mut request_close_offset = 0;
        let result = self.resume_with_marker_scopes(
            &mut continuation,
            &mut marker_scopes,
            &mut request_close_offset,
            value,
        );
        self.pop_marker_frame(
            checkpoint.guard_len,
            checkpoint.frame_len,
            checkpoint.handler_frame_len,
            checkpoint.add_id_len,
            checkpoint.plan_len,
        );
        result
    }

    fn resume_with_marker_scopes(
        &mut self,
        continuation: &mut Continuation,
        marker_scopes: &mut Vec<ActiveContinuationMarkerScope>,
        request_close_offset: &mut usize,
        mut value: Value,
    ) -> RuntimeResult {
        value = match self.close_completed_marker_scopes(
            EvalResult::Value(value),
            marker_scopes,
            *request_close_offset,
        )? {
            EvalResult::Value(value) => value,
            EvalResult::Request(request) => {
                return self.finish_resume_request(
                    request,
                    continuation,
                    marker_scopes,
                    request_close_offset,
                );
            }
        };

        'resume: loop {
            let Some(frame) = continuation.frames.pop_back() else {
                return value_result(value);
            };
            consume_marker_frame(&mut self.stats, marker_scopes);
            self.stats.request_resume_steps += 1;
            let result = if frame.handles_eval_result() {
                self.apply_shared_result_frame(frame, EvalResult::Value(value))?
            } else {
                self.apply_shared_value_frame(frame, &mut *continuation, marker_scopes, value)?
            };
            let result =
                self.close_completed_marker_scopes(result, marker_scopes, *request_close_offset)?;
            match result {
                EvalResult::Value(next) => value = next,
                EvalResult::Request(request) => {
                    match self.finish_resume_request(
                        request,
                        continuation,
                        marker_scopes,
                        request_close_offset,
                    )? {
                        EvalResult::Value(next) => {
                            value = next;
                            continue 'resume;
                        }
                        EvalResult::Request(request) => return Ok(EvalResult::Request(request)),
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
                let mut marker_scopes = Vec::new();
                let result = if frame.handles_eval_result() {
                    self.apply_result_frame(frame, EvalResult::Value(value))?
                } else {
                    self.apply_frame(frame, &mut continuation, &mut marker_scopes, value)?
                };
                self.finish_inline_result(result, continuation)
            }
            EvalResult::Request(request) => {
                self.stats.continue_with_requests += 1;
                Ok(EvalResult::Request(push_frame(
                    &mut self.stats,
                    request,
                    frame,
                )))
            }
        }
    }

    fn continue_with_current_frame(
        &mut self,
        result: EvalResult,
        frame: Frame,
        continuation: &mut Continuation,
        marker_scopes: &mut [ActiveContinuationMarkerScope],
    ) -> RuntimeResult {
        match result {
            EvalResult::Value(value) => {
                self.stats.continue_with_values += 1;
                self.apply_frame(frame, continuation, marker_scopes, value)
            }
            EvalResult::Request(request) => {
                self.stats.continue_with_requests += 1;
                Ok(EvalResult::Request(push_frame(
                    &mut self.stats,
                    request,
                    frame,
                )))
            }
        }
    }

    fn finish_inline_result(
        &mut self,
        result: EvalResult,
        mut continuation: Continuation,
    ) -> RuntimeResult {
        match result {
            EvalResult::Value(value)
                if continuation.frames.is_empty() && continuation.marker_scopes.is_none() =>
            {
                value_result(value)
            }
            EvalResult::Value(value) => self.resume(continuation, value),
            EvalResult::Request(request) => self.finish_inline_request(request, &mut continuation),
        }
    }

    fn finish_inline_request(
        &mut self,
        request: Request,
        continuation: &mut Continuation,
    ) -> RuntimeResult {
        debug_assert!(continuation.marker_scopes.is_none());
        let mut result = EvalResult::Request(request);
        loop {
            while continuation
                .frames
                .back()
                .is_some_and(|frame| frame.handles_eval_result())
            {
                let frame = continuation.frames.pop_back().expect("checked frame");
                self.stats.request_resume_steps += 1;
                result = self.apply_shared_result_frame(frame, result)?;
                if let EvalResult::Value(value) = result {
                    return self.resume(std::mem::take(continuation), value);
                }
            }
            let EvalResult::Request(request) = result else {
                unreachable!("value result is handled above");
            };
            let mut request = request;
            prepend_frames(
                &mut request.continuation,
                std::mem::take(&mut continuation.frames),
            );
            return Ok(EvalResult::Request(request));
        }
    }

    fn marker_checkpoint(&self) -> MarkerCheckpoint {
        MarkerCheckpoint {
            guard_len: self.guard_ids.len(),
            frame_len: self.active_frames.len(),
            handler_frame_len: self.active_handler_frames.len(),
            add_id_len: self.active_add_ids.len(),
            plan_len: self.active_marker_plans.len(),
        }
    }

    pub(super) fn clone_continuation_for_capture(
        &mut self,
        continuation: &Continuation,
    ) -> Continuation {
        self.stats.continuation_capture_clones += 1;
        self.record_continuation_clone_shape(continuation);
        continuation.clone()
    }

    pub(super) fn clone_continuation_for_invoke(
        &mut self,
        continuation: Continuation,
    ) -> Continuation {
        self.stats.continuation_invoke_clones += 1;
        self.record_continuation_clone_shape(&continuation);
        continuation
    }

    fn record_continuation_clone_shape(&mut self, continuation: &Continuation) {
        let frame_count = continuation.frames.len() as u64;
        let marker_scope_count = continuation
            .marker_scopes
            .as_ref()
            .map_or(0, |scopes| scopes.len() as u64);
        self.stats.continuation_frames_cloned += frame_count;
        self.stats.continuation_marker_scopes_cloned += marker_scope_count;
        self.stats.max_continuation_frames = self.stats.max_continuation_frames.max(frame_count);
    }

    fn apply_shared_result_frame(
        &mut self,
        frame: SharedFrame,
        result: EvalResult,
    ) -> RuntimeResult {
        match Rc::try_unwrap(frame) {
            Ok(frame) => self.apply_result_frame(frame, result),
            Err(frame) => self.apply_borrowed_result_frame(&frame, result),
        }
    }

    fn apply_shared_value_frame(
        &mut self,
        frame: SharedFrame,
        continuation: &mut Continuation,
        marker_scopes: &mut [ActiveContinuationMarkerScope],
        value: Value,
    ) -> RuntimeResult {
        match Rc::try_unwrap(frame) {
            Ok(frame) => self.apply_frame(frame, continuation, marker_scopes, value),
            Err(frame) => {
                if frame.applies_borrowed_value() {
                    return self.apply_borrowed_value_frame(
                        &frame,
                        continuation,
                        marker_scopes,
                        value,
                    );
                }
                let frame = self.clone_shared_frame(&frame);
                self.apply_frame(frame, continuation, marker_scopes, value)
            }
        }
    }

    fn clone_shared_frame(&mut self, frame: &Frame) -> Frame {
        self.stats.shared_frame_unwrap_clones += 1;
        match frame.clone_bucket() {
            FrameCloneBucket::Apply => self.stats.shared_frame_unwrap_apply_clones += 1,
            FrameCloneBucket::Direct => self.stats.shared_frame_unwrap_direct_clones += 1,
            FrameCloneBucket::Data => self.stats.shared_frame_unwrap_data_clones += 1,
            FrameCloneBucket::Case => self.stats.shared_frame_unwrap_case_clones += 1,
            FrameCloneBucket::Catch => self.stats.shared_frame_unwrap_catch_clones += 1,
            FrameCloneBucket::Block => self.stats.shared_frame_unwrap_block_clones += 1,
            FrameCloneBucket::Bind => self.stats.shared_frame_unwrap_bind_clones += 1,
            FrameCloneBucket::RefSet => self.stats.shared_frame_unwrap_refset_clones += 1,
        }
        frame.clone()
    }

    fn apply_borrowed_result_frame(&mut self, frame: &Frame, result: EvalResult) -> RuntimeResult {
        match frame {
            Frame::CatchResult { arms, env } => {
                self.handle_catch_result(result, arms.clone(), env.clone())
            }
            Frame::RefSetHandleResult { assigned } => {
                self.handle_ref_set_result(result, assigned.clone())
            }
            Frame::RefSetHandleValueResult { assigned } => {
                self.handle_ref_set_value_result(result, assigned.clone())
            }
            _ => unreachable!("only result frames use apply_shared_result_frame"),
        }
    }

    fn apply_borrowed_value_frame(
        &mut self,
        frame: &Frame,
        continuation: &mut Continuation,
        marker_scopes: &mut [ActiveContinuationMarkerScope],
        value: Value,
    ) -> RuntimeResult {
        match frame {
            Frame::CatchResult { .. }
            | Frame::RefSetHandleResult { .. }
            | Frame::RefSetHandleValueResult { .. } => {
                unreachable!("result frames are handled before value frames")
            }
            Frame::AdaptValue { source, target } => self.adapt_value(value, source, target),
            Frame::WrapThunkValue => {
                value_result(Value::Thunk(Rc::new(Thunk::Value(Box::new(value)))))
            }
            Frame::ForceValueIfThunk => self.force_value_if_thunk(value),
            Frame::ApplyForcedThunk { arg } => self.apply_scoped_value(value, arg.clone()),
            Frame::ApplyArg { callee } => self.apply_scoped_value(callee.clone(), value),
            Frame::ApplyCallee { arg, env } => {
                let mut env = env.clone();
                let arg = self.eval_expr(*arg, &mut env)?;
                self.continue_with_current_frame(
                    arg,
                    Frame::ApplyArg { callee: value },
                    continuation,
                    marker_scopes,
                )
            }
            Frame::ApplyAdapterArg {
                function,
                arg_markers,
                ret_markers,
                source_ret,
                target_ret,
            } => {
                let arg = mark_value_shared(value, arg_markers);
                let result = self.apply_value(function.clone(), arg)?;
                self.continue_with_current_frame(
                    result,
                    Frame::ApplyAdapterResult {
                        ret_markers: ret_markers.clone(),
                        source_ret: source_ret.clone(),
                        target_ret: target_ret.clone(),
                    },
                    continuation,
                    marker_scopes,
                )
            }
            Frame::ApplyAdapterResult {
                ret_markers,
                source_ret,
                target_ret,
            } => {
                let result = mark_value_shared(value, ret_markers);
                self.adapt_value(result, source_ret, target_ret)
            }
            Frame::DirectBinaryApply { op, context, first } => {
                self.stats.primitive_apply_calls += 1;
                self.stats.primitive_apply_complete += 1;
                let args = [first.clone(), value];
                value_result(apply_primitive(*op, context, &args)?)
            }
            Frame::DirectUnaryApply { op, context } => {
                self.stats.primitive_apply_calls += 1;
                self.stats.primitive_apply_complete += 1;
                let args = [value];
                value_result(apply_primitive(*op, context, &args)?)
            }
            Frame::Coerce { expr } => {
                let (source, target) = self.coerce_types(*expr)?;
                self.adapt_value(value, &source, &target)
            }
            Frame::ForceThunk { expr } => {
                let target_value_is_thunk = self.force_thunk_target_value_is_thunk(*expr)?;
                let result = self.force_thunk(value)?;
                if target_value_is_thunk {
                    return Ok(result);
                }
                self.continue_with_current_frame(
                    result,
                    Frame::ForceValueIfThunk,
                    continuation,
                    marker_scopes,
                )
            }
            Frame::MarkValue { markers } => value_result(mark_value_shared(value, markers)),
            Frame::Select { name, resolution } => match resolution {
                Some(SelectResolution::RecordField) => {
                    value_result(self.project_record_field(value, name)?)
                }
                Some(SelectResolution::Method { instance }) => {
                    self.apply_direct_instance_if_known(*instance, value)
                }
                Some(SelectResolution::TypeclassMethod { .. }) => {
                    Err(RuntimeError::UnsupportedExpr {
                        feature: format!("typeclass method select .{name}"),
                    })
                }
                None => Err(RuntimeError::UnresolvedSelect { name: name.clone() }),
            },
            Frame::CaseScrutineeForce { arms, env } => {
                let scrutinee = self.force_value_if_thunk(value)?;
                self.continue_with_current_frame(
                    scrutinee,
                    Frame::CaseScrutinee {
                        arms: arms.clone(),
                        env: env.clone(),
                    },
                    continuation,
                    marker_scopes,
                )
            }
            Frame::CaseScrutinee { arms, env } => self.eval_case(value, arms.clone(), env.clone()),
            Frame::HandlerBodyForce => self.force_value_if_thunk(value),
            Frame::BlockLetValue {
                pat,
                stmts,
                tail,
                env,
                index,
            } => {
                let value = recursive_let_value(pat, value);
                self.bind_pat(
                    pat.clone(),
                    value.clone(),
                    env.clone(),
                    BindThen::BlockLet {
                        stmts: stmts.clone(),
                        tail: *tail,
                        index: *index,
                        last: value,
                    },
                )
            }
            Frame::BlockExprValue {
                stmts,
                tail,
                env,
                index,
            } => self.eval_block_step(stmts.clone(), *tail, env.clone(), index + 1, value),
            Frame::RefSetResolvedUnit => value_result(Value::Unit),
            _ => unreachable!("borrowed value frame should be checked before apply"),
        }
    }

    fn enter_continuation_marker_scopes(
        &mut self,
        scopes: Option<SharedMarkerScopes>,
    ) -> Vec<ActiveContinuationMarkerScope> {
        let Some(scopes) = scopes else {
            return Vec::new();
        };
        let mut active = Vec::with_capacity(scopes.len());
        for scope in scopes.iter().cloned() {
            self.stats.marker_frame_resume_steps += 1;
            self.stats.marker_frame_calls += 1;
            let checkpoint = self.marker_checkpoint();
            if scope.resume_markers.is_empty() {
                self.stats.marker_frame_empty += 1;
            } else {
                self.stats.marker_frame_pushes += 1;
                self.push_shared_marker_frame(
                    scope.resume_markers.clone(),
                    scope.activate_add_ids,
                    scope.handler_key.clone(),
                );
            }
            active.push(ActiveContinuationMarkerScope {
                frames_remaining: scope.frames_remaining,
                resume_markers: scope.resume_markers,
                activate_add_ids: scope.activate_add_ids,
                handler_key: scope.handler_key,
                checkpoint,
            });
        }
        active
    }

    fn finish_resume_request(
        &mut self,
        request: Request,
        continuation: &mut Continuation,
        marker_scopes: &mut Vec<ActiveContinuationMarkerScope>,
        request_close_offset: &mut usize,
    ) -> RuntimeResult {
        let mut result = EvalResult::Request(request);
        loop {
            result =
                self.close_completed_marker_scopes(result, marker_scopes, *request_close_offset)?;
            while continuation
                .frames
                .back()
                .is_some_and(|frame| frame.handles_eval_result())
            {
                let frame = continuation.frames.pop_back().expect("checked frame");
                consume_marker_frame(&mut self.stats, marker_scopes);
                self.stats.request_resume_steps += 1;
                result = self.apply_shared_result_frame(frame, result)?;
                result = self.close_completed_marker_scopes(
                    result,
                    marker_scopes,
                    *request_close_offset,
                )?;
                if matches!(result, EvalResult::Value(_)) {
                    return Ok(result);
                }
            }

            result =
                self.close_completed_marker_scopes(result, marker_scopes, *request_close_offset)?;
            let EvalResult::Request(request) = result else {
                return Ok(result);
            };
            if !marker_scopes.is_empty() {
                result = self.close_innermost_marker_request(
                    continuation,
                    marker_scopes,
                    request,
                    request_close_offset,
                )?;
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

    fn close_completed_marker_scopes(
        &mut self,
        mut result: EvalResult,
        marker_scopes: &mut Vec<ActiveContinuationMarkerScope>,
        request_close_offset: usize,
    ) -> RuntimeResult {
        self.stats.marker_scope_close_calls += 1;
        while marker_scopes
            .last()
            .is_some_and(|scope| marker_scope_remaining(scope, request_close_offset) == 0)
        {
            let scope = marker_scopes.pop().expect("checked marker scope");
            self.stats.marker_scope_close_pops += 1;
            result = self.close_active_marker_scope_result(result, scope)?;
        }
        Ok(result)
    }

    fn close_innermost_marker_request(
        &mut self,
        continuation: &mut Continuation,
        marker_scopes: &mut Vec<ActiveContinuationMarkerScope>,
        mut request: Request,
        request_close_offset: &mut usize,
    ) -> RuntimeResult {
        let scope = marker_scopes
            .pop()
            .expect("request should be inside an active marker scope");
        self.stats.marker_scope_request_closes += 1;
        let frames_remaining = marker_scope_remaining(&scope, *request_close_offset);
        let inner_frames = split_back_frames(&mut continuation.frames, frames_remaining);
        *request_close_offset += frames_remaining;
        prepend_frames(&mut request.continuation, inner_frames);
        self.close_active_marker_scope_result(EvalResult::Request(request), scope)
    }

    fn close_active_marker_scope_result(
        &mut self,
        result: EvalResult,
        scope: ActiveContinuationMarkerScope,
    ) -> RuntimeResult {
        let checkpoint = scope.checkpoint;
        let handler_boundary = match &result {
            EvalResult::Request(request) => {
                self.handler_boundary_for_request(request, scope.handler_key, checkpoint.frame_len)
            }
            EvalResult::Value(_) => None,
        };
        self.pop_marker_frame(
            checkpoint.guard_len,
            checkpoint.frame_len,
            checkpoint.handler_frame_len,
            checkpoint.add_id_len,
            checkpoint.plan_len,
        );
        self.close_shared_resume_marker_frame_result(
            result,
            scope.resume_markers,
            scope.activate_add_ids,
            scope.handler_key,
            handler_boundary,
        )
    }

    fn apply_result_frame(&mut self, frame: Frame, result: EvalResult) -> RuntimeResult {
        match frame {
            Frame::CatchResult { arms, env } => self.handle_catch_result(result, arms, env),
            Frame::RefSetHandleResult { assigned } => self.handle_ref_set_result(result, assigned),
            Frame::RefSetHandleValueResult { assigned } => {
                self.handle_ref_set_value_result(result, assigned)
            }
            frame => {
                let EvalResult::Value(value) = result else {
                    unreachable!("request result is only delivered to result frames");
                };
                let mut continuation = Continuation::default();
                let mut marker_scopes = Vec::new();
                self.apply_frame(frame, &mut continuation, &mut marker_scopes, value)
            }
        }
    }

    fn apply_frame(
        &mut self,
        frame: Frame,
        continuation: &mut Continuation,
        marker_scopes: &mut [ActiveContinuationMarkerScope],
        value: Value,
    ) -> RuntimeResult {
        match frame {
            Frame::CatchResult { .. }
            | Frame::RefSetHandleResult { .. }
            | Frame::RefSetHandleValueResult { .. } => {
                unreachable!("result frames are handled before value frames")
            }
            Frame::AdaptValue { source, target } => self.adapt_value(value, &source, &target),
            Frame::WrapThunkValue => {
                value_result(Value::Thunk(Rc::new(Thunk::Value(Box::new(value)))))
            }
            Frame::ForceValueIfThunk => self.force_value_if_thunk(value),
            Frame::ApplyForcedThunk { arg } => self.apply_scoped_value(value, arg),
            Frame::ApplyArg { callee } => self.apply_scoped_value(callee, value),
            Frame::ApplyCallee { arg, env } => {
                let mut env = env;
                let arg = self.eval_expr(arg, &mut env)?;
                self.continue_with_current_frame(
                    arg,
                    Frame::ApplyArg { callee: value },
                    continuation,
                    marker_scopes,
                )
            }
            Frame::ApplyAdapterArg {
                function,
                arg_markers,
                ret_markers,
                source_ret,
                target_ret,
            } => {
                let arg = mark_value_shared(value, &arg_markers);
                let result = self.apply_value(function, arg)?;
                self.continue_with_current_frame(
                    result,
                    Frame::ApplyAdapterResult {
                        ret_markers,
                        source_ret,
                        target_ret,
                    },
                    continuation,
                    marker_scopes,
                )
            }
            Frame::ApplyAdapterResult {
                ret_markers,
                source_ret,
                target_ret,
            } => {
                let result = mark_value_shared(value, &ret_markers);
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
                    marker_scopes,
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
            Frame::Coerce { expr } => {
                let (source, target) = self.coerce_types(expr)?;
                self.adapt_value(value, &source, &target)
            }
            Frame::ForceThunk { expr } => {
                let target_value_is_thunk = self.force_thunk_target_value_is_thunk(expr)?;
                let result = self.force_thunk(value)?;
                if target_value_is_thunk {
                    return Ok(result);
                }
                self.continue_with_current_frame(
                    result,
                    Frame::ForceValueIfThunk,
                    continuation,
                    marker_scopes,
                )
            }
            Frame::MakeFunctionAdapter { expr, markers } => {
                let value = self.function_adapter_value(expr, value.clone())?;
                value_result(match markers {
                    Some(markers) => mark_value_shared(value, &markers),
                    None => value,
                })
            }
            Frame::RefSetReference { value: expr, env } => {
                let reference = self.force_value_if_thunk(value)?;
                self.continue_with_current_frame(
                    reference,
                    Frame::RefSetForcedReference { value: expr, env },
                    continuation,
                    marker_scopes,
                )
            }
            Frame::RefSetForcedReference { value: expr, env } => {
                let mut env = env;
                let value_result = self.eval_expr(expr, &mut env)?;
                self.continue_with_current_frame(
                    value_result,
                    Frame::RefSetValue { reference: value },
                    continuation,
                    marker_scopes,
                )
            }
            Frame::RefSetValue { reference } => {
                let value = self.force_value_if_thunk(value)?;
                self.continue_with_current_frame(
                    value,
                    Frame::RefSetForcedValue { reference },
                    continuation,
                    marker_scopes,
                )
            }
            Frame::RefSetForcedValue { reference } => {
                let update_effect = self.project_record_field(reference, "update_effect")?;
                let result = self.apply_scoped_value(update_effect, Value::Unit)?;
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
                    &mut self.stats,
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
            Frame::MarkValue { markers } => value_result(mark_value_shared(value, &markers)),
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
            Frame::RecordHeadSpread { record, env } => {
                let spread_fields = self.expect_record(value)?;
                self.eval_record_fields(record, env, spread_fields, 0)
            }
            Frame::RecordTailFields { spread, env } => {
                let fields = self.expect_record(value)?;
                let mut env = env;
                let spread = self.eval_expr(spread, &mut env)?;
                self.continue_with_current_frame(
                    spread,
                    Frame::RecordTailSpread { fields },
                    continuation,
                    marker_scopes,
                )
            }
            Frame::RecordTailSpread { mut fields } => {
                fields.extend(self.expect_record(value)?);
                value_result(Value::Record(shared_value_fields(fields)))
            }
            Frame::RecordField {
                record,
                env,
                mut values,
                index,
            } => {
                values.push(ValueField {
                    name: self.record_field_name(record, index)?,
                    value,
                });
                self.eval_record_fields(record, env, values, index + 1)
            }
            Frame::TupleItem {
                tuple,
                env,
                mut values,
                index,
            } => {
                values.push(value);
                self.eval_tuple_items(tuple, env, values, index + 1)
            }
            Frame::PolyVariantPayload {
                variant,
                env,
                mut values,
                index,
            } => {
                values.push(value);
                self.eval_poly_variant_payloads(variant, env, values, index + 1)
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
                    marker_scopes,
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
                let value = mark_value_shared(value, &markers);
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
            } => {
                if !matched {
                    return self.eval_case_arm(scrutinee, arms, outer_env, index + 1);
                }
                let mut arm_env = env;
                let guard = arms[index].guard;
                let body = arms[index].body;
                let Some(guard) = guard else {
                    return self.eval_expr(body, &mut arm_env);
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
                        body,
                    },
                )
            }
            BindThen::CatchValue {
                value,
                arms,
                env: outer_env,
                index,
            } => {
                if !matched {
                    return self.handle_catch_value_arm(value, arms, outer_env, index + 1);
                }
                let mut arm_env = env;
                let guard = arms[index].guard;
                let body = arms[index].body;
                let Some(guard) = guard else {
                    return self.eval_expr(body, &mut arm_env);
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
                        body,
                    },
                )
            }
            BindThen::CatchRequestPayload {
                request,
                arms,
                env: outer_env,
                index,
            } => {
                if !matched {
                    return self.handle_catch_request_arm(request, arms, outer_env, index + 1);
                }
                self.stats.catch_request_matches += 1;
                let continuation = arms[index].continuation.clone();
                let guard = arms[index].guard;
                let body = arms[index].body;
                if let Some(continuation) = continuation {
                    let captured = self.clone_continuation_for_capture(&request.continuation);
                    let id = self.store_continuation(captured);
                    return self.bind_pat(
                        continuation,
                        Value::Continuation(id),
                        env,
                        BindThen::CatchRequestContinuation {
                            request,
                            arms,
                            env: outer_env,
                            index,
                            guard,
                            body,
                        },
                    );
                }
                self.finish_catch_request_match(request, arms, outer_env, index, env, guard, body)
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
            BindThen::Sequence {
                remaining_reversed,
                then,
            } => {
                if !matched {
                    return self.finish_bind(false, env, *then);
                }
                self.bind_pat_sequence_reversed(remaining_reversed, env, *then)
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
                let stats = env.insert(def, value);
                self.record_env_insert(stats);
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

pub(super) fn push_frame(stats: &mut RuntimeStats, mut request: Request, frame: Frame) -> Request {
    request
        .continuation
        .frames
        .push_front(shared_frame(stats, frame));
    request
}

pub(super) fn push_continuation_frame(
    stats: &mut RuntimeStats,
    mut continuation: Continuation,
    frame: Frame,
) -> Continuation {
    continuation.frames.push_front(shared_frame(stats, frame));
    continuation
}

fn consume_marker_frame(
    stats: &mut RuntimeStats,
    marker_scopes: &mut [ActiveContinuationMarkerScope],
) {
    let depth = marker_scopes.len() as u64;
    stats.marker_scope_consume_calls += 1;
    if depth > 0 {
        stats.marker_scope_consume_nonempty_calls += 1;
    }
    stats.marker_scope_frame_touches += depth;
    stats.marker_scope_consume_touches += depth;
    stats.marker_scope_max_depth = stats.marker_scope_max_depth.max(depth);
    for scope in marker_scopes {
        if scope.frames_remaining > 0 {
            scope.frames_remaining -= 1;
        }
    }
}

fn marker_scope_remaining(
    scope: &ActiveContinuationMarkerScope,
    request_close_offset: usize,
) -> usize {
    scope
        .frames_remaining
        .checked_sub(request_close_offset)
        .expect("marker scope request-close offset should not exceed remaining frames")
}

fn split_back_frames(frames: &mut VecDeque<SharedFrame>, count: usize) -> VecDeque<SharedFrame> {
    if count == 0 {
        return VecDeque::new();
    }
    let split_at = frames
        .len()
        .checked_sub(count)
        .expect("marker scope should not cover more frames than remain");
    frames.split_off(split_at)
}

fn prepend_frames(continuation: &mut Continuation, mut frames: VecDeque<SharedFrame>) {
    frames.append(&mut continuation.frames);
    continuation.frames = frames;
}

fn shared_frame(stats: &mut RuntimeStats, frame: Frame) -> SharedFrame {
    stats.frame_allocs += 1;
    Rc::new(frame)
}

pub(super) fn prepend_marker_scope(
    continuation: &mut Continuation,
    scope: ContinuationMarkerScope,
) {
    let existing = continuation.marker_scopes.as_ref();
    let mut scopes = Vec::with_capacity(existing.map_or(0, |scopes| scopes.len()) + 1);
    scopes.push(scope);
    if let Some(existing) = existing {
        scopes.extend(existing.iter().cloned());
    }
    continuation.marker_scopes = Some(Rc::from(scopes.into_boxed_slice()));
}
