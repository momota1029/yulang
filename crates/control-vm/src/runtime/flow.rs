use super::*;

impl<'a> Runtime<'a> {
    pub(super) fn apply_scoped_value(&mut self, callee: Value, arg: Value) -> RuntimeResult {
        // Active hygiene markers are carried by the runtime stack while an
        // expression is evaluated. Attach them only at source-level calls; pop
        // and request boundaries still close over escaping values.
        let Some(markers) = self.active_marker_plans.last() else {
            return self.apply_value(callee, arg);
        };
        let markers = shared_markers_for_function_call(markers);
        if markers.is_empty() {
            return self.apply_value(callee, arg);
        }
        match callee {
            Value::Marked { .. } => self.apply_value(mark_value(callee, &markers), arg),
            callee if callee_apply_closes_without_frame(&callee) => {
                let result = self.apply_value(callee, arg)?;
                self.close_shared_scoped_result(result, markers)
            }
            callee => self
                .with_shared_marker_frame(markers, move |runtime| runtime.apply_value(callee, arg)),
        }
    }

    pub(super) fn apply_value(&mut self, callee: Value, arg: Value) -> RuntimeResult {
        self.stats.apply_value_calls += 1;
        match callee {
            Value::Marked { value, markers } => {
                self.stats.apply_marked_calls += 1;
                let markers = if matches!(value.as_ref(), Value::Continuation(_)) {
                    markers_for_continuation_call(&markers)
                } else {
                    markers_for_function_call(&markers)
                };
                let value = *value;
                if callee_apply_closes_without_frame(&value) {
                    let result = self.apply_value(value, arg)?;
                    return self.close_scoped_result(result, markers);
                }
                self.with_marker_frame(markers, move |runtime| runtime.apply_value(value, arg))
            }
            Value::PrimitiveOp(primitive) => {
                self.stats.apply_primitive_calls += 1;
                self.apply_primitive_op(primitive, arg)
            }
            Value::ConstructorFunction(constructor) => {
                self.stats.apply_constructor_calls += 1;
                value_result(apply_constructor(constructor, arg))
            }
            Value::Closure(closure) => {
                self.stats.apply_closure_calls += 1;
                self.apply_closure(closure, arg)
            }
            Value::RecursiveClosure { def, closure } => {
                self.stats.apply_recursive_closure_calls += 1;
                self.apply_recursive_closure(def, closure, arg)
            }
            Value::FunctionAdapter(adapter) => {
                self.stats.apply_adapter_calls += 1;
                self.apply_adapter(adapter, arg)
            }
            Value::Thunk(_) => {
                self.stats.apply_forced_thunk_calls += 1;
                let result = self.force_thunk(callee)?;
                self.continue_with_frame(result, Frame::ApplyForcedThunk { arg })
            }
            Value::EffectOp { path } => {
                self.stats.apply_effect_op_calls += 1;
                value_result(Value::Thunk(Rc::new(Thunk::Effect {
                    path,
                    payload: Box::new(arg),
                })))
            }
            Value::Continuation(id) => {
                self.stats.apply_continuation_calls += 1;
                value_result(Value::Thunk(Rc::new(Thunk::Continuation {
                    id,
                    arg: Box::new(arg),
                })))
            }
            value => Err(RuntimeError::NotFunction { value }),
        }
    }

    pub(super) fn close_scoped_result(
        &mut self,
        result: EvalResult,
        markers: Vec<ValueMarker>,
    ) -> RuntimeResult {
        match result {
            EvalResult::Value(value) => value_result(mark_value(value, &markers)),
            EvalResult::Request(request) => {
                let resume_markers = shared_markers(markers_for_continuation_resume(&markers));
                self.close_marker_request(request, resume_markers, true, None)
            }
        }
    }

    pub(super) fn close_shared_scoped_result(
        &mut self,
        result: EvalResult,
        markers: SharedMarkers,
    ) -> RuntimeResult {
        match result {
            EvalResult::Value(value) => value_result(mark_value(value, &markers)),
            EvalResult::Request(request) => {
                let resume_markers = shared_markers(markers_for_continuation_resume(&markers));
                self.close_marker_request(request, resume_markers, true, None)
            }
        }
    }

    pub(super) fn eval_primitive_op(
        &mut self,
        op: PrimitiveOp,
        context: PrimitiveContext,
    ) -> RuntimeResult {
        if op.arity() == 0 {
            self.stats.primitive_zero_arity_calls += 1;
            return value_result(apply_primitive(op, &context, &[])?);
        }
        value_result(Value::PrimitiveOp(PrimitiveValue {
            op,
            context,
            args: Vec::new(),
        }))
    }

    pub(super) fn apply_primitive_op(
        &mut self,
        mut primitive: PrimitiveValue,
        arg: Value,
    ) -> RuntimeResult {
        self.stats.primitive_apply_calls += 1;
        primitive.args.push(arg);
        if primitive.args.len() < primitive.op.arity() {
            self.stats.primitive_apply_partial += 1;
            return value_result(Value::PrimitiveOp(primitive));
        }
        self.stats.primitive_apply_complete += 1;
        value_result(apply_primitive(
            primitive.op,
            &primitive.context,
            &primitive.args,
        )?)
    }

    pub(super) fn apply_closure(&mut self, closure: Rc<Closure>, arg: Value) -> RuntimeResult {
        let body = closure.body;
        self.bind_pat(
            closure.param.clone(),
            arg,
            closure.env.clone(),
            BindThen::ApplyClosure { body },
        )
    }

    pub(super) fn apply_recursive_closure(
        &mut self,
        def: DefId,
        closure: Rc<Closure>,
        arg: Value,
    ) -> RuntimeResult {
        let mut env = closure.env.clone();
        let stats = env.insert(
            def,
            Value::RecursiveClosure {
                def,
                closure: closure.clone(),
            },
        );
        self.record_env_insert(stats);
        self.bind_pat(
            closure.param.clone(),
            arg,
            env,
            BindThen::ApplyClosure { body: closure.body },
        )
    }

    pub(super) fn apply_adapter(
        &mut self,
        adapter: Rc<FunctionAdapter>,
        arg: Value,
    ) -> RuntimeResult {
        let (source_arg, source_ret) =
            function_parts(&adapter.source).ok_or(RuntimeError::ExpectedFunctionType)?;
        let (target_arg, target_ret) =
            function_parts(&adapter.target).ok_or(RuntimeError::ExpectedFunctionType)?;
        let source_arg = source_arg.clone();
        let source_ret = source_ret.clone();
        let target_arg = target_arg.clone();
        let target_ret = target_ret.clone();
        let function = adapter.function.as_ref().clone();
        let markers = self.instantiate_hygiene(&adapter.hygiene);
        self.with_marker_frame(markers.clone(), move |runtime| {
            let resume_markers = shared_markers(markers.clone());
            let arg = mark_value(arg.clone(), &resume_markers);
            let arg = runtime.adapt_value(arg, &target_arg, &source_arg)?;
            runtime.continue_with_frame(
                arg,
                Frame::ApplyAdapterArg {
                    function: function.clone(),
                    markers: resume_markers,
                    source_ret: source_ret.clone(),
                    target_ret: target_ret.clone(),
                },
            )
        })
    }

    pub(super) fn emit_effect_request(
        &mut self,
        path: Vec<String>,
        payload: Value,
    ) -> RuntimeResult {
        self.stats.effect_requests += 1;
        let path_key = self.intern_path(&path);
        let mut request = Request {
            path,
            path_key,
            guard_ids: Vec::new(),
            carried_guard_ids: Vec::new(),
            payload,
            continuation: Continuation::default(),
        };
        self.mark_request_with_active_markers(&mut request);
        Ok(EvalResult::Request(request))
    }

    pub(super) fn mark_request_with_active_markers(&mut self, request: &mut Request) {
        let mut has_live_guard = request
            .guard_ids
            .iter()
            .any(|id| self.guard_ids.contains(id));
        if has_live_guard {
            return;
        }
        for marker in &self.active_add_ids {
            self.stats.active_add_id_scans += 1;
            let path_matches_marker =
                counted_path_has_prefix(&mut self.stats, &request.path_key, &marker.path_key);
            if (path_matches_marker && !marker.guard_own_path)
                || (!path_matches_marker && !marker.guard_foreign_path)
            {
                continue;
            }
            if !request.guard_ids.contains(&marker.id) {
                request.guard_ids.push(marker.id);
                has_live_guard = self.guard_ids.contains(&marker.id);
            }
            if marker.carry_after_frame
                && request_path_carries_function_adapter_guard(&request.path)
                && !request.carried_guard_ids.contains(&marker.id)
            {
                request.carried_guard_ids.push(marker.id);
            }
            if has_live_guard {
                break;
            }
        }
    }

    pub(super) fn request_guard_for_path(
        &mut self,
        request: &Request,
        operation_key: &InternedPath,
    ) -> Option<GuardId> {
        let matching_handler = self.find_matching_handler_frame(operation_key);
        let Some(matching_handler) = matching_handler else {
            if !self.active_handler_frames.is_empty() {
                return None;
            }
            return self
                .active_frames
                .iter()
                .find(|frame| request.guard_ids.contains(&frame.id))
                .map(|frame| frame.id)
                .or_else(|| {
                    // Function adapter guards can leave their marker frame before the
                    // surrounding catch observes the request. In that case, the carried
                    // guard still skips the next matching handler once.
                    if self.active_frames.is_empty() {
                        request.carried_guard_ids.first().copied()
                    } else {
                        None
                    }
                });
        };
        self.active_frames[matching_handler + 1..]
            .iter()
            .find(|frame| request.guard_ids.contains(&frame.id))
            .map(|frame| frame.id)
            .or_else(|| {
                self.find_guarded_matching_handler(operation_key, request, matching_handler)
            })
            .or_else(|| {
                if self.active_frames.is_empty() {
                    request.carried_guard_ids.first().copied()
                } else {
                    None
                }
            })
    }

    fn find_matching_handler_frame(&mut self, operation_key: &InternedPath) -> Option<usize> {
        for frame in self.active_handler_frames.iter().rev() {
            self.stats.active_frame_scans += 1;
            if counted_path_has_prefix(&mut self.stats, operation_key, &frame.handler_key) {
                return Some(frame.frame_index);
            }
        }
        None
    }

    fn find_guarded_matching_handler(
        &mut self,
        operation_key: &InternedPath,
        request: &Request,
        matching_handler: usize,
    ) -> Option<GuardId> {
        for frame in self
            .active_handler_frames
            .iter()
            .take_while(|frame| frame.frame_index <= matching_handler)
        {
            self.stats.active_frame_scans += 1;
            if counted_path_has_prefix(&mut self.stats, operation_key, &frame.handler_key)
                && request.guard_ids.contains(&frame.id)
            {
                return Some(frame.id);
            }
        }
        None
    }

    pub(super) fn instantiate_hygiene(
        &mut self,
        hygiene: &FunctionAdapterHygiene,
    ) -> Vec<ValueMarker> {
        let mut markers = Vec::with_capacity(hygiene.markers.len() * 2);
        for marker in &hygiene.markers {
            let id = self.fresh_guard_id();
            let path_key = self.intern_path(&marker.path);
            markers.push(ValueMarker::Frame { id });
            markers.push(ValueMarker::AddId(AddIdMarker {
                id,
                path: marker.path.clone(),
                path_key,
                depth: marker.depth,
                guard_own_path: false,
                guard_foreign_path: true,
                carry_after_frame: true,
            }));
        }
        markers
    }

    pub(super) fn fresh_guard_id(&mut self) -> GuardId {
        let id = GuardId(self.next_guard_id);
        self.next_guard_id += 1;
        id
    }

    pub(super) fn with_stack_handler_frame(
        &mut self,
        markers: Vec<ValueMarker>,
        handler_path: Vec<String>,
        run: impl FnOnce(&mut Runtime<'a>) -> RuntimeResult + 'a,
    ) -> RuntimeResult {
        let handler_key = self.intern_path(&handler_path);
        self.with_marker_plan(markers, false, Some(handler_key), run)
    }

    pub(super) fn with_marker_frame(
        &mut self,
        markers: Vec<ValueMarker>,
        run: impl FnOnce(&mut Runtime<'a>) -> RuntimeResult + 'a,
    ) -> RuntimeResult {
        self.with_marker_plan(markers, true, None, run)
    }

    pub(super) fn with_shared_marker_frame(
        &mut self,
        markers: SharedMarkers,
        run: impl FnOnce(&mut Runtime<'a>) -> RuntimeResult + 'a,
    ) -> RuntimeResult {
        self.with_shared_marker_plan(markers, true, None, run)
    }

    pub(super) fn with_marker_plan(
        &mut self,
        markers: Vec<ValueMarker>,
        activate_add_ids: bool,
        handler_key: Option<InternedPath>,
        run: impl FnOnce(&mut Runtime<'a>) -> RuntimeResult + 'a,
    ) -> RuntimeResult {
        self.stats.marker_frame_calls += 1;
        if markers.is_empty() {
            self.stats.marker_frame_empty += 1;
            return run(self);
        }

        let guard_len = self.guard_ids.len();
        let frame_len = self.active_frames.len();
        let handler_frame_len = self.active_handler_frames.len();
        let add_id_len = self.active_add_ids.len();
        let plan_len = self.active_marker_plans.len();
        self.stats.marker_frame_pushes += 1;
        self.push_marker_frame(&markers, activate_add_ids, handler_key.clone());
        let result = run(self);
        self.pop_marker_frame(
            guard_len,
            frame_len,
            handler_frame_len,
            add_id_len,
            plan_len,
        );

        self.close_marker_frame_result(result?, markers, activate_add_ids, handler_key)
    }

    fn with_shared_marker_plan(
        &mut self,
        markers: SharedMarkers,
        activate_add_ids: bool,
        handler_key: Option<InternedPath>,
        run: impl FnOnce(&mut Runtime<'a>) -> RuntimeResult + 'a,
    ) -> RuntimeResult {
        self.stats.marker_frame_calls += 1;
        if markers.is_empty() {
            self.stats.marker_frame_empty += 1;
            return run(self);
        }

        let guard_len = self.guard_ids.len();
        let frame_len = self.active_frames.len();
        let handler_frame_len = self.active_handler_frames.len();
        let add_id_len = self.active_add_ids.len();
        let plan_len = self.active_marker_plans.len();
        self.stats.marker_frame_pushes += 1;
        self.push_shared_marker_frame(markers.clone(), activate_add_ids, handler_key.clone());
        let result = run(self);
        self.pop_marker_frame(
            guard_len,
            frame_len,
            handler_frame_len,
            add_id_len,
            plan_len,
        );

        self.close_shared_marker_frame_result(result?, markers, activate_add_ids, handler_key)
    }

    pub(super) fn push_marker_frame(
        &mut self,
        markers: &[ValueMarker],
        activate_add_ids: bool,
        handler_key: Option<InternedPath>,
    ) {
        let active_plan = shared_markers(markers.to_vec());
        self.push_marker_frame_with_plan(markers, activate_add_ids, handler_key, active_plan);
    }

    pub(super) fn push_shared_marker_frame(
        &mut self,
        markers: SharedMarkers,
        activate_add_ids: bool,
        handler_key: Option<InternedPath>,
    ) {
        let active_plan = markers.clone();
        self.push_marker_frame_with_plan(&markers, activate_add_ids, handler_key, active_plan);
    }

    fn push_marker_frame_with_plan(
        &mut self,
        markers: &[ValueMarker],
        activate_add_ids: bool,
        handler_key: Option<InternedPath>,
        active_plan: SharedMarkers,
    ) {
        for marker in markers {
            match marker {
                ValueMarker::Frame { id } => {
                    if !self.guard_ids.contains(id) {
                        self.guard_ids.push(*id);
                    }
                    let frame_index = self.active_frames.len();
                    self.active_frames.push(ActiveFrame { id: *id });
                    if let Some(handler_key) = handler_key.clone() {
                        self.active_handler_frames.push(ActiveHandlerFrame {
                            frame_index,
                            id: *id,
                            handler_key,
                        });
                    }
                }
                ValueMarker::AddId(marker) if activate_add_ids && marker.depth == 0 => {
                    if !self.active_add_ids.contains(marker) {
                        self.active_add_ids.push(marker.clone());
                    }
                }
                ValueMarker::AddId(_) => {}
            }
        }
        self.active_marker_plans.push(active_plan);
    }

    pub(super) fn pop_marker_frame(
        &mut self,
        guard_len: usize,
        frame_len: usize,
        handler_frame_len: usize,
        add_id_len: usize,
        plan_len: usize,
    ) {
        self.guard_ids.truncate(guard_len);
        self.active_frames.truncate(frame_len);
        self.active_handler_frames.truncate(handler_frame_len);
        self.active_add_ids.truncate(add_id_len);
        self.active_marker_plans.truncate(plan_len);
    }

    pub(super) fn close_marker_frame_result(
        &mut self,
        result: EvalResult,
        markers: Vec<ValueMarker>,
        activate_add_ids: bool,
        handler_key: Option<InternedPath>,
    ) -> RuntimeResult {
        match result {
            EvalResult::Value(value) => {
                self.stats.marker_frame_value_closes += 1;
                value_result(mark_value(value, &markers))
            }
            EvalResult::Request(request) => {
                self.stats.marker_frame_request_closes += 1;
                let resume_markers = shared_markers(markers_for_continuation_resume(&markers));
                self.close_marker_request(request, resume_markers, activate_add_ids, handler_key)
            }
        }
    }

    pub(super) fn close_shared_marker_frame_result(
        &mut self,
        result: EvalResult,
        markers: SharedMarkers,
        activate_add_ids: bool,
        handler_key: Option<InternedPath>,
    ) -> RuntimeResult {
        match result {
            EvalResult::Value(value) => {
                self.stats.marker_frame_value_closes += 1;
                value_result(mark_value(value, &markers))
            }
            EvalResult::Request(request) => {
                self.stats.marker_frame_request_closes += 1;
                let resume_markers = shared_markers(markers_for_continuation_resume(&markers));
                self.close_marker_request(request, resume_markers, activate_add_ids, handler_key)
            }
        }
    }

    pub(super) fn close_shared_resume_marker_frame_result(
        &mut self,
        result: EvalResult,
        markers: SharedMarkers,
        activate_add_ids: bool,
        handler_key: Option<InternedPath>,
    ) -> RuntimeResult {
        match result {
            EvalResult::Value(value) => {
                self.stats.marker_frame_value_closes += 1;
                value_result(mark_value(value, &markers))
            }
            EvalResult::Request(request) => {
                self.stats.marker_frame_request_closes += 1;
                // Shared resume marker plans are created after
                // `markers_for_continuation_resume`; reusing them avoids
                // re-normalizing the same multi-shot continuation path.
                self.close_marker_request(request, markers, activate_add_ids, handler_key)
            }
        }
    }

    pub(super) fn close_marker_request(
        &mut self,
        request: Request,
        resume_markers: SharedMarkers,
        activate_add_ids: bool,
        handler_key: Option<InternedPath>,
    ) -> RuntimeResult {
        let mut request = request;
        let frames_remaining = request.continuation.frames.len();
        prepend_marker_scope(
            &mut request.continuation,
            ContinuationMarkerScope {
                frames_remaining,
                resume_markers: resume_markers.clone(),
                activate_add_ids,
                handler_key: handler_key.clone(),
            },
        );
        Ok(EvalResult::Request(request))
    }
}
