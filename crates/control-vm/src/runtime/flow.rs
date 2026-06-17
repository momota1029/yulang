use super::*;

impl<'a> Runtime<'a> {
    pub(super) fn apply_value(&mut self, callee: Value, arg: Value) -> RuntimeResult<'a> {
        self.stats.apply_value_calls += 1;
        match callee {
            Value::Marked { value, markers } => {
                let markers = if matches!(value.as_ref(), Value::Continuation(_)) {
                    markers_for_continuation_call(markers)
                } else {
                    markers_for_function_call(markers)
                };
                self.with_marker_frame(markers, move |runtime| runtime.apply_value(*value, arg))
            }
            Value::PrimitiveOp(primitive) => self.apply_primitive_op(primitive, arg),
            Value::ConstructorFunction(constructor) => {
                value_result(apply_constructor(constructor, arg))
            }
            Value::Closure(closure) => self.apply_closure(closure, arg),
            Value::RecursiveClosure { def, closure } => {
                self.apply_recursive_closure(def, closure, arg)
            }
            Value::FunctionAdapter(adapter) => self.apply_adapter(adapter, arg),
            Value::Thunk(_) => {
                let result = self.force_thunk(callee)?;
                self.continue_with(result, move |runtime, callee| {
                    runtime.apply_value(callee, arg.clone())
                })
            }
            Value::EffectOp { path } => value_result(Value::Thunk(Thunk::Effect {
                path,
                payload: Box::new(arg),
            })),
            Value::Continuation(id) => value_result(Value::Thunk(Thunk::Continuation {
                id,
                arg: Box::new(arg),
            })),
            value => Err(RuntimeError::NotFunction { value }),
        }
    }

    pub(super) fn eval_primitive_op(
        &mut self,
        op: PrimitiveOp,
        context: PrimitiveContext,
    ) -> RuntimeResult<'a> {
        if op.arity() == 0 {
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
    ) -> RuntimeResult<'a> {
        primitive.args.push(arg);
        if primitive.args.len() < primitive.op.arity() {
            return value_result(Value::PrimitiveOp(primitive));
        }
        value_result(apply_primitive(
            primitive.op,
            &primitive.context,
            &primitive.args,
        )?)
    }

    pub(super) fn apply_closure(&mut self, closure: Closure, arg: Value) -> RuntimeResult<'a> {
        let body = closure.body;
        let bind = self.bind_pat(closure.param, arg, closure.env)?;
        self.continue_bind(bind, move |runtime, matched, mut env| {
            if !matched {
                return Err(RuntimeError::PatternMismatch);
            }
            runtime.eval_expr(body, &mut env)
        })
    }

    pub(super) fn apply_recursive_closure(
        &mut self,
        def: DefId,
        mut closure: Closure,
        arg: Value,
    ) -> RuntimeResult<'a> {
        closure.env.insert(
            def,
            Value::RecursiveClosure {
                def,
                closure: closure.clone(),
            },
        );
        self.apply_closure(closure, arg)
    }

    pub(super) fn apply_adapter(
        &mut self,
        adapter: FunctionAdapter,
        arg: Value,
    ) -> RuntimeResult<'a> {
        let (source_arg, source_ret) =
            function_parts(&adapter.source).ok_or(RuntimeError::ExpectedFunctionType)?;
        let (target_arg, target_ret) =
            function_parts(&adapter.target).ok_or(RuntimeError::ExpectedFunctionType)?;
        let source_arg = source_arg.clone();
        let source_ret = source_ret.clone();
        let target_arg = target_arg.clone();
        let target_ret = target_ret.clone();
        let function = *adapter.function;
        let markers = self.instantiate_hygiene(&adapter.hygiene);
        self.with_marker_frame(markers.clone(), move |runtime| {
            let arg = mark_value(arg.clone(), &markers);
            let arg = runtime.adapt_value(arg, &target_arg, &source_arg)?;
            runtime.continue_with(arg, move |runtime, arg| {
                let arg = mark_value(arg, &markers);
                let result = runtime.apply_value(function.clone(), arg)?;
                let source_ret = source_ret.clone();
                let target_ret = target_ret.clone();
                let markers = markers.clone();
                runtime.continue_with(result, move |runtime, result| {
                    let result = mark_value(result, &markers);
                    runtime.adapt_value(result, &source_ret, &target_ret)
                })
            })
        })
    }

    pub(super) fn emit_effect_request(
        &mut self,
        path: Vec<String>,
        payload: Value,
    ) -> RuntimeResult<'a> {
        self.stats.effect_requests += 1;
        let path_key = self.intern_path(&path);
        let mut request = Request {
            path,
            path_key,
            guard_ids: Vec::new(),
            carried_guard_ids: Vec::new(),
            payload,
            resume: Rc::new(|_, value| value_result(value)),
        };
        self.mark_request_with_active_markers(&mut request);
        Ok(EvalResult::Request(request))
    }

    pub(super) fn mark_request_with_active_markers(&mut self, request: &mut Request<'a>) {
        for marker in &self.active_add_ids {
            self.stats.active_add_id_scans += 1;
            let path_matches_marker =
                counted_path_has_prefix(&mut self.stats, &request.path_key, &marker.path_key);
            if marker.depth != 0
                || (path_matches_marker && !marker.guard_own_path)
                || (!path_matches_marker && !marker.guard_foreign_path)
                || request
                    .guard_ids
                    .iter()
                    .any(|id| self.guard_ids.contains(id))
            {
                continue;
            }
            if !request.guard_ids.contains(&marker.id) {
                request.guard_ids.push(marker.id);
            }
            if marker.carry_after_frame
                && request_path_carries_function_adapter_guard(&request.path)
                && !request.carried_guard_ids.contains(&marker.id)
            {
                request.carried_guard_ids.push(marker.id);
            }
        }
    }

    pub(super) fn mark_active_value(&mut self, value: Value) -> Value {
        // Handler marker propagation follows the innermost active handler. Carrying outer
        // markers into a nested handler would make the outer handler skip the same request.
        let Some(markers) = self.active_marker_plans.last() else {
            return value;
        };
        mark_value(value, markers)
    }

    pub(super) fn mark_active_created_value(&mut self, value: Value) -> Value {
        let Some(markers) = self.active_marker_plans.last() else {
            return value;
        };
        let markers = markers_for_created_value(markers, &value);
        mark_value(value, &markers)
    }

    pub(super) fn request_guard_for_path(
        &mut self,
        request: &Request<'_>,
        operation_key: &InternedPath,
    ) -> Option<GuardId> {
        let matching_handler = self.find_matching_handler_frame(operation_key);
        let Some(matching_handler) = matching_handler else {
            if self
                .active_frames
                .iter()
                .any(|frame| frame.handler_path.is_some())
            {
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
        for (index, frame) in self.active_frames.iter().enumerate().rev() {
            self.stats.active_frame_scans += 1;
            let Some(path_key) = frame.handler_key.as_ref() else {
                continue;
            };
            if counted_path_has_prefix(&mut self.stats, operation_key, path_key) {
                return Some(index);
            }
        }
        None
    }

    fn find_guarded_matching_handler(
        &mut self,
        operation_key: &InternedPath,
        request: &Request<'_>,
        matching_handler: usize,
    ) -> Option<GuardId> {
        for frame in &self.active_frames[..=matching_handler] {
            self.stats.active_frame_scans += 1;
            let Some(path_key) = frame.handler_key.as_ref() else {
                continue;
            };
            if counted_path_has_prefix(&mut self.stats, operation_key, path_key)
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
        run: impl FnOnce(&mut Runtime<'a>) -> RuntimeResult<'a> + 'a,
    ) -> RuntimeResult<'a> {
        let handler_key = self.intern_path(&handler_path);
        self.with_marker_plan(markers, false, Some((handler_path, handler_key)), run)
    }

    pub(super) fn with_marker_frame(
        &mut self,
        markers: Vec<ValueMarker>,
        run: impl FnOnce(&mut Runtime<'a>) -> RuntimeResult<'a> + 'a,
    ) -> RuntimeResult<'a> {
        self.with_marker_plan(markers, true, None, run)
    }

    pub(super) fn with_marker_plan(
        &mut self,
        markers: Vec<ValueMarker>,
        activate_add_ids: bool,
        handler_path: Option<(Vec<String>, InternedPath)>,
        run: impl FnOnce(&mut Runtime<'a>) -> RuntimeResult<'a> + 'a,
    ) -> RuntimeResult<'a> {
        if markers.is_empty() {
            return run(self);
        }

        let guard_len = self.guard_ids.len();
        let frame_len = self.active_frames.len();
        let add_id_len = self.active_add_ids.len();
        let plan_len = self.active_marker_plans.len();
        self.push_marker_frame(&markers, activate_add_ids, handler_path.clone());
        let result = run(self);
        self.pop_marker_frame(guard_len, frame_len, add_id_len, plan_len);

        self.close_marker_frame_result(result?, markers, activate_add_ids, handler_path)
    }

    pub(super) fn push_marker_frame(
        &mut self,
        markers: &[ValueMarker],
        activate_add_ids: bool,
        handler_path: Option<(Vec<String>, InternedPath)>,
    ) {
        self.guard_ids
            .extend(markers.iter().filter_map(ValueMarker::frame_id));
        self.active_frames
            .extend(
                markers
                    .iter()
                    .filter_map(ValueMarker::frame_id)
                    .map(|id| ActiveFrame {
                        id,
                        handler_path: handler_path.as_ref().map(|(path, _)| path.clone()),
                        handler_key: handler_path.as_ref().map(|(_, key)| key.clone()),
                    }),
            );
        if activate_add_ids {
            self.active_add_ids
                .extend(markers.iter().filter_map(ValueMarker::add_id).cloned());
        }
        self.active_marker_plans.push(markers_for_value(markers));
    }

    pub(super) fn pop_marker_frame(
        &mut self,
        guard_len: usize,
        frame_len: usize,
        add_id_len: usize,
        plan_len: usize,
    ) {
        self.guard_ids.truncate(guard_len);
        self.active_frames.truncate(frame_len);
        self.active_add_ids.truncate(add_id_len);
        self.active_marker_plans.truncate(plan_len);
    }

    pub(super) fn close_marker_frame_result(
        &mut self,
        result: EvalResult<'a>,
        markers: Vec<ValueMarker>,
        activate_add_ids: bool,
        handler_path: Option<(Vec<String>, InternedPath)>,
    ) -> RuntimeResult<'a> {
        match result {
            EvalResult::Value(value) => {
                value_result(mark_value(value, &markers_for_value(&markers)))
            }
            EvalResult::Request(request) => {
                let resume = request.resume.clone();
                let resume_markers = markers_for_continuation_resume(&markers);
                Ok(EvalResult::Request(Request {
                    path: request.path,
                    path_key: request.path_key,
                    guard_ids: request.guard_ids,
                    carried_guard_ids: request.carried_guard_ids,
                    payload: request.payload,
                    resume: Rc::new(move |runtime, value| {
                        let resume = resume.clone();
                        runtime.with_marker_plan(
                            resume_markers.clone(),
                            activate_add_ids,
                            handler_path.clone(),
                            move |runtime| resume(runtime, value),
                        )
                    }),
                }))
            }
        }
    }
}
