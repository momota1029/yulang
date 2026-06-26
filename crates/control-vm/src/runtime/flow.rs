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
            Value::Marked { .. } => self.apply_value(mark_value_shared(callee, &markers), arg),
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
                    shared_markers_for_continuation_call(&markers)
                } else {
                    shared_markers_for_function_call(&markers)
                };
                let value = *value;
                if callee_apply_closes_without_frame(&value) {
                    let result = self.apply_value(value, arg)?;
                    return self.close_shared_scoped_result(result, markers);
                }
                self.with_shared_marker_frame(markers, move |runtime| {
                    runtime.apply_value(value, arg)
                })
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
            Value::EffectOp { path, path_key } => {
                self.stats.apply_effect_op_calls += 1;
                value_result(Value::Thunk(Rc::new(Thunk::Effect {
                    path,
                    path_key,
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

    pub(super) fn close_shared_scoped_result(
        &mut self,
        result: EvalResult,
        markers: SharedMarkers,
    ) -> RuntimeResult {
        match result {
            EvalResult::Value(value) => value_result(mark_value_shared(value, &markers)),
            EvalResult::Request(request) => {
                let resume_markers = shared_markers_for_continuation_resume(&markers);
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
        let body_markers =
            shared_markers(self.instantiate_hygiene_markers(&adapter.hygiene.markers));
        let arg_markers =
            shared_markers(self.instantiate_hygiene_markers(&adapter.hygiene.arg_markers));
        let ret_markers =
            shared_markers(self.instantiate_hygiene_markers(&adapter.hygiene.ret_markers));
        let arg_boundary_markers = shared_combined_markers(&body_markers, &arg_markers);
        let ret_boundary_markers = shared_combined_markers(&body_markers, &ret_markers);
        self.with_shared_marker_frame(body_markers, move |runtime| {
            let arg = mark_value_shared(arg.clone(), &arg_boundary_markers);
            let arg = runtime.adapt_value(arg, &target_arg, &source_arg)?;
            runtime.continue_with_frame(
                arg,
                Frame::ApplyAdapterArg {
                    function: function.clone(),
                    arg_markers: arg_boundary_markers.clone(),
                    ret_markers: ret_boundary_markers.clone(),
                    source_ret: source_ret.clone(),
                    target_ret: target_ret.clone(),
                },
            )
        })
    }

    pub(super) fn emit_effect_request(
        &mut self,
        path: Vec<String>,
        path_key: InternedPath,
        payload: Value,
    ) -> RuntimeResult {
        self.stats.effect_requests += 1;
        let mut request = Request {
            path,
            path_key,
            guard_ids: GuardIds::new(),
            carried_guards: Vec::new(),
            handler_boundary: None,
            payload,
            continuation: Continuation::default(),
        };
        self.mark_request_with_active_markers(&mut request);
        Ok(EvalResult::Request(request))
    }

    pub(super) fn mark_request_with_active_markers(&mut self, request: &mut Request) {
        let scope_expected = if let Some(scope) = self.scope_state_shadow.as_ref() {
            let candidate_stats = scope.path_candidate_stats(&request.path_key);
            self.stats.scope_state_shadow_checks += 1;
            self.stats.scope_state_shadow_active_add_markers +=
                candidate_stats.active_add_markers as u64;
            self.stats.scope_state_shadow_path_candidates += candidate_stats.path_candidates as u64;
            self.stats.scope_state_shadow_all_path_candidates +=
                candidate_stats.all_path_candidates as u64;
            self.stats.scope_state_shadow_own_path_candidates +=
                candidate_stats.own_path_candidates as u64;
            self.stats.scope_state_shadow_foreign_path_candidates +=
                candidate_stats.foreign_path_candidates as u64;
            Some(scope.mark_request(request))
        } else {
            None
        };
        for active_marker in &self.active_add_ids {
            let marker = &active_marker.marker;
            self.stats.active_add_id_scans += 1;
            let path_matches_marker =
                counted_path_has_prefix(&mut self.stats, &request.path_key, marker.path_key);
            if (path_matches_marker && !marker.guard_own_path)
                || (!path_matches_marker && !marker.guard_foreign_path)
                || (!marker.carry_after_frame
                    && request_excepted_at_marker_entry(
                        &mut self.stats,
                        &self.active_frames,
                        request,
                        active_marker,
                    ))
            {
                continue;
            }
            if marker.carry_after_frame
                && !request
                    .carried_guards
                    .iter()
                    .any(|guard| guard.id == marker.id)
            {
                let entry_guard_ids = request_guard_ids_at_marker_entry(
                    &mut self.stats,
                    &self.active_frames,
                    request,
                    active_marker,
                );
                let exposed_guard_ids = self.carried_exposed_guard_ids_at_marker_entry(
                    request,
                    active_marker,
                    entry_guard_ids,
                );
                request.guard_ids.push_unique(marker.id);
                request.carried_guards.push(CarriedGuard {
                    id: marker.id,
                    entry_frame_len: active_marker.entry_frame_len,
                    exposed_guard_ids,
                });
            } else if !marker.carry_after_frame {
                request.guard_ids.push_unique(marker.id);
            }
        }
        if let Some(scope_expected) = scope_expected {
            self.assert_scope_state_request_marking(request, scope_expected);
        }
    }

    fn assert_scope_state_request_marking(&self, request: &Request, expected: ScopeRequestMarking) {
        let actual = ScopeRequestMarking::from_request(request);
        assert_eq!(
            actual, expected,
            "ScopeState shadow produced a different request marking"
        );
    }

    fn carried_exposed_guard_ids_at_marker_entry(
        &self,
        request: &Request,
        marker: &ActiveAddIdMarker,
        mut ids: GuardIds,
    ) -> GuardIds {
        if marker.marker.preserve_own_on_resume {
            // Explicit argument-effect contracts permit handlers that were
            // already visible at the callback call site to handle the matching
            // effect family. Ordinary own-path guards do not get this exposure.
            self.push_contract_matching_handler_ids_at_marker_entry(
                request,
                marker.entry_frame_len,
                &mut ids,
            );
        }
        if self.exposes_matching_handler_alias(request, marker.entry_frame_len, &ids)
            && let Some(handler_id) = self.outermost_matching_handler_id(&request.path_key)
            && !ids.contains(handler_id)
        {
            ids.push_unique(handler_id);
        }
        ids
    }

    fn push_contract_matching_handler_ids_at_marker_entry(
        &self,
        request: &Request,
        entry_frame_len: usize,
        ids: &mut GuardIds,
    ) {
        for frame in &self.active_handler_frames {
            if frame.frame_index < entry_frame_len && request.path_key.has_prefix(frame.handler_key)
            {
                ids.push_unique(frame.id);
            }
        }
    }

    fn exposes_matching_handler_alias(
        &self,
        request: &Request,
        entry_frame_len: usize,
        ids: &GuardIds,
    ) -> bool {
        ids.iter().any(|id| {
            self.active_handler_frames.iter().any(|frame| {
                frame.frame_index < entry_frame_len
                    && frame.id == *id
                    && request.path_key.has_prefix(frame.handler_key)
            })
        })
    }

    fn outermost_matching_handler_id(&self, request_key: &InternedPath) -> Option<GuardId> {
        self.active_handler_frames
            .iter()
            .find(|frame| request_key.has_prefix(frame.handler_key))
            .map(|frame| frame.id)
    }

    pub(super) fn request_guard_for_path(
        &mut self,
        request: &Request,
        operation_key: &InternedPath,
    ) -> Option<GuardSkip> {
        let matching_handler = self.find_matching_handler_frame(operation_key);
        let Some(matching_handler) = matching_handler else {
            if !self.active_handler_frames.is_empty() {
                return None;
            }
            return self
                .active_frames
                .iter()
                .find(|frame| request.guard_ids.contains(frame.id))
                .map(|frame| GuardSkip::Preserve(frame.id))
                // Function adapter guards can leave their marker frame before the
                // surrounding catch observes the request, so the request carries
                // that active color until the relevant handler boundary sees it.
                .or_else(|| {
                    request
                        .carried_guards
                        .first()
                        .map(|guard| GuardSkip::Preserve(guard.id))
                });
        };
        self.carried_guard_for_matching_handler(request, matching_handler)
            .or_else(|| {
                let handler_id = self.active_frames.get(matching_handler)?.id;
                self.active_frames[matching_handler + 1..]
                    .iter()
                    .find(|frame| self.guard_blocks_handler(request, frame.id, handler_id))
                    .map(|frame| GuardSkip::Preserve(frame.id))
            })
            .or_else(|| self.current_handler_guard(request, matching_handler))
            .or_else(|| {
                if self.active_frames.is_empty() {
                    request
                        .carried_guards
                        .first()
                        .map(|guard| GuardSkip::Preserve(guard.id))
                } else {
                    None
                }
            })
    }

    fn carried_guard_for_matching_handler(
        &self,
        request: &Request,
        matching_handler: usize,
    ) -> Option<GuardSkip> {
        let handler_id = self
            .active_frames
            .get(matching_handler)
            .map(|frame| frame.id)?;
        request
            .carried_guards
            .iter()
            .find(|guard| {
                matching_handler < guard.entry_frame_len
                    && !guard.exposed_guard_ids.contains(handler_id)
            })
            .map(|guard| GuardSkip::Preserve(guard.id))
    }

    fn guard_blocks_handler(
        &self,
        request: &Request,
        guard_id: GuardId,
        handler_id: GuardId,
    ) -> bool {
        request.guard_ids.contains(guard_id)
            && !request.carried_guards.iter().any(|guard| {
                guard.exposed_guard_ids.contains(handler_id)
                    && (guard.id == guard_id || guard.exposed_guard_ids.contains(guard_id))
            })
    }

    fn current_handler_guard(
        &mut self,
        request: &Request,
        matching_handler: usize,
    ) -> Option<GuardSkip> {
        for frame in &self.active_handler_frames {
            self.stats.active_frame_scans += 1;
            if frame.frame_index == matching_handler
                && self.guard_blocks_handler(request, frame.id, frame.id)
            {
                return Some(GuardSkip::Preserve(frame.id));
            }
        }
        None
    }

    fn find_matching_handler_frame(&mut self, operation_key: &InternedPath) -> Option<usize> {
        for frame in self.active_handler_frames.iter().rev() {
            self.stats.active_frame_scans += 1;
            if counted_path_has_prefix(&mut self.stats, operation_key, frame.handler_key) {
                return Some(frame.frame_index);
            }
        }
        None
    }

    pub(super) fn instantiate_hygiene_markers(
        &mut self,
        markers: &[mono::GuardMarker],
    ) -> Vec<ValueMarker> {
        let mut value_markers = Vec::with_capacity(markers.len() * 2);
        for marker in markers {
            let id = self.fresh_guard_id();
            let path_key = self.intern_path(&marker.path);
            value_markers.push(ValueMarker::Frame { id });
            value_markers.push(ValueMarker::AddId(AddIdMarker {
                id,
                path_key: path_key.prefix(),
                depth: marker.depth,
                guard_own_path: marker.guard_own_path,
                guard_foreign_path: marker.guard_foreign_path,
                carry_after_frame: marker.guard_own_path,
                preserve_own_on_resume: marker.preserve_own_on_resume,
            }));
        }
        value_markers
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
        let handler_key = self.intern_path(&handler_path).prefix();
        self.with_marker_plan(markers, false, Some(handler_key), run)
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
        handler_key: Option<InternedPathPrefix>,
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
        let handler_boundary = match &result {
            Ok(EvalResult::Request(request)) => {
                self.handler_boundary_for_request(request, handler_key, frame_len)
            }
            Ok(EvalResult::Value(_)) | Err(_) => None,
        };
        self.pop_marker_frame(
            guard_len,
            frame_len,
            handler_frame_len,
            add_id_len,
            plan_len,
        );

        self.close_marker_frame_result(
            result?,
            markers,
            activate_add_ids,
            handler_key,
            handler_boundary,
        )
    }

    fn with_shared_marker_plan(
        &mut self,
        markers: SharedMarkers,
        activate_add_ids: bool,
        handler_key: Option<InternedPathPrefix>,
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
        let handler_boundary = match &result {
            Ok(EvalResult::Request(request)) => {
                self.handler_boundary_for_request(request, handler_key, frame_len)
            }
            Ok(EvalResult::Value(_)) | Err(_) => None,
        };
        self.pop_marker_frame(
            guard_len,
            frame_len,
            handler_frame_len,
            add_id_len,
            plan_len,
        );

        self.close_shared_marker_frame_result(
            result?,
            markers,
            activate_add_ids,
            handler_key,
            handler_boundary,
        )
    }

    pub(super) fn push_marker_frame(
        &mut self,
        markers: &[ValueMarker],
        activate_add_ids: bool,
        handler_key: Option<InternedPathPrefix>,
    ) {
        let active_plan = shared_markers(markers.to_vec());
        self.push_marker_frame_with_plan(markers, activate_add_ids, handler_key, active_plan);
    }

    pub(super) fn push_shared_marker_frame(
        &mut self,
        markers: SharedMarkers,
        activate_add_ids: bool,
        handler_key: Option<InternedPathPrefix>,
    ) {
        let active_plan = markers.clone();
        self.push_marker_frame_with_plan(&markers, activate_add_ids, handler_key, active_plan);
    }

    fn push_marker_frame_with_plan(
        &mut self,
        markers: &[ValueMarker],
        activate_add_ids: bool,
        handler_key: Option<InternedPathPrefix>,
        active_plan: SharedMarkers,
    ) {
        let mut frame_entries = Vec::new();
        for marker in markers {
            match marker {
                ValueMarker::Frame { id } => {
                    let entry_frame_len = self.active_frames.len();
                    if !self.guard_ids.contains(id) {
                        self.guard_ids.push(*id);
                    }
                    let frame_index = entry_frame_len;
                    self.active_frames.push(ActiveFrame { id: *id });
                    if let Some(scope) = &mut self.scope_state_shadow {
                        scope.push_frame(*id);
                    }
                    frame_entries.push((*id, entry_frame_len));
                    if let Some(handler_key) = handler_key {
                        self.active_handler_frames.push(ActiveHandlerFrame {
                            frame_index,
                            id: *id,
                            handler_key,
                        });
                        if let Some(scope) = &mut self.scope_state_shadow {
                            scope.push_handler_frame(frame_index, *id, handler_key);
                        }
                    }
                }
                ValueMarker::AddId(marker) if activate_add_ids && marker.depth == 0 => {
                    let active_marker = ActiveAddIdMarker {
                        marker: marker.clone(),
                        entry_frame_len: self.entry_frame_len_for_marker(marker.id, &frame_entries),
                    };
                    self.stats.active_add_insert_checks += 1;
                    // Exact duplicate add-id markers are idempotent during
                    // request marking: GuardIds and carried guards are
                    // de-duplicated by guard id. Avoid a linear membership scan
                    // here; repeated markers only add repeated cheap marking
                    // candidates if they ever appear.
                    if let Some(scope) = &mut self.scope_state_shadow {
                        scope.push_add_marker(active_marker.clone());
                    }
                    self.active_add_ids.push(active_marker);
                }
                ValueMarker::AddId(_) => {}
            }
        }
        self.active_marker_plans.push(active_plan);
    }

    fn entry_frame_len_for_marker(&self, id: GuardId, frame_entries: &[(GuardId, usize)]) -> usize {
        frame_entries
            .iter()
            .rev()
            .find_map(|(frame_id, entry_frame_len)| (*frame_id == id).then_some(*entry_frame_len))
            .or_else(|| self.active_frames.iter().position(|frame| frame.id == id))
            .unwrap_or(self.active_frames.len())
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
        if let Some(scope) = &mut self.scope_state_shadow {
            scope.truncate(frame_len, handler_frame_len, add_id_len);
        }
    }

    pub(super) fn close_marker_frame_result(
        &mut self,
        result: EvalResult,
        markers: Vec<ValueMarker>,
        activate_add_ids: bool,
        handler_key: Option<InternedPathPrefix>,
        handler_boundary: Option<HandlerBoundary>,
    ) -> RuntimeResult {
        match result {
            EvalResult::Value(value) => {
                self.stats.marker_frame_value_closes += 1;
                value_result(mark_value(value, &markers))
            }
            EvalResult::Request(request) => {
                self.stats.marker_frame_request_closes += 1;
                let mut request = request;
                if let Some(handler_boundary) = handler_boundary {
                    request.handler_boundary = Some(handler_boundary);
                }
                request.payload = mark_value(request.payload, &markers);
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
        handler_key: Option<InternedPathPrefix>,
        handler_boundary: Option<HandlerBoundary>,
    ) -> RuntimeResult {
        match result {
            EvalResult::Value(value) => {
                self.stats.marker_frame_value_closes += 1;
                value_result(mark_value_shared(value, &markers))
            }
            EvalResult::Request(request) => {
                self.stats.marker_frame_request_closes += 1;
                let mut request = request;
                if let Some(handler_boundary) = handler_boundary {
                    request.handler_boundary = Some(handler_boundary);
                }
                request.payload = mark_value_shared(request.payload, &markers);
                let resume_markers = shared_markers_for_continuation_resume(&markers);
                self.close_marker_request(request, resume_markers, activate_add_ids, handler_key)
            }
        }
    }

    pub(super) fn close_shared_resume_marker_frame_result(
        &mut self,
        result: EvalResult,
        markers: SharedMarkers,
        activate_add_ids: bool,
        handler_key: Option<InternedPathPrefix>,
        handler_boundary: Option<HandlerBoundary>,
    ) -> RuntimeResult {
        match result {
            EvalResult::Value(value) => {
                self.stats.marker_frame_value_closes += 1;
                value_result(mark_value_shared(value, &markers))
            }
            EvalResult::Request(request) => {
                self.stats.marker_frame_request_closes += 1;
                let mut request = request;
                if let Some(handler_boundary) = handler_boundary {
                    request.handler_boundary = Some(handler_boundary);
                }
                request.payload = mark_value_shared(request.payload, &markers);
                // Shared resume marker plans are created after
                // `markers_for_continuation_resume`; reusing them avoids
                // re-normalizing the same multi-shot continuation path.
                self.close_marker_request(request, markers, activate_add_ids, handler_key)
            }
        }
    }

    pub(super) fn handler_boundary_for_request(
        &self,
        request: &Request,
        handler_key: Option<InternedPathPrefix>,
        frame_len_before_marker: usize,
    ) -> Option<HandlerBoundary> {
        let handler_key = handler_key?;
        let handler = self.active_handler_frames.iter().rev().find(|frame| {
            frame.frame_index >= frame_len_before_marker && frame.handler_key == handler_key
        })?;
        let blocked =
            self.handler_boundary_blocked(request, handler.frame_index, handler.id, handler_key);
        Some(HandlerBoundary {
            id: handler.id,
            handler_key,
            blocked,
        })
    }

    fn handler_boundary_blocked(
        &self,
        request: &Request,
        handler_frame_index: usize,
        handler_id: GuardId,
        handler_key: InternedPathPrefix,
    ) -> bool {
        self.carried_guard_for_matching_handler(request, handler_frame_index)
            .is_some()
            || self.active_frames.iter().enumerate().any(|(index, frame)| {
                frame.id != handler_id
                    && self.guard_blocks_handler(request, frame.id, handler_id)
                    && (index > handler_frame_index
                        || self.guard_frame_matches_handler(frame.id, handler_key))
            })
    }

    fn guard_frame_matches_handler(
        &self,
        guard_id: GuardId,
        handler_key: InternedPathPrefix,
    ) -> bool {
        self.active_handler_frames
            .iter()
            .any(|frame| frame.id == guard_id && frame.handler_key == handler_key)
    }

    pub(super) fn close_marker_request(
        &mut self,
        request: Request,
        resume_markers: SharedMarkers,
        activate_add_ids: bool,
        handler_key: Option<InternedPathPrefix>,
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

fn request_excepted_at_marker_entry(
    stats: &mut RuntimeStats,
    active_frames: &[ActiveFrame],
    request: &Request,
    marker: &ActiveAddIdMarker,
) -> bool {
    stats.active_add_entry_except_checks += 1;
    if request.guard_ids.is_empty() {
        return false;
    }
    for frame in active_frames.iter().take(marker.entry_frame_len) {
        stats.active_add_entry_frame_scans += 1;
        if request.guard_ids.contains(frame.id) {
            return true;
        }
    }
    false
}

fn request_guard_ids_at_marker_entry(
    stats: &mut RuntimeStats,
    active_frames: &[ActiveFrame],
    request: &Request,
    marker: &ActiveAddIdMarker,
) -> GuardIds {
    stats.active_add_entry_guard_collects += 1;
    let mut ids = GuardIds::new();
    for frame in active_frames.iter().take(marker.entry_frame_len) {
        stats.active_add_entry_frame_scans += 1;
        if request.guard_ids.contains(frame.id) {
            ids.push_unique(frame.id);
        }
    }
    ids
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn outer_marker_colors_request_hidden_by_later_inner_marker() {
        let program = Program::default();
        let mut runtime = Runtime::new(&program);
        let outer = GuardId(1);
        let inner = GuardId(2);

        let outer_markers = marker_frame(&mut runtime, outer, &["outer"]);
        runtime.push_marker_frame(&outer_markers, true, None);
        let inner_markers = marker_frame(&mut runtime, inner, &["inner"]);
        runtime.push_marker_frame(&inner_markers, true, None);

        let mut request = request(&mut runtime, &["foreign", "op"], vec![inner]);
        runtime.mark_request_with_active_markers(&mut request);

        assert!(request.guard_ids.contains(outer));
        assert!(request.guard_ids.contains(inner));
    }

    #[test]
    fn inner_marker_does_not_repaint_request_excepted_at_entry() {
        let program = Program::default();
        let mut runtime = Runtime::new(&program);
        let outer = GuardId(1);
        let inner = GuardId(2);

        let outer_markers = marker_frame(&mut runtime, outer, &["outer"]);
        runtime.push_marker_frame(&outer_markers, true, None);
        let inner_markers = marker_frame(&mut runtime, inner, &["inner"]);
        runtime.push_marker_frame(&inner_markers, true, None);

        let mut request = request(&mut runtime, &["foreign", "op"], vec![outer]);
        runtime.mark_request_with_active_markers(&mut request);

        assert!(request.guard_ids.contains(outer));
        assert!(!request.guard_ids.contains(inner));
    }

    fn marker_frame(runtime: &mut Runtime<'_>, id: GuardId, prefix: &[&str]) -> Vec<ValueMarker> {
        let prefix = path(prefix);
        let path_key = runtime.intern_path(&prefix).prefix();
        vec![
            ValueMarker::Frame { id },
            ValueMarker::AddId(AddIdMarker {
                id,
                path_key,
                depth: 0,
                guard_own_path: false,
                guard_foreign_path: true,
                carry_after_frame: false,
                preserve_own_on_resume: false,
            }),
        ]
    }

    fn request(
        runtime: &mut Runtime<'_>,
        request_path: &[&str],
        guard_ids: Vec<GuardId>,
    ) -> Request {
        let request_path = path(request_path);
        let path_key = runtime.intern_path(&request_path);
        Request {
            path: request_path,
            path_key,
            guard_ids: GuardIds::from(guard_ids),
            carried_guards: Vec::new(),
            handler_boundary: None,
            payload: Value::Unit,
            continuation: Continuation::default(),
        }
    }

    fn path(segments: &[&str]) -> Vec<String> {
        segments
            .iter()
            .map(|segment| (*segment).to_string())
            .collect()
    }
}
