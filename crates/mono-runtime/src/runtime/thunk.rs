use super::*;

impl<'a> Runtime<'a> {
    pub(super) fn adapt_value(
        &mut self,
        value: Value,
        source: &Type,
        target: &Type,
    ) -> RuntimeResult<'a> {
        if equivalent_runtime_types(source, target) || matches!(target, Type::Any) {
            return value_result(value);
        }
        if matches!(source, Type::Never) {
            return value_result(value);
        }
        match (source, target) {
            (
                Type::Thunk {
                    value: source_value,
                    ..
                },
                Type::Thunk {
                    value: target_value,
                    ..
                },
            ) => value_result(Value::Thunk(Thunk::Adapter {
                source: source_value.as_ref().clone(),
                target: target_value.as_ref().clone(),
                thunk: Box::new(value),
            })),
            (Type::Thunk { .. }, target) => {
                let source_value = thunk_value_type(source).unwrap_or(source).clone();
                let target = target.clone();
                let value = self.force_thunk(value)?;
                self.continue_with(value, move |runtime, value| {
                    runtime.adapt_value(value, &source_value, &target)
                })
            }
            (source, Type::Thunk { .. }) => {
                let target_value = thunk_value_type(target).unwrap_or(target).clone();
                let source = source.clone();
                let value = self.adapt_value(value, &source, &target_value)?;
                self.continue_with(value, |_, value| {
                    value_result(Value::Thunk(Thunk::Value(Box::new(value))))
                })
            }
            (Type::Fun { .. }, Type::Fun { .. }) => {
                value_result(Value::FunctionAdapter(FunctionAdapter {
                    source: source.clone(),
                    target: target.clone(),
                    function: Box::new(value),
                    hygiene: FunctionAdapterHygiene {
                        markers: Vec::new(),
                    },
                }))
            }
            _ => Err(RuntimeError::UnsupportedBoundary {
                feature: format!(
                    "coerce {} => {}",
                    mono::dump::dump_type(source),
                    mono::dump::dump_type(target)
                ),
            }),
        }
    }

    pub(super) fn force_thunk(&mut self, thunk: Value) -> RuntimeResult<'a> {
        match thunk {
            Value::Marked { value, markers } => {
                self.with_marker_frame(markers, move |runtime| runtime.force_thunk(*value))
            }
            Value::Thunk(Thunk::Expr { body, mut env }) => self.eval_expr(&body, &mut env),
            Value::Thunk(Thunk::Value(value)) => value_result(*value),
            Value::Thunk(Thunk::Effect { path, payload }) => {
                self.emit_effect_request(path, *payload)
            }
            Value::Thunk(Thunk::Continuation { id, arg }) => {
                let resume = self
                    .continuations
                    .get(&id)
                    .cloned()
                    .ok_or(RuntimeError::MissingContinuation { id })?;
                let result = resume(self, *arg)?;
                self.continue_with(result, |runtime, value| runtime.force_value_if_thunk(value))
            }
            Value::Thunk(Thunk::Adapter {
                source,
                target,
                thunk,
            }) => {
                let value = self.force_thunk(*thunk)?;
                self.continue_with(value, move |runtime, value| {
                    runtime.adapt_value(value, &source, &target)
                })
            }
            value => Err(RuntimeError::NotThunk { value }),
        }
    }

    pub(super) fn continue_with(
        &mut self,
        result: EvalResult<'a>,
        continuation: impl Fn(&mut Runtime<'a>, Value) -> RuntimeResult<'a> + 'a,
    ) -> RuntimeResult<'a> {
        self.continue_with_rc(result, Rc::new(continuation))
    }

    pub(super) fn continue_with_rc(
        &mut self,
        result: EvalResult<'a>,
        continuation: Continuation<'a>,
    ) -> RuntimeResult<'a> {
        match result {
            EvalResult::Value(value) => continuation(self, value),
            EvalResult::Request(request) => {
                let request_resume = request.resume.clone();
                Ok(EvalResult::Request(Request {
                    path: request.path,
                    guard_ids: request.guard_ids,
                    carried_guard_ids: request.carried_guard_ids,
                    payload: request.payload,
                    resume: Rc::new(move |runtime, value| {
                        let resumed = request_resume(runtime, value)?;
                        runtime.continue_with_rc(resumed, continuation.clone())
                    }),
                }))
            }
        }
    }

    pub(super) fn continue_bind(
        &mut self,
        result: BindEvalResult<'a>,
        continuation: impl Fn(&mut Runtime<'a>, bool, CapturedEnv) -> RuntimeResult<'a> + 'a,
    ) -> RuntimeResult<'a> {
        self.continue_bind_rc(result, Rc::new(continuation))
    }

    pub(super) fn continue_bind_rc(
        &mut self,
        result: BindEvalResult<'a>,
        continuation: BindContinuation<'a>,
    ) -> RuntimeResult<'a> {
        match result {
            BindEvalResult::Done { matched, env } => continuation(self, matched, env),
            BindEvalResult::Request(request) => {
                let request_resume = request.resume.clone();
                Ok(EvalResult::Request(Request {
                    path: request.path,
                    guard_ids: request.guard_ids,
                    carried_guard_ids: request.carried_guard_ids,
                    payload: request.payload,
                    resume: Rc::new(move |runtime, value| {
                        let resumed = request_resume(runtime, value)?;
                        runtime.continue_bind_rc(resumed, continuation.clone())
                    }),
                }))
            }
        }
    }

    pub(super) fn continue_bind_result(
        &mut self,
        result: BindEvalResult<'a>,
        continuation: BindStep<'a>,
    ) -> BindResult<'a> {
        match result {
            BindEvalResult::Done { matched, env } => continuation(self, matched, env),
            BindEvalResult::Request(request) => {
                let request_resume = request.resume.clone();
                Ok(BindEvalResult::Request(BindRequest {
                    path: request.path,
                    guard_ids: request.guard_ids,
                    carried_guard_ids: request.carried_guard_ids,
                    payload: request.payload,
                    resume: Rc::new(move |runtime, value| {
                        let resumed = request_resume(runtime, value)?;
                        runtime.continue_bind_result(resumed, continuation.clone())
                    }),
                }))
            }
        }
    }

    pub(super) fn continue_value_as_bind(
        &mut self,
        result: EvalResult<'a>,
        env: CapturedEnv,
        continuation: BindValueStep<'a>,
    ) -> BindResult<'a> {
        match result {
            EvalResult::Value(value) => continuation(self, value, env),
            EvalResult::Request(request) => {
                let request_resume = request.resume.clone();
                Ok(BindEvalResult::Request(BindRequest {
                    path: request.path,
                    guard_ids: request.guard_ids,
                    carried_guard_ids: request.carried_guard_ids,
                    payload: request.payload,
                    resume: Rc::new(move |runtime, value| {
                        let resumed = request_resume(runtime, value)?;
                        runtime.continue_value_as_bind(resumed, env.clone(), continuation.clone())
                    }),
                }))
            }
        }
    }

    pub(super) fn force_value_if_thunk(&mut self, value: Value) -> RuntimeResult<'a> {
        if value_is_thunk_like(&value) {
            return self.force_thunk(value);
        }
        value_result(value)
    }

    pub(super) fn store_continuation(&mut self, continuation: Continuation<'a>) -> ContinuationId {
        let id = ContinuationId(self.next_continuation_id);
        self.next_continuation_id += 1;
        self.continuations.insert(id, continuation);
        id
    }

    pub(super) fn expect_record(&self, value: Value) -> Result<Vec<ValueField>, RuntimeError> {
        let (value, markers) = into_value_markers(value);
        match value {
            Value::Record(fields) => Ok(fields
                .into_iter()
                .map(|field| ValueField {
                    name: field.name,
                    value: mark_value(field.value, &markers),
                })
                .collect()),
            value => Err(RuntimeError::ExpectedRecord { value }),
        }
    }

    pub(super) fn project_record_field(
        &self,
        value: Value,
        name: &str,
    ) -> Result<Value, RuntimeError> {
        let (value, markers) = into_value_markers(value);
        match value {
            Value::Record(fields) => fields
                .iter()
                .rev()
                .find(|field| field.name == name)
                .map(|field| mark_value(field.value.clone(), &markers))
                .ok_or_else(|| RuntimeError::MissingRecordField {
                    name: name.to_string(),
                }),
            Value::DataConstructor { payloads, .. } if payloads.len() == 1 => {
                self.project_record_field(mark_value(payloads[0].clone(), &markers), name)
            }
            value => Err(RuntimeError::ExpectedRecord { value }),
        }
    }
}
