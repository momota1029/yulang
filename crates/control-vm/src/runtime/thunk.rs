use super::*;

impl<'a> Runtime<'a> {
    pub(super) fn adapt_value(
        &mut self,
        value: Value,
        source: &Type,
        target: &Type,
    ) -> RuntimeResult {
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
            ) => value_result(Value::Thunk(Rc::new(Thunk::Adapter {
                source: source_value.as_ref().clone(),
                target: target_value.as_ref().clone(),
                thunk: Box::new(value),
            }))),
            (Type::Thunk { .. }, target) => {
                let source_value = thunk_value_type(source).unwrap_or(source).clone();
                let target = target.clone();
                let value = self.force_thunk(value)?;
                self.continue_with_frame(
                    value,
                    Frame::AdaptValue {
                        source: source_value,
                        target,
                    },
                )
            }
            (source, Type::Thunk { .. }) => {
                let target_value = thunk_value_type(target).unwrap_or(target).clone();
                let source = source.clone();
                let value = self.adapt_value(value, &source, &target_value)?;
                self.continue_with_frame(value, Frame::WrapThunkValue)
            }
            (Type::Fun { .. }, Type::Fun { .. }) => {
                value_result(Value::FunctionAdapter(Rc::new(FunctionAdapter {
                    source: source.clone(),
                    target: target.clone(),
                    function: Box::new(value),
                    hygiene: FunctionAdapterHygiene::default(),
                })))
            }
            (Type::Record(_), Type::Record(_)) if value_boundary_supported(source, target) => {
                value_result(value)
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

    pub(super) fn force_thunk(&mut self, thunk: Value) -> RuntimeResult {
        self.stats.force_thunk_calls += 1;
        match thunk {
            Value::Marked { value, markers } => {
                self.stats.force_marked_calls += 1;
                self.with_shared_marker_frame(markers, move |runtime| runtime.force_thunk(*value))
            }
            Value::Thunk(thunk) => self.force_thunk_handle(thunk),
            value => Err(RuntimeError::NotThunk { value }),
        }
    }

    fn force_thunk_handle(&mut self, thunk: Rc<Thunk>) -> RuntimeResult {
        match Rc::try_unwrap(thunk) {
            Ok(thunk) => self.force_owned_thunk(thunk),
            Err(thunk) => self.force_shared_thunk(&thunk),
        }
    }

    fn force_owned_thunk(&mut self, thunk: Thunk) -> RuntimeResult {
        match thunk {
            Thunk::Expr { body, mut env } => {
                self.stats.force_expr_calls += 1;
                self.eval_expr(body, &mut env)
            }
            Thunk::Value(value) => {
                self.stats.force_value_calls += 1;
                value_result(*value)
            }
            Thunk::Effect { path, payload } => {
                self.stats.force_effect_calls += 1;
                self.emit_effect_request(path, *payload)
            }
            Thunk::Continuation { id, arg } => {
                self.stats.force_continuation_calls += 1;
                let resume = {
                    let continuation = self
                        .continuations
                        .get(&id)
                        .ok_or(RuntimeError::MissingContinuation { id })?
                        .clone();
                    self.clone_continuation_for_invoke(continuation)
                };
                self.stats.continuation_invocations += 1;
                let result = self.resume(resume, *arg)?;
                self.continue_with_frame(result, Frame::ForceValueIfThunk)
            }
            Thunk::Adapter {
                source,
                target,
                thunk,
            } => {
                self.stats.force_adapter_calls += 1;
                let value = self.force_thunk(*thunk)?;
                self.continue_with_frame(value, Frame::AdaptValue { source, target })
            }
        }
    }

    fn force_shared_thunk(&mut self, thunk: &Thunk) -> RuntimeResult {
        match thunk {
            Thunk::Expr { body, env } => {
                self.stats.force_expr_calls += 1;
                let mut env = env.clone();
                self.eval_expr(*body, &mut env)
            }
            Thunk::Value(value) => {
                self.stats.force_value_calls += 1;
                value_result(value.as_ref().clone())
            }
            Thunk::Effect { path, payload } => {
                self.stats.force_effect_calls += 1;
                self.emit_effect_request(path.clone(), payload.as_ref().clone())
            }
            Thunk::Continuation { id, arg } => {
                self.stats.force_continuation_calls += 1;
                let resume = {
                    let continuation = self
                        .continuations
                        .get(id)
                        .ok_or(RuntimeError::MissingContinuation { id: *id })?
                        .clone();
                    self.clone_continuation_for_invoke(continuation)
                };
                self.stats.continuation_invocations += 1;
                let result = self.resume(resume, arg.as_ref().clone())?;
                self.continue_with_frame(result, Frame::ForceValueIfThunk)
            }
            Thunk::Adapter {
                source,
                target,
                thunk,
            } => {
                self.stats.force_adapter_calls += 1;
                let value = self.force_thunk(thunk.as_ref().clone())?;
                self.continue_with_frame(
                    value,
                    Frame::AdaptValue {
                        source: source.clone(),
                        target: target.clone(),
                    },
                )
            }
        }
    }

    pub(super) fn force_value_if_thunk(&mut self, value: Value) -> RuntimeResult {
        if value_is_thunk_like(&value) {
            return self.force_thunk(value);
        }
        value_result(value)
    }

    pub(super) fn store_continuation(&mut self, continuation: Continuation) -> ContinuationId {
        self.stats.continuations_stored += 1;
        let id = ContinuationId(self.next_continuation_id);
        self.next_continuation_id += 1;
        self.continuations.insert(id, continuation);
        id
    }

    pub(super) fn expect_record(&self, value: Value) -> Result<Vec<ValueField>, RuntimeError> {
        let (value, markers) = into_value_markers(value);
        match value {
            Value::Record(fields) => Ok(fields
                .iter()
                .map(|field| ValueField {
                    name: field.name.clone(),
                    value: mark_value(field.value.clone(), &markers),
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
