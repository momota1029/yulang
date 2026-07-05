use super::*;

impl<'a> Runtime<'a> {
    pub fn new(program: &'a mono::Program) -> Self {
        Self {
            program,
            instances: HashMap::new(),
            evaluating_instances: HashSet::new(),
            continuations: HashMap::new(),
            next_continuation_id: 0,
            guard_ids: Vec::new(),
            active_frames: Vec::new(),
            active_add_ids: Vec::new(),
            active_marker_plans: Vec::new(),
            next_guard_id: 0,
        }
    }

    pub fn run(&mut self) -> Result<Vec<Value>, RuntimeError> {
        self.run_with_host(&mut |_, _| None)
    }

    pub fn run_with_host<F>(&mut self, host: &mut F) -> Result<Vec<Value>, RuntimeError>
    where
        F: FnMut(&[String], &Value) -> Option<Value>,
    {
        let mut results = Vec::new();
        let mut env = CapturedEnv::default();
        for root in &self.program.roots {
            let result = match root {
                Root::Instance(instance) => EvalResult::Value(self.eval_instance(*instance)?),
                Root::EvalInstance(instance) => EvalResult::Value(self.eval_instance(*instance)?),
                Root::Expr(expr) => self.eval_expr(expr, &mut env)?,
            };
            let value = self.resolve_host_requests(result, host)?;
            if !matches!(root, Root::EvalInstance(_)) {
                results.push(value);
            }
        }
        Ok(results)
    }

    fn resolve_host_requests<F>(
        &mut self,
        mut result: EvalResult<'a>,
        host: &mut F,
    ) -> Result<Value, RuntimeError>
    where
        F: FnMut(&[String], &Value) -> Option<Value>,
    {
        loop {
            match result {
                EvalResult::Value(value) => return Ok(value),
                EvalResult::Request(request) => {
                    let Some(value) = host(&request.path, &request.payload) else {
                        return Err(RuntimeError::UnhandledEffect { path: request.path });
                    };
                    result = (request.resume)(self, value)?;
                }
            }
        }
    }

    pub(super) fn eval_instance(&mut self, instance: InstanceId) -> Result<Value, RuntimeError> {
        if let Some(value) = self.instances.get(&instance) {
            return Ok(value.clone());
        }
        if !self.evaluating_instances.insert(instance) {
            return Err(RuntimeError::RecursiveInstance { instance });
        }
        let mono_instance = self
            .program
            .instances
            .get(instance.0 as usize)
            .ok_or(RuntimeError::MissingInstance { instance })?;
        if mono_instance.id != instance {
            self.evaluating_instances.remove(&instance);
            return Err(RuntimeError::MismatchedInstanceSlot {
                requested: instance,
                actual: mono_instance.id,
            });
        }

        let mut env = CapturedEnv::default();
        let value = self.eval_expr(&mono_instance.body, &mut env);
        self.evaluating_instances.remove(&instance);
        let value = strip_value_markers(expect_eval_value(value?)?);
        self.instances.insert(instance, value.clone());
        Ok(value)
    }
}
