use super::*;

pub(super) struct Runtime<'a> {
    pub(super) program: &'a Program,
    pub(super) instances: HashMap<InstanceId, Value>,
    pub(super) evaluating_instances: HashSet<InstanceId>,
    pub(super) continuations: HashMap<ContinuationId, Continuation<'a>>,
    pub(super) next_continuation_id: u32,
    pub(super) guard_ids: Vec<GuardId>,
    pub(super) active_frames: Vec<ActiveFrame>,
    pub(super) active_add_ids: Vec<AddIdMarker>,
    pub(super) active_marker_plans: Vec<Vec<ValueMarker>>,
    pub(super) next_guard_id: u32,
    pub(super) stats: RuntimeStats,
    pub(super) path_interner: PathInterner,
}

impl<'a> Runtime<'a> {
    pub(super) fn new(program: &'a Program) -> Self {
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
            stats: RuntimeStats::default(),
            path_interner: PathInterner::default(),
        }
    }

    pub(super) fn run(&mut self) -> Result<Vec<Value>, RuntimeError> {
        self.run_with_host(&mut |_, _| None)
    }

    pub(super) fn run_with_host<F>(&mut self, host: &mut F) -> Result<Vec<Value>, RuntimeError>
    where
        F: FnMut(&[String], &Value) -> Option<Value>,
    {
        let mut results = Vec::new();
        let mut env = CapturedEnv::default();
        for root in &self.program.roots {
            match root {
                Root::Instance(instance) => {
                    let result = EvalResult::Value(self.eval_instance(*instance)?);
                    results.push(self.resolve_host_requests(result, host)?);
                }
                Root::EvalInstance(instance) => {
                    let result = EvalResult::Value(self.eval_instance(*instance)?);
                    let _ = self.resolve_host_requests(result, host)?;
                }
                Root::Expr(expr) => {
                    let result = self.eval_expr(*expr, &mut env)?;
                    results.push(self.resolve_host_requests(result, host)?);
                }
            };
        }
        Ok(results)
    }

    pub(super) fn resolve_host_requests<F>(
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
                    self.stats.host_requests += 1;
                    let Some(value) = host(&request.path, &request.payload) else {
                        return Err(RuntimeError::UnhandledEffect { path: request.path });
                    };
                    result = (request.resume)(self, value)?;
                }
            }
        }
    }

    pub(super) fn eval_instance(&mut self, instance: InstanceId) -> Result<Value, RuntimeError> {
        self.stats.instance_eval_calls += 1;
        if let Some(value) = self.instances.get(&instance) {
            self.stats.instance_cache_hits += 1;
            return Ok(value.clone());
        }
        self.stats.instance_cache_misses += 1;
        if !self.evaluating_instances.insert(instance) {
            return Err(RuntimeError::RecursiveInstance { instance });
        }
        let control_instance = self
            .program
            .instances
            .get(instance.0 as usize)
            .ok_or(RuntimeError::MissingInstance { instance })?;
        if control_instance.id != instance {
            self.evaluating_instances.remove(&instance);
            return Err(RuntimeError::MismatchedInstanceSlot {
                requested: instance,
                actual: control_instance.id,
            });
        }

        let mut env = CapturedEnv::default();
        let value = self.eval_expr(control_instance.entry, &mut env);
        self.evaluating_instances.remove(&instance);
        let value = strip_value_markers(expect_eval_value(value?)?);
        self.instances.insert(instance, value.clone());
        Ok(value)
    }

    pub(super) fn intern_path(&mut self, path: &[String]) -> InternedPath {
        self.path_interner.intern(path)
    }
}
